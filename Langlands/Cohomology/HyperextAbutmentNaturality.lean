import Langlands.Cohomology.HyperextAbutmentFiltration

/-!
# Naturality of the hyperext abutment filtration

Let `t` be a t-structure on a pretriangulated category `C`. The abutment filtration
`F^p = filtration t K B n p` on `Hom(K, B⟦n⟧)` of `Langlands.Cohomology.HyperextAbutmentFiltration`
consists of the morphisms factoring through `K ⟶ τ_{≥ p - n} K`. This module shows that it is
natural in `K` and in `B`.

* Precomposition with `φ : K' ⟶ K` (`precomp`) maps `F^p` on `Hom(K, B⟦n⟧)` into `F^p` on
  `Hom(K', B⟦n⟧)` (`precomp_mem_filtration`), and postcomposition with `ψ⟦n⟧'` for
  `ψ : B ⟶ B'` (`postcomp`) maps `F^p` on `Hom(K, B⟦n⟧)` into `F^p` on `Hom(K, B'⟦n⟧)`
  (`postcomp_mem_filtration`).
* Hence they induce additive maps on the steps (`filtrationPrecomp`, `filtrationPostcomp`) and on
  the graded pieces `gr^p = F^p / F^{p+1}` (`gradedPrecomp`, `gradedPostcomp`). These maps send
  identities to identities and composites to composites (contravariantly in `K`, covariantly in
  `B`), and the maps in `K` commute with those in `B`.

For the canonical t-structure on the derived category and `B = W₀`, the object `W` placed in
degree `0`, the edge map `HyperextDegeneration.edgeMap K W n` is natural in `W`
(`edgeMap_postcomp`), complementing its naturality in `K` (`edgeMap_comp` of
`HyperextAbutmentFiltration`); `edgeMapAddMonoidHom_comp_postcomp` and
`edgeMapAddMonoidHom_comp_precomp` state both as equalities of additive maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w v u

section Composition

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

/-- Precomposition with `φ : K' ⟶ K`, as an additive map
`Hom(K, B⟦n⟧) →+ Hom(K', B⟦n⟧)`. -/
def precomp {K' K : C} (φ : K' ⟶ K) (B : C) (n : ℤ) : ShiftedHom K B n →+ ShiftedHom K' B n :=
  Preadditive.leftComp (B⟦n⟧) φ

@[simp]
lemma precomp_apply {K' K : C} (φ : K' ⟶ K) (B : C) (n : ℤ) (f : ShiftedHom K B n) :
    precomp φ B n f = φ ≫ f :=
  rfl

/-- Postcomposition with `ψ⟦n⟧'` for `ψ : B ⟶ B'`, as an additive map
`Hom(K, B⟦n⟧) →+ Hom(K, B'⟦n⟧)`. -/
def postcomp (K : C) {B B' : C} (ψ : B ⟶ B') (n : ℤ) : ShiftedHom K B n →+ ShiftedHom K B' n :=
  Preadditive.rightComp K (ψ⟦n⟧')

@[simp]
lemma postcomp_apply (K : C) {B B' : C} (ψ : B ⟶ B') (n : ℤ) (f : ShiftedHom K B n) :
    postcomp K ψ n f = f ≫ ψ⟦n⟧' :=
  rfl

end Composition

section TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {t : TStructure C}

/-- Precomposition maps `F^p` into `F^p`: if `f` vanishes on `τ_{< p - n} K`, then `φ ≫ f`
vanishes on `τ_{< p - n} K'`, by naturality of `τ_{< p - n} ⟶ 𝟭`. -/
lemma precomp_mem_filtration {K' K B : C} (φ : K' ⟶ K) {n p : ℤ} {f : ShiftedHom K B n}
    (hf : f ∈ filtration t K B n p) : precomp φ B n f ∈ filtration t K' B n p := by
  rw [mem_filtration_iff_truncLTι_comp_eq_zero] at hf ⊢
  have h : (t.truncLTι (p - n)).app K' ≫ φ =
      (t.truncLT (p - n)).map φ ≫ (t.truncLTι (p - n)).app K :=
    ((t.truncLTι (p - n)).naturality φ).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h).trans
    ((Category.assoc _ _ _).trans ((congrArg _ hf).trans comp_zero)))

/-- Postcomposition maps `F^p` into `F^p`: a factorization `f = π ≫ g` through
`K ⟶ τ_{≥ p - n} K` gives `f ≫ ψ⟦n⟧' = π ≫ (g ≫ ψ⟦n⟧')`. -/
lemma postcomp_mem_filtration {K B B' : C} (ψ : B ⟶ B') {n p : ℤ} {f : ShiftedHom K B n}
    (hf : f ∈ filtration t K B n p) : postcomp K ψ n f ∈ filtration t K B' n p := by
  obtain ⟨g, rfl⟩ := (mem_filtration_iff f).1 hf
  exact (mem_filtration_iff _).2 ⟨g ≫ ψ⟦n⟧', (Category.assoc _ _ _).symm⟩

variable (t)

/-- The additive map `F^p(K, B) →+ F^p(K', B)` induced by precomposition with `φ : K' ⟶ K`. -/
def filtrationPrecomp {K' K : C} (φ : K' ⟶ K) (B : C) (n p : ℤ) :
    filtration t K B n p →+ filtration t K' B n p :=
  ((precomp φ B n).comp (filtration t K B n p).subtype).codRestrict (filtration t K' B n p)
    fun f => precomp_mem_filtration φ f.2

/-- The additive map `F^p(K, B) →+ F^p(K, B')` induced by postcomposition with `ψ⟦n⟧'`. -/
def filtrationPostcomp (K : C) {B B' : C} (ψ : B ⟶ B') (n p : ℤ) :
    filtration t K B n p →+ filtration t K B' n p :=
  ((postcomp K ψ n).comp (filtration t K B n p).subtype).codRestrict (filtration t K B' n p)
    fun f => postcomp_mem_filtration ψ f.2

@[simp]
lemma coe_filtrationPrecomp {K' K : C} (φ : K' ⟶ K) (B : C) (n p : ℤ)
    (f : filtration t K B n p) :
    (filtrationPrecomp t φ B n p f : ShiftedHom K' B n) = φ ≫ (f : ShiftedHom K B n) :=
  rfl

@[simp]
lemma coe_filtrationPostcomp (K : C) {B B' : C} (ψ : B ⟶ B') (n p : ℤ)
    (f : filtration t K B n p) :
    (filtrationPostcomp t K ψ n p f : ShiftedHom K B' n) = (f : ShiftedHom K B n) ≫ ψ⟦n⟧' :=
  rfl

/-- The additive map `gr^p(K, B) →+ gr^p(K', B)` induced by precomposition with `φ : K' ⟶ K`. -/
def gradedPrecomp {K' K : C} (φ : K' ⟶ K) (B : C) (n p : ℤ) :
    graded t K B n p →+ graded t K' B n p :=
  QuotientAddGroup.map _ _ (filtrationPrecomp t φ B n p) fun f hf => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact precomp_mem_filtration (p := p + 1) φ hf

/-- The additive map `gr^p(K, B) →+ gr^p(K, B')` induced by postcomposition with `ψ⟦n⟧'`. -/
def gradedPostcomp (K : C) {B B' : C} (ψ : B ⟶ B') (n p : ℤ) :
    graded t K B n p →+ graded t K B' n p :=
  QuotientAddGroup.map _ _ (filtrationPostcomp t K ψ n p) fun f hf => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact postcomp_mem_filtration (p := p + 1) ψ hf

@[simp]
lemma gradedPrecomp_mk {K' K : C} (φ : K' ⟶ K) (B : C) (n p : ℤ) (f : filtration t K B n p) :
    gradedPrecomp t φ B n p (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (filtrationPrecomp t φ B n p f) :=
  rfl

@[simp]
lemma gradedPostcomp_mk (K : C) {B B' : C} (ψ : B ⟶ B') (n p : ℤ) (f : filtration t K B n p) :
    gradedPostcomp t K ψ n p (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (filtrationPostcomp t K ψ n p f) :=
  rfl

lemma filtrationPrecomp_id (K B : C) (n p : ℤ) :
    filtrationPrecomp t (𝟙 K) B n p = AddMonoidHom.id _ := by
  ext f
  change 𝟙 K ≫ (f : ShiftedHom K B n) = f
  exact Category.id_comp _

lemma filtrationPrecomp_comp {K'' K' K : C} (φ' : K'' ⟶ K') (φ : K' ⟶ K) (B : C) (n p : ℤ) :
    filtrationPrecomp t (φ' ≫ φ) B n p =
      (filtrationPrecomp t φ' B n p).comp (filtrationPrecomp t φ B n p) := by
  ext f
  change (φ' ≫ φ) ≫ (f : ShiftedHom K B n) = φ' ≫ φ ≫ (f : ShiftedHom K B n)
  exact Category.assoc _ _ _

lemma filtrationPostcomp_id (K B : C) (n p : ℤ) :
    filtrationPostcomp t K (𝟙 B) n p = AddMonoidHom.id _ := by
  ext f
  change (f : ShiftedHom K B n) ≫ (𝟙 B)⟦n⟧' = f
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

lemma filtrationPostcomp_comp (K : C) {B B' B'' : C} (ψ : B ⟶ B') (ψ' : B' ⟶ B'') (n p : ℤ) :
    filtrationPostcomp t K (ψ ≫ ψ') n p =
      (filtrationPostcomp t K ψ' n p).comp (filtrationPostcomp t K ψ n p) := by
  ext f
  change (f : ShiftedHom K B n) ≫ (ψ ≫ ψ')⟦n⟧' = ((f : ShiftedHom K B n) ≫ ψ⟦n⟧') ≫ ψ'⟦n⟧'
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Precomposition and postcomposition commute on the steps of the filtration. -/
lemma filtrationPrecomp_comp_filtrationPostcomp {K' K B B' : C} (φ : K' ⟶ K) (ψ : B ⟶ B')
    (n p : ℤ) :
    (filtrationPrecomp t φ B' n p).comp (filtrationPostcomp t K ψ n p) =
      (filtrationPostcomp t K' ψ n p).comp (filtrationPrecomp t φ B n p) := by
  ext f
  change φ ≫ (f : ShiftedHom K B n) ≫ ψ⟦n⟧' = (φ ≫ (f : ShiftedHom K B n)) ≫ ψ⟦n⟧'
  exact (Category.assoc _ _ _).symm

lemma gradedPrecomp_id (K B : C) (n p : ℤ) :
    gradedPrecomp t (𝟙 K) B n p = AddMonoidHom.id _ := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext f
  change QuotientAddGroup.mk (filtrationPrecomp t (𝟙 K) B n p f) = QuotientAddGroup.mk f
  rw [filtrationPrecomp_id]
  rfl

lemma gradedPrecomp_comp {K'' K' K : C} (φ' : K'' ⟶ K') (φ : K' ⟶ K) (B : C) (n p : ℤ) :
    gradedPrecomp t (φ' ≫ φ) B n p =
      (gradedPrecomp t φ' B n p).comp (gradedPrecomp t φ B n p) := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext f
  change QuotientAddGroup.mk (filtrationPrecomp t (φ' ≫ φ) B n p f) =
    QuotientAddGroup.mk (filtrationPrecomp t φ' B n p (filtrationPrecomp t φ B n p f))
  rw [filtrationPrecomp_comp]
  rfl

lemma gradedPostcomp_id (K B : C) (n p : ℤ) :
    gradedPostcomp t K (𝟙 B) n p = AddMonoidHom.id _ := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext f
  change QuotientAddGroup.mk (filtrationPostcomp t K (𝟙 B) n p f) = QuotientAddGroup.mk f
  rw [filtrationPostcomp_id]
  rfl

lemma gradedPostcomp_comp (K : C) {B B' B'' : C} (ψ : B ⟶ B') (ψ' : B' ⟶ B'') (n p : ℤ) :
    gradedPostcomp t K (ψ ≫ ψ') n p =
      (gradedPostcomp t K ψ' n p).comp (gradedPostcomp t K ψ n p) := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext f
  change QuotientAddGroup.mk (filtrationPostcomp t K (ψ ≫ ψ') n p f) =
    QuotientAddGroup.mk (filtrationPostcomp t K ψ' n p (filtrationPostcomp t K ψ n p f))
  rw [filtrationPostcomp_comp]
  rfl

/-- Precomposition and postcomposition commute on the graded pieces. -/
lemma gradedPrecomp_comp_gradedPostcomp {K' K B B' : C} (φ : K' ⟶ K) (ψ : B ⟶ B') (n p : ℤ) :
    (gradedPrecomp t φ B' n p).comp (gradedPostcomp t K ψ n p) =
      (gradedPostcomp t K' ψ n p).comp (gradedPrecomp t φ B n p) := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext f
  change QuotientAddGroup.mk (filtrationPrecomp t φ B' n p (filtrationPostcomp t K ψ n p f)) =
    QuotientAddGroup.mk (filtrationPostcomp t K' ψ n p (filtrationPrecomp t φ B n p f))
  rw [← AddMonoidHom.comp_apply, filtrationPrecomp_comp_filtrationPostcomp]
  rfl

end TStructure

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- The edge map is natural in `W`: postcomposing with `ψ : W ⟶ W'` placed in degree `0` and
shifted by `n` corresponds to postcomposing the induced map on `H^{-n}` with `ψ`. -/
lemma edgeMap_postcomp (K : DerivedCategory C) {W W' : C} (ψ : W ⟶ W') (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap K W' n (postcomp K ((singleFunctor C 0).map ψ) n f) =
      HyperextDegeneration.edgeMap K W n f ≫ ψ := by
  have h := (singleFunctorCompHomologyFunctorIso C 0).hom.naturality ψ
  simp only [HyperextDegeneration.edgeMap, postcomp_apply, Functor.shiftMap_comp]
  exact (Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm)

/-- Naturality of the edge map in `W`, as an equality of additive maps. -/
lemma edgeMapAddMonoidHom_comp_postcomp (K : DerivedCategory C) {W W' : C} (ψ : W ⟶ W')
    (n : ℤ) :
    (edgeMapAddMonoidHom K W' n).comp (postcomp K ((singleFunctor C 0).map ψ) n) =
      (Preadditive.rightComp _ ψ).comp (edgeMapAddMonoidHom K W n) := by
  ext f
  exact edgeMap_postcomp K ψ n f

/-- Naturality of the edge map in `K`, as an equality of additive maps. -/
lemma edgeMapAddMonoidHom_comp_precomp {X K : DerivedCategory C} (φ : X ⟶ K) (W : C) (n : ℤ) :
    (edgeMapAddMonoidHom X W n).comp (precomp φ ((singleFunctor C 0).obj W) n) =
      (Preadditive.leftComp _ ((homologyFunctor C (-n)).map φ)).comp
        (edgeMapAddMonoidHom K W n) := by
  ext f
  exact edgeMap_comp φ W n f

end Derived

end HyperextAbutment

end Langlands.Cohomology
