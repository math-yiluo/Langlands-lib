import Langlands.Cohomology.GaloisCovering
import Langlands.Cohomology.SiteCech.InjectiveCoefficients
import Langlands.Cohomology.SiteCech.FreeSections
import Langlands.Cohomology.SiteCech.LocalCechExactness
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Čech cochains of a Galois covering -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.GaloisCovering

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Cohomology.SiteCech

universe u v w a b

/-- Exactness transfers along additive maps of cochain complexes of modules that commute with
the differentials, are surjective in degree `n + 1` and injective in degree `n + 2`. -/
theorem exactAt_of_comparison {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{a} R) ℕ}
    {L : CochainComplex (ModuleCat.{b} R) ℕ} (e : ∀ k, K.X k →+ L.X k)
    (he : ∀ k (x : K.X k), e (k + 1) (K.d k (k + 1) x) = L.d k (k + 1) (e k x)) (n : ℕ)
    (hs : Function.Surjective (e (n + 1))) (hi : Function.Injective (e (n + 2)))
    (hK : K.ExactAt (n + 1)) : L.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hK ⊢
  intro y hy
  obtain ⟨x, rfl⟩ := hs y
  have hx : K.d (n + 1) (n + 2) x = 0 := by
    apply hi
    rw [map_zero]
    exact (he (n + 1) x).trans hy
  obtain ⟨z, hz⟩ := hK x hx
  exact ⟨e n z, (he n z).symm.trans (congrArg (e (n + 1)) hz)⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Γ : Type w} [Group Γ]
  {V' V : C} (G : GaloisCovering J Γ V' V) [LocallySmall.{w} C]

/-- The presheaf arrow of a Galois covering. -/
abbrev presheafArrow : Arrow (Cᵒᵖ ⥤ Type w) := Arrow.mk (shrinkYoneda.{w}.map G.p)

/-- The Čech term of degree `n` of the presheaf arrow. -/
abbrev cechTerm (n : ℕ) : Cᵒᵖ ⥤ Type w :=
  G.presheafArrow.cechNerve.obj (op (SimplexCategory.mk n))

/-- A tuple of arrows into `V'` with a common composite to `V` as a morphism from a
representable presheaf to the Čech term. -/
def tupleHom {U : C} {n : ℕ} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) : shrinkYoneda.{w}.obj U ⟶ G.cechTerm n :=
  WidePullback.lift (shrinkYoneda.{w}.map (t 0 ≫ G.p)) (fun i => shrinkYoneda.{w}.map (t i))
    (fun i => by
      change shrinkYoneda.{w}.map (t i) ≫ shrinkYoneda.{w}.map G.p = _
      rw [← Functor.map_comp, ht i])

@[reassoc (attr := simp)]
theorem tupleHom_π {U : C} {n : ℕ} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (i : Fin (n + 1)) :
    G.tupleHom t ht ≫ WidePullback.π _ i = shrinkYoneda.{w}.map (t i) :=
  WidePullback.lift_π _ _ _ _ i

theorem tupleHom_ext {U : C} {n : ℕ} (a b : shrinkYoneda.{w}.obj U ⟶ G.cechTerm n)
    (h : ∀ i : Fin (n + 1), a ≫ WidePullback.π _ i = b ≫ WidePullback.π _ i) : a = b := by
  apply WidePullback.hom_ext
  · exact h
  · rw [← WidePullback.π_arrow _ 0, reassoc_of% (h 0)]

/-- Restricting a tuple along an arrow. -/
theorem map_comp_tupleHom {U U' : C} (h : U' ⟶ U) {n : ℕ} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) :
    shrinkYoneda.{w}.map h ≫ G.tupleHom t ht =
      G.tupleHom (fun i => h ≫ t i) (fun i => by rw [Category.assoc, ht i, Category.assoc]) := by
  apply G.tupleHom_ext
  intro i
  rw [Category.assoc, tupleHom_π, tupleHom_π, Functor.map_comp]

/-- Faces of the Čech nerve delete an entry of a tuple. -/
theorem tupleHom_δ {U : C} {n : ℕ} (t : Fin (n + 2) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (j : Fin (n + 2)) :
    G.tupleHom t ht ≫ G.presheafArrow.cechNerve.δ j =
      G.tupleHom (fun i => t (j.succAbove i)) (fun i => by rw [ht, ← ht (j.succAbove 0)]) := by
  apply G.tupleHom_ext
  intro i
  rw [tupleHom_π, Category.assoc]
  change G.tupleHom t ht ≫ (WidePullback.lift _ _ _ ≫ WidePullback.π _ i) = _
  rw [WidePullback.lift_π, tupleHom_π]
  rfl

/-- The presheaf arrow of a Galois covering is locally surjective. -/
instance isLocallySurjective_presheafArrow :
    Presheaf.IsLocallySurjective J G.presheafArrow.hom where
  imageSieve_mem {U} s := by
    obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective s
    apply J.superset_covering _ (J.pullback_stable g G.covering)
    rintro W k ⟨Y, a, b, ⟨⟩, hab⟩
    refine ⟨shrinkYonedaObjObjEquiv.symm a, ?_⟩
    change (shrinkYoneda.{w}.map G.p).app _ (shrinkYonedaObjObjEquiv.symm a) =
      (shrinkYoneda.{w}.obj V).map k.op (shrinkYonedaObjObjEquiv.symm g)
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm,
      shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm]
    exact congrArg _ hab

/-- The tuple of arrows underlying an element of a Čech term. -/
def tupleOf {n : ℕ} {U : C} (x : (G.cechTerm n).obj (op U)) (i : Fin (n + 1)) : U ⟶ V' :=
  (fullyFaithfulShrinkYoneda C).preimage (shrinkYonedaEquiv.symm x ≫ WidePullback.π _ i)

theorem shrinkYoneda_map_tupleOf {n : ℕ} {U : C} (x : (G.cechTerm n).obj (op U))
    (i : Fin (n + 1)) :
    shrinkYoneda.{w}.map (G.tupleOf x i) = shrinkYonedaEquiv.symm x ≫ WidePullback.π _ i :=
  (fullyFaithfulShrinkYoneda C).map_preimage _

theorem tupleOf_comp_p {n : ℕ} {U : C} (x : (G.cechTerm n).obj (op U)) (i : Fin (n + 1)) :
    G.tupleOf x i ≫ G.p = G.tupleOf x 0 ≫ G.p := by
  apply shrinkYoneda.{w}.map_injective
  rw [Functor.map_comp, Functor.map_comp, shrinkYoneda_map_tupleOf, shrinkYoneda_map_tupleOf,
    Category.assoc, Category.assoc]
  have h1 := WidePullback.π_arrow (fun _ : Fin (n + 1) => G.presheafArrow.hom) i
  have h0 := WidePullback.π_arrow (fun _ : Fin (n + 1) => G.presheafArrow.hom) 0
  exact (congrArg (fun f => shrinkYonedaEquiv.symm x ≫ f) h1).trans
    (congrArg (fun f => shrinkYonedaEquiv.symm x ≫ f) h0).symm

theorem tupleHom_tupleOf {n : ℕ} {U : C} (x : (G.cechTerm n).obj (op U)) :
    G.tupleHom (G.tupleOf x) (G.tupleOf_comp_p x) = shrinkYonedaEquiv.symm x := by
  apply G.tupleHom_ext
  intro i
  rw [tupleHom_π, shrinkYoneda_map_tupleOf]

theorem tupleOf_shrinkYonedaEquiv_tupleHom {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) :
    G.tupleOf (shrinkYonedaEquiv (G.tupleHom t ht)) = t := by
  funext i
  apply shrinkYoneda.{w}.map_injective
  rw [shrinkYoneda_map_tupleOf, Equiv.symm_apply_apply, tupleHom_π]

theorem tupleOf_map {n : ℕ} {U U' : C} (h : U' ⟶ U) (x : (G.cechTerm n).obj (op U)) :
    G.tupleOf ((G.cechTerm n).map h.op x) = fun i => h ≫ G.tupleOf x i := by
  funext i
  apply shrinkYoneda.{w}.map_injective
  rw [shrinkYoneda_map_tupleOf, shrinkYonedaEquiv_symm_map, Functor.map_comp,
    shrinkYoneda_map_tupleOf, Category.assoc]
  rfl

/-- The intersection of finitely many sieves. -/
def finInter {U : C} {m : ℕ} (S : Fin m → Sieve U) : Sieve U where
  arrows _ k := ∀ i, S i k
  downward_closed hk l i := (S i).downward_closed (hk i) l

omit [LocallySmall.{w} C] in
theorem finInter_mem {U : C} : ∀ {m : ℕ} (S : Fin m → Sieve U), (∀ i, S i ∈ J U) →
    finInter S ∈ J U
  | 0, _, _ => J.superset_covering (fun _ _ _ i => Fin.elim0 i) (J.top_mem U)
  | m + 1, S, hS => by
    refine J.superset_covering ?_ (J.intersection_covering (hS 0)
      (finInter_mem (fun i => S i.succ) (fun i => hS i.succ)))
    rintro W k ⟨h0, hk⟩ i
    exact Fin.cases h0 (fun i => hk i) i


variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
variable (I : Sheaf J (ModuleCat.{w} R))

/-- The value of a Čech cochain on a tuple, as a linear map in the cochain. -/
def valueHom {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) :
    ((freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) →ₗ[R] I.obj.obj (op U) :=
  (freeRepresentableHomLinearEquiv J R U I).toLinearMap ∘ₗ
    Linear.leftComp R I ((freeSheafFunctor J R).map (G.tupleHom t ht))

theorem valueHom_apply {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (φ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) :
    G.valueHom R I t ht φ =
      freeRepresentableHomEquiv J R U I ((freeSheafFunctor J R).map (G.tupleHom t ht) ≫ φ) :=
  rfl

/-- Values of a cochain are natural in the source of the tuple. -/
theorem valueHom_comp {n : ℕ} {U U' : C} (h : U' ⟶ U) (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (φ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) :
    G.valueHom R I (fun i => h ≫ t i)
        (fun i => by rw [Category.assoc, ht i, Category.assoc]) φ =
      I.obj.map h.op (G.valueHom R I t ht φ) := by
  rw [valueHom_apply, valueHom_apply, ← G.map_comp_tupleHom h t ht, Functor.map_comp,
    Category.assoc, freeRepresentableHomEquiv_naturality_left]

/-- The value of a precomposed cochain on a tuple. -/
theorem valueHom_δ_comp {n : ℕ} {U : C} (t : Fin (n + 2) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (j : Fin (n + 2))
    (φ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) :
    G.valueHom R I t ht ((freeSheafFunctor J R).map (G.presheafArrow.cechNerve.δ j) ≫ φ) =
      G.valueHom R I (fun i => t (j.succAbove i))
        (fun i => by rw [ht, ← ht (j.succAbove 0)]) φ := by
  rw [valueHom_apply, valueHom_apply, ← Category.assoc, ← Functor.map_comp, G.tupleHom_δ]

/-- Values of a cochain through the free-sheaf adjunction. -/
theorem valueHom_eq_homEquiv {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (φ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) :
    G.valueHom R I t ht φ =
      ((freeSheafAdjunction J R).homEquiv _ I φ).app (op U)
        (shrinkYonedaEquiv (G.tupleHom t ht)) := by
  rw [valueHom_apply]
  unfold freeRepresentableHomEquiv
  rw [Equiv.trans_apply, Adjunction.homEquiv_naturality_left]
  exact shrinkYonedaEquiv_comp _ _

/-- A Čech cochain is determined by its values on tuples. -/
theorem cochain_ext {n : ℕ} (φ₁ φ₂ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I)
    (h : ∀ (U : C) (t : Fin (n + 1) → (U ⟶ V')) (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p),
      G.valueHom R I t ht φ₁ = G.valueHom R I t ht φ₂) : φ₁ = φ₂ := by
  apply ((freeSheafAdjunction J R).homEquiv _ I).injective
  ext ⟨U⟩ x
  have hx : x = shrinkYonedaEquiv (G.tupleHom (G.tupleOf x) (G.tupleOf_comp_p x)) := by
    rw [tupleHom_tupleOf, Equiv.apply_symm_apply]
  rw [hx]
  exact (G.valueHom_eq_homEquiv R I _ _ φ₁).symm.trans
    ((h U _ _).trans (G.valueHom_eq_homEquiv R I _ _ φ₂))

/-- The free sheaf Čech chain complex of the covering. -/
abbrev cechChain : ChainComplex (Sheaf J (ModuleCat.{w} R)) ℕ :=
  freeCechChainComplex J R G.presheafArrow

/-- The Čech cochain complex of the covering with coefficients in `I`. -/
abbrev cechCochain : CochainComplex (ModuleCat R) ℕ :=
  (G.cechChain R).linearYonedaObj R I

theorem cechCochain_d_apply (n : ℕ) (φ : (G.cechCochain R I).X n) :
    (G.cechCochain R I).d n (n + 1) φ = (G.cechChain R).d (n + 1) n ≫ φ := by
  simp [ChainComplex.linearYonedaObj_d]

theorem cechChain_d (n : ℕ) :
    (G.cechChain R).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (freeSheafFunctor J R).map (G.presheafArrow.cechNerve.δ i) := by
  simp only [freeCechChainComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD]
  rfl

/-- Values of the Čech differential are alternating sums over deleted entries. -/
theorem valueHom_cech_d {n : ℕ} {U : C} (t : Fin (n + 2) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (φ : (G.cechCochain R I).X n) :
    G.valueHom R I t ht ((G.cechCochain R I).d n (n + 1) φ) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        G.valueHom R I (fun i => t (j.succAbove i))
          (fun i => by rw [ht, ← ht (j.succAbove 0)]) φ := by
  rw [cechCochain_d_apply, cechChain_d, Preadditive.sum_comp, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.zsmul_comp, map_zsmul, G.valueHom_δ_comp R I t ht j φ]

/-- The Čech cochain complex of an injective sheaf is exact in positive degrees. -/
theorem cechCochain_exactAt_of_injective [Injective I] (n : ℕ)
    [Presheaf.IsLocallySurjective J G.presheafArrow.hom] :
    (G.cechCochain R I).ExactAt (n + 1) := by
  have := quasiIso_freeCechAugmentation_of_locally_surjective J R G.presheafArrow
  have hP : (G.cechChain R).ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt (freeCechAugmentation J R G.presheafArrow) (n + 1)).2
      (ChainComplex.exactAt_succ_single_obj _ n)
  exact exactAt_linearYonedaObj_of_injective R _ I n hP

/-- The homogeneous tuple of deck transformations attached to a group tuple. -/
def hpat {n : ℕ} (g : Fin n → Γ) (k : Fin (n + 1)) : V' ⟶ V' :=
  G.deck (Fin.partialProd g k)⁻¹

omit [LocallySmall.{w} C] in
theorem hpat_comp_p {n : ℕ} (g : Fin n → Γ) (k : Fin (n + 1)) :
    G.hpat g k ≫ G.p = G.hpat g 0 ≫ G.p := by
  simp only [hpat, G.deck_comp]

/-- The sieve on which a tuple is a translate of a homogeneous deck tuple. -/
def patternSieve {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V')) : Sieve U where
  arrows _ k := ∃ g : Fin n → Γ, ∀ i, k ≫ t i = (k ≫ t 0) ≫ G.hpat g i
  downward_closed := by
    rintro W W' k ⟨g, hg⟩ l
    refine ⟨g, fun i => ?_⟩
    simp only [Category.assoc] at hg ⊢
    rw [hg i]

omit [LocallySmall.{w} C] in
theorem hpat_zero {n : ℕ} (g : Fin n → Γ) : G.hpat g 0 = 𝟙 V' := by
  simp only [hpat, Fin.partialProd_zero, inv_one, G.deck_one]

omit [LocallySmall.{w} C] in
/-- Every tuple is locally a translate of a homogeneous deck tuple. -/
theorem patternSieve_mem {n : ℕ} {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) : G.patternSieve t ∈ J U := by
  refine J.superset_covering ?_
    (finInter_mem (fun i => GaloisCovering.transitivitySieve G.deck (t 0) (t i))
      (fun i => G.locally_transitive _ _ (ht i).symm))
  intro W k hk
  choose γ hγ using hk
  let δ : Fin (n + 1) → Γ := fun i => if i = 0 then 1 else (γ i)⁻¹
  have hδ : Fin.partialProd (fun j : Fin n => (δ j.castSucc)⁻¹ * δ j.succ) = δ := by
    have h := Fin.partialProd_left_inv δ
    simpa [δ] using h
  refine ⟨fun j => (δ j.castSucc)⁻¹ * δ j.succ, fun i => ?_⟩
  simp only [hpat]
  rw [hδ]
  by_cases hi : i = 0
  · subst hi
    simp [δ, G.deck_one]
  · simp only [δ, hi, ite_false, inv_inv]
    rw [hγ i, Category.assoc]

theorem valueHom_congr {n : ℕ} {U : C} {t t' : Fin (n + 1) → (U ⟶ V')} (h : t = t')
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) (ht' : ∀ i, t' i ≫ G.p = t' 0 ≫ G.p)
    (φ : (freeSheafFunctor J R).obj (G.cechTerm n) ⟶ I) :
    G.valueHom R I t ht φ = G.valueHom R I t' ht' φ := by
  subst h
  rfl

/-- Comparison of Čech cochains with inhomogeneous group cochains: evaluate on the
homogeneous deck tuples. -/
def compare (n : ℕ) : (G.cechCochain R I).X n →ₗ[R] ((Fin n → Γ) → I.obj.obj (op V')) :=
  LinearMap.pi fun g => G.valueHom R I (G.hpat g) (G.hpat_comp_p g)

theorem compare_apply (n : ℕ) (φ : (G.cechCochain R I).X n) (g : Fin n → Γ) :
    G.compare R I n φ g = G.valueHom R I (G.hpat g) (G.hpat_comp_p g) φ := rfl

/-- The comparison commutes with the differentials. -/
theorem compare_d (n : ℕ) (φ : (G.cechCochain R I).X n) :
    G.compare R I (n + 1) ((G.cechCochain R I).d n (n + 1) φ) =
      (groupCohomology.inhomogeneousCochains (G.rep I)).d n (n + 1) (G.compare R I n φ) := by
  funext g
  rw [groupCohomology.inhomogeneousCochains.d_def]
  rw [compare_apply, valueHom_cech_d, Fin.sum_univ_succ, inhomogeneousCochains.d_hom_apply]
  congr 1
  · have h0 : (fun i => G.hpat g ((0 : Fin (n + 2)).succAbove i)) =
        fun i => G.deck (g 0)⁻¹ ≫ G.hpat (fun i => g i.succ) i := by
      funext i
      simp only [hpat, Fin.succAbove_zero, Fin.partialProd_succ', mul_inv_rev, G.deck_mul]
      rfl
    rw [Fin.val_zero, pow_zero, one_smul, G.valueHom_congr R I h0 _
      (fun i => by rw [Category.assoc, G.hpat_comp_p, ← Category.assoc]),
      G.valueHom_comp R I (G.deck (g 0)⁻¹) (G.hpat fun i => g i.succ) (G.hpat_comp_p _) φ]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (fun i => G.hpat g (j.succ.succAbove i)) =
        G.hpat (Fin.contractNth j (· * ·) g) := by
      funext i
      simp only [hpat]
      rw [Fin.partialProd_contractNth]
      rfl
    rw [G.valueHom_congr R I hj _ (G.hpat_comp_p _), Fin.val_succ, ← Int.cast_smul_eq_zsmul R,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    rfl

/-- The comparison with inhomogeneous cochains is injective. -/
theorem compare_injective (n : ℕ) : Function.Injective (G.compare R I n) := by
  intro φ₁ φ₂ h
  apply G.cochain_ext R I φ₁ φ₂
  intro U t ht
  apply eq_of_sieve _ (G.patternSieve_mem t ht)
  rintro W k ⟨g, hg⟩
  have hk : (fun i => k ≫ t i) = fun i => (k ≫ t 0) ≫ G.hpat g i := funext hg
  rw [← G.valueHom_comp R I k t ht φ₁, ← G.valueHom_comp R I k t ht φ₂,
    G.valueHom_congr R I hk _ (fun i => by rw [Category.assoc, G.hpat_comp_p, ← Category.assoc]),
    G.valueHom_congr R I hk _ (fun i => by rw [Category.assoc, G.hpat_comp_p, ← Category.assoc]),
    G.valueHom_comp R I (k ≫ t 0) (G.hpat g) (G.hpat_comp_p g) φ₁,
    G.valueHom_comp R I (k ≫ t 0) (G.hpat g) (G.hpat_comp_p g) φ₂,
    ← compare_apply, ← compare_apply, h]

/-- Positive group cohomology of the sections of an injective sheaf over `V'` vanishes,
provided the comparison maps are surjective and injective in the relevant degrees. -/
theorem isZero_groupCohomology_of_compare [Injective I]
    [Presheaf.IsLocallySurjective J G.presheafArrow.hom] (n : ℕ)
    (hs : Function.Surjective (G.compare R I (n + 1)))
    (hi : Function.Injective (G.compare R I (n + 2))) :
    IsZero (groupCohomology (G.rep I) (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (exactAt_of_comparison (K := G.cechCochain R I)
      (L := groupCohomology.inhomogeneousCochains (G.rep I))
      (fun k => (G.compare R I k).toAddMonoidHom) (fun k x => G.compare_d R I k x) n hs hi
      (G.cechCochain_exactAt_of_injective R I n))

omit [LocallySmall.{w} C] in
/-- Partial products determine a tuple of group elements. -/
theorem eq_of_partialProd_eq {n : ℕ} {g g' : Fin n → Γ}
    (h : ∀ i, Fin.partialProd g i = Fin.partialProd g' i) : g = g' := by
  funext j
  rw [← Fin.partialProd_right_inv g j, ← Fin.partialProd_right_inv g' j, h, h]

omit [LocallySmall.{w} C] in
theorem pattern_comp {n : ℕ} {U W W' : C} {t : Fin (n + 1) → (U ⟶ V')} {k : W ⟶ U}
    {g : Fin n → Γ} (hk : ∀ i, k ≫ t i = (k ≫ t 0) ≫ G.hpat g i) (l : W' ⟶ W) :
    ∀ i, (l ≫ k) ≫ t i = ((l ≫ k) ≫ t 0) ≫ G.hpat g i := by
  intro i
  simp only [Category.assoc] at hk ⊢
  rw [hk i]

omit [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)] in
/-- Local uniqueness of patterns: two homogeneous deck tuples through the same arrow give
the same restrictions of any cochain values. -/
theorem map_eq_of_hpat_eq {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) {W : C}
    (f : W ⟶ V') {g g' : Fin n → Γ} (h : ∀ i, f ≫ G.hpat g i = f ≫ G.hpat g' i) :
    I.obj.map f.op (c g) = I.obj.map f.op (c g') := by
  by_cases hW : (⊥ : Sieve W) ∈ J W
  · exact eq_of_sieve ⊥ hW _ _ (fun _ _ hk => absurd hk (by simp))
  · have hpp : ∀ i, Fin.partialProd g i = Fin.partialProd g' i := by
      intro i
      have hi := h i
      simp only [hpat] at hi
      have hfix : f ≫ G.deck (Fin.partialProd g' i * (Fin.partialProd g i)⁻¹) = f := by
        rw [G.deck_mul, ← Category.assoc, hi, Category.assoc, ← G.deck_mul, mul_inv_cancel,
          G.deck_one, Category.comp_id]
      rcases G.locally_free f _ hfix with h1 | h1
      · exact (mul_inv_eq_one.1 h1).symm
      · exact absurd h1 hW
    rw [eq_of_partialProd_eq hpp]

/-- Gluing the local values of an inhomogeneous cochain along the pattern sieve of a
tuple. -/
def glue {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) {U : C} (t : Fin (n + 1) → (U ⟶ V'))
    (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) : I.obj.obj (op U) :=
  I.property.amalgamate ⟨G.patternSieve t, G.patternSieve_mem t ht⟩
    (fun A => sectionHom (I.obj.map (A.f ≫ t 0).op (c A.hf.choose)))
    (by
      intro A₁ A₂ r
      rw [sectionHom_comp, sectionHom_comp, map_map_apply, map_map_apply]
      have e1 := G.pattern_comp A₁.hf.choose_spec r.g₁
      have e2 := G.pattern_comp A₂.hf.choose_spec r.g₂
      rw [r.w] at e1
      rw [← Category.assoc, ← Category.assoc, r.w]
      exact congrArg _ (G.map_eq_of_hpat_eq R I c _ (fun i => (e1 i).symm.trans (e2 i)))) (1 : R)

omit [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)] in
theorem glue_spec {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) {U : C}
    (t : Fin (n + 1) → (U ⟶ V')) (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p) {W : C} (k : W ⟶ U)
    (g : Fin n → Γ) (hk : ∀ i, k ≫ t i = (k ≫ t 0) ≫ G.hpat g i) :
    I.obj.map k.op (G.glue R I c t ht) = I.obj.map (k ≫ t 0).op (c g) := by
  have h := congrArg (fun e => e (1 : R)) (I.property.amalgamate_map
    ⟨G.patternSieve t, G.patternSieve_mem t ht⟩
    (fun A => sectionHom (I.obj.map (A.f ≫ t 0).op (c A.hf.choose))) (by
      intro A₁ A₂ r
      rw [sectionHom_comp, sectionHom_comp, map_map_apply, map_map_apply]
      have e1 := G.pattern_comp A₁.hf.choose_spec r.g₁
      have e2 := G.pattern_comp A₂.hf.choose_spec r.g₂
      rw [r.w] at e1
      rw [← Category.assoc, ← Category.assoc, r.w]
      exact congrArg _ (G.map_eq_of_hpat_eq R I c _ (fun i => (e1 i).symm.trans (e2 i))))
    ⟨W, k, ⟨g, hk⟩⟩)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans ((sectionHom_apply_one _).trans (G.map_eq_of_hpat_eq R I c _ (fun i => ?_)))
  exact ((Exists.choose_spec (⟨g, hk⟩ : ∃ g, ∀ i, k ≫ t i = (k ≫ t 0) ≫ G.hpat g i)) i).symm.trans
    (hk i)

omit [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)] in
theorem glue_congr {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) {U : C}
    {t t' : Fin (n + 1) → (U ⟶ V')} (h : t = t') (ht : ∀ i, t i ≫ G.p = t 0 ≫ G.p)
    (ht' : ∀ i, t' i ≫ G.p = t' 0 ≫ G.p) : G.glue R I c t ht = G.glue R I c t' ht' := by
  subst h
  rfl

/-- The glued values form a natural transformation from the Čech term. -/
def glueHom {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) :
    G.cechTerm n ⟶ (sheafToPresheaf J (ModuleCat.{w} R) ⋙
      (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{w} R))).obj I where
  app X := ↾fun x => G.glue R I c (U := X.unop) (G.tupleOf (U := X.unop) x)
    (G.tupleOf_comp_p (U := X.unop) x)
  naturality U U' h := by
    ext x
    change G.glue R I c (G.tupleOf ((G.cechTerm n).map h x)) (G.tupleOf_comp_p _) =
      I.obj.map h (G.glue R I c (G.tupleOf x) (G.tupleOf_comp_p x))
    refine (G.glue_congr R I c (G.tupleOf_map h.unop x) _
      (fun i => by rw [Category.assoc, G.tupleOf_comp_p, Category.assoc])).trans ?_
    apply eq_of_sieve (G.patternSieve (fun i => h.unop ≫ G.tupleOf x i)) (G.patternSieve_mem _
      (fun i => by rw [Category.assoc, G.tupleOf_comp_p, Category.assoc]))
    rintro W k ⟨g, hg⟩
    rw [G.glue_spec R I c _ _ k g hg]
    change _ = I.obj.map k.op (I.obj.map h.unop.op _)
    rw [map_map_apply, G.glue_spec R I c _ _ (k ≫ h.unop) g (fun i => by
      simp only [Category.assoc] at hg ⊢
      exact hg i)]
    simp only [Category.assoc]

omit [HasSheafify J (ModuleCat.{w} R)] in
theorem glueHom_app {n : ℕ} (c : (Fin n → Γ) → I.obj.obj (op V')) {U : C}
    (x : (G.cechTerm n).obj (op U)) :
    (G.glueHom R I c).app (op U) x = G.glue R I c (G.tupleOf x) (G.tupleOf_comp_p x) :=
  rfl

/-- The comparison with inhomogeneous cochains is surjective. -/
theorem compare_surjective (n : ℕ) : Function.Surjective (G.compare R I n) := by
  intro c
  refine ⟨((freeSheafAdjunction J R).homEquiv (G.cechTerm n) I).symm (G.glueHom R I c), ?_⟩
  funext g
  rw [compare_apply, valueHom_eq_homEquiv, Equiv.apply_symm_apply, glueHom_app,
    G.glue_congr R I c (G.tupleOf_shrinkYonedaEquiv_tupleHom _ (G.hpat_comp_p g)) _
    (G.hpat_comp_p g)]
  have h := G.glue_spec R I c (G.hpat g) (G.hpat_comp_p g) (𝟙 V') g
    (fun i => by simp only [G.hpat_zero, Category.id_comp])
  rwa [op_id, I.obj.map_id, G.hpat_zero, Category.id_comp, op_id, I.obj.map_id] at h

/-- **Injective sheaves are Galois acyclic.** The positive-degree group cohomology of the
sections over `V'` of an injective sheaf vanishes. -/
theorem isZero_groupCohomology_rep_of_injective [Injective I] (n : ℕ) :
    IsZero (groupCohomology (G.rep I) (n + 1)) :=
  G.isZero_groupCohomology_of_compare R I n (G.compare_surjective R I _)
    (G.compare_injective R I _)

end Langlands.Cohomology.GaloisCovering
