/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Čech complexes of coverings on a site

Source: Stacks Project, Cohomology on Sites, Tags 03AK, 03AM, 03AO, 03AQ
(blueprint: def-weil-pbc-site-cech-complex).

`SiteCechComplex` records the chosen fibre products, including their universal properties.
Its `complexFunctor` constructs the alternating restriction complex; `cohomologyFunctor`
is its cohomology. Only verification proofs are postponed, never the differential or maps.
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Chosen iterated fibre products and index maps for a family over `U`.
The universal properties characterize the choices; the degree-zero choice is the original
object. Source: Stacks 03AK, 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
structure SiteCechComplex {C : Type u} [Category.{v} C] {T : Type w} {U : C}
    (f : T → C) (hom : ∀ t, f t ⟶ U) where
  W : ∀ p : ℕ, (Fin (p + 1) → T) → C
  pr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)), W p t ⟶ f (t k)
  comm : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
    pr p t k ≫ hom (t k) = pr p t 0 ≫ hom (t 0)
  universal : ∀ (p : ℕ) (t : Fin (p + 1) → T) (Z : C)
    (a : ∀ k, Z ⟶ f (t k)),
    (∀ k, a k ≫ hom (t k) = a 0 ≫ hom (t 0)) →
    ∃! b : Z ⟶ W p t, ∀ k, b ≫ pr p t k = a k
  W_zero : ∀ t, W 0 t = f (t 0)
  pr_zero : ∀ t, pr 0 t 0 = eqToHom (W_zero t)
  indexMap : ∀ {p q : ℕ} (t : Fin (p + 1) → T) (α : Fin (q + 1) → Fin (p + 1)),
    W p t ⟶ W q (t ∘ α)
  indexMap_pr : ∀ {p q : ℕ} (t : Fin (p + 1) → T) (α : Fin (q + 1) → Fin (p + 1))
    (k : Fin (q + 1)), indexMap t α ≫ pr q (t ∘ α) k = pr p t (α k)

namespace SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type w} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U}

private structure FibreData {p : ℕ} (t : Fin (p + 1) → T) where
  W : C
  pr : ∀ k, W ⟶ f (t k)
  comm : ∀ k, pr k ≫ hom (t k) = pr 0 ≫ hom (t 0)
  universal : ∀ (Z : C) (a : ∀ k, Z ⟶ f (t k)),
    (∀ k, a k ≫ hom (t k) = a 0 ≫ hom (t 0)) →
    ∃! b : Z ⟶ W, ∀ k, b ≫ pr k = a k

private def fibreDataZero (t : Fin (0 + 1) → T) : FibreData (hom := hom) t where
  W := f (t 0)
  pr k := eqToHom (by congr 1; exact congrArg t (by omega))
  comm k := by fin_cases k; rfl
  universal Z a _ := by
    refine ⟨a 0, ?_, ?_⟩
    · intro k
      fin_cases k
      simp
    · intro b hb
      simpa using hb 0

private noncomputable def fibreDataStep (J : Precoverage C) [J.HasPullbacks]
    (hcover : Presieve.ofArrows f hom ∈ J U) {p : ℕ} (t : Fin (p + 1 + 1) → T)
    (V : FibreData (hom := hom) (t ∘ Fin.succ)) : FibreData (hom := hom) t := by
  let v := V.pr 0 ≫ hom (t (Fin.succ 0))
  have hp := J.hasPullbacks_of_mem v hcover
  have : HasPullback (hom (t 0)) v :=
    hp.hasPullback (Presieve.ofArrows.mk (t 0))
  let W := pullback (hom (t 0)) v
  let pr : ∀ k, W ⟶ f (t k) :=
    Fin.cases (pullback.fst _ _) (fun k ↦ pullback.snd _ _ ≫ V.pr k)
  have hc (k) : pr k ≫ hom (t k) = pr 0 ≫ hom (t 0) := by
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · rfl
    · change (pullback.snd _ _ ≫ V.pr k) ≫ hom (t k.succ) =
        pullback.fst _ _ ≫ hom (t 0)
      rw [Category.assoc]
      exact (congrArg (fun h ↦ pullback.snd (hom (t 0)) v ≫ h) (V.comm k)).trans
        pullback.condition.symm
  refine ⟨W, pr, hc, ?_⟩
  intro Z a ha
  obtain ⟨b, hb, hu⟩ := V.universal Z (fun k ↦ a k.succ)
    (fun k ↦ (ha k.succ).trans (ha (Fin.succ 0)).symm)
  have hab : a 0 ≫ hom (t 0) = b ≫ v := by
    dsimp [v]
    rw [← Category.assoc, hb 0]
    exact (ha (Fin.succ 0)).symm
  refine ⟨pullback.lift (a 0) b hab, ?_, ?_⟩
  · intro k
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · exact pullback.lift_fst _ _ _
    · change pullback.lift (a 0) b hab ≫ pullback.snd _ _ ≫ V.pr k = a k.succ
      rw [pullback.lift_snd_assoc, hb]
  · intro c hc'
    apply pullback.hom_ext
    · exact (hc' 0).trans (pullback.lift_fst _ _ _).symm
    · rw [pullback.lift_snd]
      exact hu (c ≫ pullback.snd _ _) (fun k ↦ by
        simpa [pr, Category.assoc] using hc' k.succ)

/-- A covering admits all the chosen fibre products and index maps.
Source: Stacks Sites 00VH(3), Cohomology on Sites 03AK, 03AM.
Proof: induct on the number of factors. In degree zero take `f (t 0)` and its identity.
Pull back the last covering arrow along the common map of the previous product to `U`.
Its universal property together with the induction hypothesis gives existence and uniqueness
for the enlarged tuple. Choose the products simultaneously. Each index map is the unique
map to the target product with components `pr (α k)`; their composites to `U` agree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem exists_of_covering (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hcover : Presieve.ofArrows f hom ∈ J U) : Nonempty (SiteCechComplex f hom) := by
  classical
  let D : ∀ (p : ℕ) (t : Fin (p + 1) → T), FibreData (hom := hom) t :=
    fun p ↦ Nat.rec fibreDataZero (fun _ prev t ↦
      fibreDataStep J hcover t (prev (t ∘ Fin.succ))) p
  let W (p t) := (D p t).W
  let pr (p t) := (D p t).pr
  have hc (p t k) := (D p t).comm k
  have hu (p t Z a h) := (D p t).universal Z a h
  have hi {p q : ℕ} (t : Fin (p + 1) → T) (α : Fin (q + 1) → Fin (p + 1)) :
      ∃ b : W p t ⟶ W q (t ∘ α), ∀ k, b ≫ pr q (t ∘ α) k = pr p t (α k) := by
    obtain ⟨b, hb, _⟩ := hu q (t ∘ α) (W p t) (fun k ↦ pr p t (α k))
      (fun k ↦ (hc p t (α k)).trans (hc p t (α 0)).symm)
    exact ⟨b, hb⟩
  refine ⟨{
    W := W
    pr := pr
    comm := hc
    universal := hu
    W_zero := fun _ ↦ rfl
    pr_zero := ?_
    indexMap := fun t α ↦ (hi t α).choose
    indexMap_pr := fun t α ↦ (hi t α).choose_spec }⟩
  intro t
  rfl

variable (S : SiteCechComplex f hom)

/-- Any two chosen products have exactly one projection-compatible isomorphism.
Source: Stacks 03AK, 03AM.
Proof: each universal property gives a unique map to the other product. Each composite
has the same projections as the identity, so equals the identity by uniqueness. Any
other compatible isomorphism has the same forward map, hence is the same isomorphism.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem fibreIso_exists_unique (S' : SiteCechComplex f hom) (p : ℕ)
    (t : Fin (p + 1) → T) :
    ∃! e : S.W p t ≅ S'.W p t, ∀ k, e.hom ≫ S'.pr p t k = S.pr p t k := by
  obtain ⟨a, ha, hua⟩ := S'.universal p t (S.W p t) (S.pr p t) (S.comm p t)
  obtain ⟨b, hb, hub⟩ := S.universal p t (S'.W p t) (S'.pr p t) (S'.comm p t)
  have hab : a ≫ b = 𝟙 _ := by
    obtain ⟨c, hc, huc⟩ := S.universal p t (S.W p t) (S.pr p t) (S.comm p t)
    apply (huc _ _).trans (huc _ _).symm
    · intro k
      rw [Category.assoc, hb, ha]
    · intro k
      simp
  have hba : b ≫ a = 𝟙 _ := by
    obtain ⟨c, hc, huc⟩ := S'.universal p t (S'.W p t) (S'.pr p t) (S'.comm p t)
    apply (huc _ _).trans (huc _ _).symm
    · intro k
      rw [Category.assoc, ha, hb]
    · intro k
      simp
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro e he
  apply Iso.ext
  exact hua e.hom he

/-- The product of presheaf sections in degree `p`, with componentwise group operations.
Source: Stacks 03AK, 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
def cochains (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) : AddCommGrpCat.{max r w} :=
  AddCommGrpCat.of (∀ t : Fin (p + 1) → T, F.obj (op (S.W p t)))

/-- The alternating restriction formula, omitting the `j`th factor via `Fin.succAbove`.
Source: Stacks 03AL (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def differentialValue (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ)
    (s : S.cochains F p) : S.cochains F (p + 1) :=
  fun t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (F.map (S.indexMap t j.succAbove).op) (s (t ∘ j.succAbove))

/-- The differential preserves zero. Source: Stacks 03AL.
Proof: every restriction homomorphism takes zero to zero; every signed summand is zero.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differentialValue_zero (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.differentialValue F p 0 = 0 := by
  funext t
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (F.map (S.indexMap t j.succAbove).op) 0) = 0
  simp

/-- The differential preserves addition. Source: Stacks 03AL.
Proof: distribute each restriction homomorphism and integer scalar multiplication over
addition, then distribute the finite sum, componentwise.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differentialValue_add (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ)
    (s t : S.cochains F p) :
    S.differentialValue F p (s + t) = S.differentialValue F p s +
      S.differentialValue F p t := by
  funext u
  simp [differentialValue, cochains, map_add, smul_add, Finset.sum_add_distrib]

/-- The differential as an actual group homomorphism.
Source: Stacks 03AL (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def differential (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.cochains F p ⟶ S.cochains F (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := S.differentialValue F p
      map_zero' := S.differentialValue_zero F p
      map_add' := S.differentialValue_add F p }

private theorem projection_ext {p : ℕ} {t : Fin (p + 1) → T} {Z : C}
    (a b : Z ⟶ S.W p t) (h : ∀ k, a ≫ S.pr p t k = b ≫ S.pr p t k) : a = b := by
  have hc (k) : (b ≫ S.pr p t k) ≫ hom (t k) =
      (b ≫ S.pr p t 0) ≫ hom (t 0) := by
    simp only [Category.assoc, S.comm]
  obtain ⟨c, _, hu⟩ := S.universal p t Z (fun k ↦ b ≫ S.pr p t k) hc
  exact (hu a h).trans (hu b (fun _ ↦ rfl)).symm

private def cochainsIndexMap (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) {p q : ℕ}
    (α : Fin (q + 1) → Fin (p + 1)) : S.cochains F q ⟶ S.cochains F p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ F.map (S.indexMap t α).op (s (t ∘ α))
      map_zero' := by funext t; exact (F.map (S.indexMap t α).op).hom.map_zero
      map_add' := by
        intro a b
        funext t
        exact (F.map (S.indexMap t α).op).hom.map_add _ _ }

private noncomputable def cosimplicial (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    CosimplicialObject AddCommGrpCat.{max r w} where
  obj n := S.cochains F n.len
  map α := S.cochainsIndexMap F α.toOrderHom
  map_id n := by
    have hi (t : Fin (n.len + 1) → T) : S.indexMap t id = 𝟙 _ := by
      apply S.projection_ext
      intro k
      exact (S.indexMap_pr t id k).trans (Category.id_comp _).symm
    apply AddCommGrpCat.ext
    intro s
    funext t
    change F.map (S.indexMap t id).op (s t) = s t
    rw [hi]
    simp
  map_comp α β := by
    have hi (t) : S.indexMap t (β.toOrderHom ∘ α.toOrderHom) =
        S.indexMap t β.toOrderHom ≫ S.indexMap (t ∘ β.toOrderHom) α.toOrderHom := by
      apply S.projection_ext
      intro k
      symm
      rw [Category.assoc]
      exact (congrArg (fun h ↦ S.indexMap t β.toOrderHom ≫ h)
        (S.indexMap_pr (t ∘ β.toOrderHom) α.toOrderHom k)).trans
        ((S.indexMap_pr t β.toOrderHom (α.toOrderHom k)).trans
          (S.indexMap_pr t (β.toOrderHom ∘ α.toOrderHom) k).symm)
    apply AddCommGrpCat.ext
    intro s
    funext t
    change F.map (S.indexMap t (β.toOrderHom ∘ α.toOrderHom)).op
        (s (t ∘ (β.toOrderHom ∘ α.toOrderHom))) =
      F.map (S.indexMap t β.toOrderHom).op
        (F.map (S.indexMap (t ∘ β.toOrderHom) α.toOrderHom).op
          (s ((t ∘ β.toOrderHom) ∘ α.toOrderHom)))
    rw [hi, op_comp, F.map_comp]
    rfl

private theorem differential_eq (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.differential F p =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (S.cosimplicial F) p := by
  apply AddCommGrpCat.ext
  intro s
  funext t
  change S.differentialValue F p s t =
    (AddCommGrpCat.homAddEquiv
      (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • (S.cosimplicial F).δ j) s) t
  rw [map_sum]
  simp only [map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  change S.differentialValue F p s t =
    (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (fun t ↦ F.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove)))) t
  simp only [differentialValue, Finset.sum_apply, Pi.smul_apply]

/-- Consecutive differentials compose to zero. Source: Stacks 03AK after equation 03AL.
Proof: expand the double sum. Index maps compose as maps of finite sets, by the universal
property of the target product. For `i ≤ j`, the injections omitting `i` then `j` agree with
those omitting `j+1` then `i`. Pair `(i,j)` with `(j+1,i)`; restrictions agree and the signs
are opposite. These pairs partition the double sum, so all terms cancel.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differential_squared (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.differential F p ≫ S.differential F (p + 1) = 0 := by
  rw [S.differential_eq, S.differential_eq]
  exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (S.cosimplicial F) p

/-- The nonnegative Čech complex, constructed from its specified objects and differential.
Source: Stacks 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complex (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    CochainComplex AddCommGrpCat.{max r w} ℕ :=
  CochainComplex.of (S.cochains F) (S.differential F) (S.differential_squared F)

/-- A presheaf morphism acts on each factor by its component at the chosen product.
Source: Stacks 03AO, 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
def cochainsMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (p : ℕ) :
    S.cochains F p ⟶ S.cochains G p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ φ.app (op (S.W p t)) (s t)
      map_zero' := funext fun t ↦ (φ.app (op (S.W p t))).hom.map_zero
      map_add' := fun s s' ↦ funext fun t ↦
        (φ.app (op (S.W p t))).hom.map_add (s t) (s' t) }

/-- The component maps commute with the alternating differential. Source: Stacks 03AO.
Proof: naturality of `φ` commutes with each omitted-factor restriction; its additivity
commutes with integer multiples and the finite sum. The two components therefore agree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem cochainsMap_comm {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (p : ℕ) :
    S.cochainsMap φ p ≫ (S.complex G).d p (p + 1) =
      (S.complex F).d p (p + 1) ≫ S.cochainsMap φ (p + 1) := by
  simp only [complex, CochainComplex.of_d]
  apply AddCommGrpCat.ext
  intro s
  funext t
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (G.map (S.indexMap t j.succAbove).op)
        (φ.app _ (s (t ∘ j.succAbove)))) =
    φ.app _ (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (F.map (S.indexMap t j.succAbove).op) (s (t ∘ j.succAbove)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  exact congrArg (fun h ↦ h (s (t ∘ j.succAbove)))
    (φ.naturality (S.indexMap t j.succAbove).op).symm

/-- The specified morphism of Čech complexes induced by a presheaf morphism.
Source: Stacks 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complexMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) :
    S.complex F ⟶ S.complex G :=
  CochainComplex.ofHom (S.cochainsMap φ) (S.cochainsMap_comm φ)

/-- Identity transformations act as identities on the Čech complex. Source: Stacks 03AO.
Proof: in each factor the identity transformation is the identity group homomorphism;
complex morphisms are determined by their degree components.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem complexMap_id (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    S.complexMap (𝟙 F) = 𝟙 (S.complex F) := by
  ext p s
  rfl

/-- The Čech construction preserves composition. Source: Stacks 03AO.
Proof: transformation composition is componentwise composition; this is also the
composition of the displayed maps on each product of sections, in each degree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem complexMap_comp {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (ψ : G ⟶ H) :
    S.complexMap (φ ≫ ψ) = S.complexMap φ ≫ S.complexMap ψ := by
  ext p s
  rfl

/-- The Čech complex functor on presheaves of abelian groups.
Source: Stacks 03AO, 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ CochainComplex AddCommGrpCat.{max r w} ℕ where
  obj := S.complex
  map := S.complexMap
  map_id := S.complexMap_id
  map_comp := S.complexMap_comp

/-- The Čech complex functor is additive. Source: Stacks 03AO.
Proof: transformations add sectionwise (lem-weil-pbc-abelian-presheaves-evaluation-exact).
The product maps therefore preserve sums of morphisms, and equality of complex morphisms
is degreewise equality. (blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem complexFunctor_additive :
    (S.complexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      CochainComplex AddCommGrpCat.{max r w} ℕ).Additive := by
  constructor
  intro F G φ ψ
  ext p s
  rfl

/-- The integer-indexed complex functor, zero in all negative degrees.
Source: Stacks 03AM, 03AO (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def integerComplexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ CochainComplex AddCommGrpCat.{max r w} ℤ :=
  S.complexFunctor ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max r w}

/-- The integer-indexed Čech functor is additive. Source: Stacks 03AO.
Proof: the nonnegative complex functor is additive, and extension by zero is additive
componentwise. Their composite is additive.
(blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem integerComplexFunctor_additive :
    (S.integerComplexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      CochainComplex AddCommGrpCat.{max r w} ℤ).Additive := by
  dsimp [integerComplexFunctor]
  infer_instance

/-- Čech cohomology is the cohomology of the constructed complex, hence kernel modulo image;
in degree zero the incoming differential is zero.
Source: Stacks 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def cohomologyFunctor (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{max r w} :=
  S.complexFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p

/-- The Čech cohomology functors are additive. Source: Stacks 03AM, 03AO.
Proof: the complex functor is additive, as is the homology functor of an abelian category
(def-weil-abstract-derived-category); their composite is additive.
(blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem cohomologyFunctor_additive (p : ℕ) :
    (S.cohomologyFunctor p : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      AddCommGrpCat.{max r w}).Additive := by
  dsimp [cohomologyFunctor]
  infer_instance

/-- Exact presheaf sequences give exact sequences in every Čech degree. Source: Stacks 03AQ.
Proof: evaluation at each chosen product is exact by
lem-weil-pbc-abelian-presheaves-evaluation-exact. A product of exact abelian-group sequences
is exact: choose a preimage in each factor for any kernel element. This also includes the
empty product. These are precisely the components of `cochainsMap`.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem degreewise_exact (A : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{r})) (hA : A.Exact)
    (p : ℕ) : Function.Exact (S.cochainsMap A.f p) (S.cochainsMap A.g p) := by
  classical
  have he (t : Fin (p + 1) → T) :
      Function.Exact (A.f.app (op (S.W p t))) (A.g.app (op (S.W p t))) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (hA.map ((evaluation _ _).obj (op (S.W p t))))
  intro s
  constructor
  · intro hs
    have hs' (t : Fin (p + 1) → T) : A.g.app (op (S.W p t)) (s t) = 0 :=
      congrFun hs t
    choose a ha using fun t ↦ (he t (s t)).mp (hs' t)
    exact ⟨a, funext ha⟩
  · rintro ⟨a, rfl⟩
    funext t
    exact (he t _).mpr ⟨a t, rfl⟩

private noncomputable def comparisonMapOf (S' : SiteCechComplex f hom)
    (i : ∀ p t, S'.W p t ⟶ S.W p t)
    (hi : ∀ p t k, i p t ≫ S.pr p t k = S'.pr p t k)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) : S.complex F ⟶ S'.complex F :=
  CochainComplex.ofHom (fun p ↦ AddCommGrpCat.ofHom
    { toFun := fun s t ↦ F.map (i p t).op (s t)
      map_zero' := by funext t; exact (F.map (i p t).op).hom.map_zero
      map_add' := by intro a b; funext t; exact (F.map (i p t).op).hom.map_add _ _ })
    (by
      intro p
      simp only [complex, CochainComplex.of_d]
      apply AddCommGrpCat.ext
      intro s
      funext t
      change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        F.map (S'.indexMap t j.succAbove).op
          (F.map (i p (t ∘ j.succAbove)).op (s (t ∘ j.succAbove)))) =
        F.map (i (p + 1) t).op (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          F.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove)))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_zsmul]
      congr 1
      have h : S'.indexMap t j.succAbove ≫ i p (t ∘ j.succAbove) =
          i (p + 1) t ≫ S.indexMap t j.succAbove := by
        apply S.projection_ext
        intro k
        simp only [Category.assoc]
        rw [hi, S'.indexMap_pr, S.indexMap_pr, hi]
      have h' := congrArg (fun a ↦ F.map a.op) h
      simp only [op_comp, F.map_comp] at h'
      exact congrArg (fun a ↦ a (s (t ∘ j.succAbove))) h')

/-- The complexes from different product choices are canonically naturally isomorphic.
Source: Stacks 03AK, 03AM.
Proof: the unique product isomorphisms commute with all index maps, since their
projections agree. Restriction along the unique projection-compatible map `i` from the
other product (the inverse of that isomorphism, `fibreIso_exists_unique`) gives the
displayed degree maps. They commute with each differential term and have inverse maps
from the opposite product isomorphisms. Naturality in presheaves is componentwise
naturality; thus these give an isomorphism of functors, and homology gives canonical
cohomology isomorphisms.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem comparison_exists (S' : SiteCechComplex f hom) :
    ∃ e : (S.complexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
        CochainComplex AddCommGrpCat.{max r w} ℕ) ≅ S'.complexFunctor,
      ∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) (s : S.cochains F p)
        (t : Fin (p + 1) → T),
        ∀ i : S'.W p t ⟶ S.W p t, (∀ k, i ≫ S.pr p t k = S'.pr p t k) →
          ((e.hom.app F).f p) s t = F.map i.op (s t) := by
  classical
  choose e he hue using fun p t ↦ S.fibreIso_exists_unique S' p t
  have hi (p t k) : (e p t).inv ≫ S.pr p t k = S'.pr p t k := by
    rw [← he p t k, Iso.inv_hom_id_assoc]
  let a (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    S.comparisonMapOf S' (fun p t ↦ (e p t).inv) hi F
  let b (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    S'.comparisonMapOf S (fun p t ↦ (e p t).hom) he F
  have hab (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) : a F ≫ b F = 𝟙 _ := by
    ext p s
    funext t
    change F.map (e p t).hom.op (F.map (e p t).inv.op (s t)) = s t
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, Iso.hom_inv_id]
    simp
  have hba (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) : b F ≫ a F = 𝟙 _ := by
    ext p s
    funext t
    change F.map (e p t).inv.op (F.map (e p t).hom.op (s t)) = s t
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, Iso.inv_hom_id]
    simp
  let E : S.complexFunctor ≅ S'.complexFunctor :=
    NatIso.ofComponents (fun F ↦ ⟨a F, b F, hab F, hba F⟩) (by
      intro F G φ
      ext p s
      funext t
      exact congrArg (fun h ↦ h (s t)) (φ.naturality (e p t).inv.op).symm)
  refine ⟨E, ?_⟩
  intro F p s t i hi'
  have h : i = (e p t).inv := S.projection_ext i _ (fun k ↦ (hi' k).trans (hi p t k).symm)
  subst i
  rfl

/-- Short exact presheaf sequences give short exact sequences of integer-indexed complexes.
Source: Stacks 03AQ.
Proof: evaluate the sequence sectionwise, take products of the resulting exact sequences
as in `degreewise_exact`, and use componentwise injectivity and surjectivity of the maps.
Negative degrees are zero. A sequence of complexes is short exact exactly when it is
short exact in each degree (lem-weil-pbc-cochain-complexes-degreewise-exact).
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem shortExact_map (A : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{r})) (hA : A.ShortExact) :
    (A.map S.integerComplexFunctor).ShortExact := by
  classical
  have hm := hA.mono_f
  have hg := hA.epi_g
  have hn (p : ℕ) :
      ((A.map S.complexFunctor).map (HomologicalComplex.eval _ _ p)).ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.ab_exact_iff_function_exact _).mpr
      exact S.degreewise_exact A hA.exact p
    · apply (AddCommGrpCat.mono_iff_injective _).mpr
      intro a b h
      funext t
      exact (AddCommGrpCat.mono_iff_injective (A.f.app (op (S.W p t)))).mp
        inferInstance (congrFun h t)
    · apply (AddCommGrpCat.epi_iff_surjective _).mpr
      intro s
      have hs (t : Fin (p + 1) → T) :=
        (AddCommGrpCat.epi_iff_surjective (A.g.app (op (S.W p t)))).mp
          inferInstance (s t)
      choose a ha using hs
      exact ⟨a, funext ha⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro z
  let e := ComplexShape.embeddingUpNat
  by_cases hz : ∃ p, e.f p = z
  · obtain ⟨p, hp⟩ := hz
    let i (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) := (S.complex F).extendXIso e hp
    apply ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (i A.X₁).symm (i A.X₂).symm (i A.X₃).symm ?_ ?_) (hn p)
    · change (i A.X₁).inv ≫ (HomologicalComplex.extendMap (S.complexMap A.f) e).f z =
        S.cochainsMap A.f p ≫ (i A.X₂).inv
      rw [HomologicalComplex.extendMap_f _ _ hp]
      simp [i, complexMap]
    · change (i A.X₂).inv ≫ (HomologicalComplex.extendMap (S.complexMap A.g) e).f z =
        S.cochainsMap A.g p ≫ (i A.X₃).inv
      rw [HomologicalComplex.extendMap_f _ _ hp]
      simp [i, complexMap]
  · have hz' (p) : e.f p ≠ z := fun hp ↦ hz ⟨p, hp⟩
    have h₁ := (S.complex A.X₁).isZero_extend_X e z hz'
    have h₂ := (S.complex A.X₂).isZero_extend_X e z hz'
    have h₃ := (S.complex A.X₃).isZero_extend_X e z hz'
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · exact ShortComplex.exact_of_isZero_X₂ _ h₂
    · exact h₁.mono _
    · exact h₃.epi _


end SiteCechComplex
end CategoryTheory
