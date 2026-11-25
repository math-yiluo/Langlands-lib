/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
/-! # Generic ordinary semilinear systems and their representative models

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1;
Stacks 03D1, 03EK, 05RU, 06YY, 07A4 and 0G7E
(auxiliary; not a blueprint node).

## Main definitions

- `Systems`, `DS`: module sheaves on the generic ringed sequence site and their localization.
- `evaluation`, `coefficientMap`, `reduction`: the actual component and transition operations.
- `ScalarData`: scalar adjunctions normalized on ordinary and K-flat representatives.
- `TensorComparisonModel`: tensor comparisons fixed on actual total-complex summands.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r c₂ v₂ k
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

section Foundation

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)

/-- The site fits in the chosen coefficient universe.
Source: the small-site size convention (auxiliary; not a blueprint node).
Proof: the supplied EssentiallySmall instance is exactly this small-model witness. -/
theorem siteSmall : EssentiallySmall.{r} C := by
  infer_instance

/-- Canonical abelian sheafification in the chosen coefficient universe.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance abelianSheafify : HasSheafify J AddCommGrpCat.{r} :=
  @SheafOfModules.hasSheafify_coefficientUniverse C _ (siteSmall.{c, v, r}) J

/-- The locally bijective criterion at the same coefficient universe.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance locallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse C _ (siteSmall.{c, v, r}) J

/-- Forget commutativity, retaining the actual coefficient ring sheaf.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
abbrev ring (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

/-- The recorded module-sheaf category, with the coefficient universe independent of the site.
Source: Stacks 03D1 (auxiliary; not a blueprint node). -/
abbrev Mod (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (ring.{c, v, r} J R)

/-- The canonical abelian structure on the actual module-sheaf category.
Source: Stacks 03D1 (auxiliary; not a blueprint node). -/
instance moduleAbelian (R : Sheaf J CommRingCat.{r}) :
    Abelian (Mod.{c, v, r} J R) :=
  letI : HasSheafify J AddCommGrpCat.{r} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  inferInstance

/-- The standard ordinary localization at quasi-isomorphisms.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
instance hasDerived (R : Sheaf J CommRingCat.{r}) :
    HasDerivedCategory.{max c v (r + 1)} (Mod.{c, v, r} J R) :=
  HasDerivedCategory.standard _

/-- The ordinary unbounded derived module category.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
abbrev D (R : Sheaf J CommRingCat.{r}) :=
  @DerivedCategory (Mod.{c, v, r} J R) _ _ (hasDerived.{c, v, r} J R)

variable (B : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The sequence site is essentially small in the same coefficient universe.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: take a small model of C and its product with the natural-number poset,
using a universe lift of the latter. The product of the two equivalences is an
equivalence with a category whose objects and arrows lie in the coefficient universe. -/
theorem sequenceSmall : EssentiallySmall.{r} (ℕ × C) := by
  exact EssentiallySmall.mk'
    ((AsSmall.equiv : ℕ ≌ AsSmall.{r} ℕ).prod (equivSmallModel.{r} C))

attribute [instance] sequenceSmall

/-- A slice of an essentially small category is essentially small in the same universe.
Source: the small-site convention (auxiliary; not a blueprint node).
Proof: an equivalence with a small model induces an equivalence of slice categories.
The slice of the small model has objects and morphisms in the same universe. -/
theorem sliceSmall (U : C) : EssentiallySmall.{r} (Over U) := by
  exact EssentiallySmall.mk' (Over.postEquiv U (equivSmallModel.{r} C))

attribute [instance] sliceSmall

/-- All coefficient transitions, obtained by composing the given adjacent maps.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def rings : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r} := Functor.ofOpSequence τ

/-- The ring presheaf with value B_n(U) and the given horizontal restrictions.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def ringPresheaf : (ℕ × C)ᵒᵖ ⥤ CommRingCat.{r} :=
  (prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj
    (rings.{c, v, r} J B τ ⋙ sheafToPresheaf J CommRingCat.{r})

private theorem sequence_isSheaf_of_slices {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type k)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

private theorem uncurry_slice_eq' {C : Type c} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ CommRingCat.{r}) (n : ℕ) :
    (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F = F.obj (op n) := by
  apply CategoryTheory.Functor.ext
    (F := (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F) (G := F.obj (op n)) (fun _ ↦ rfl) ?_
  intro X Y f
  change (F.map (𝟙 (op n))).app X ≫ (F.obj (op n)).map f = _
  rw [F.map_id]
  simp

private theorem horizontal_map' {C : Type c} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ CommRingCat.{r}) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    ((prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj F).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op = (F.map (homOfLE h).op).app U := by
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option linter.unusedSectionVars false in
/-- The actual ring presheaf is a sheaf for the vertical sequence topology.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: glue in B_n on the vertical covering slice. Separatedness on the pullbacks of
that cover verifies compatibility with horizontal restrictions. The algebra operations
commute with gluing since each B_n is a ring sheaf. -/
theorem ringPresheaf_isSheaf :
    Presheaf.IsSheaf (coefficientSequenceTopology J) (ringPresheaf.{c, v, r} J B τ) := by
  intro A
  apply sequence_isSheaf_of_slices
  intro n
  dsimp only [ringPresheaf]
  rw [← Functor.assoc, uncurry_slice_eq']
  exact ((rings.{c, v, r} J B τ).obj (op n)).property A

/-- The ring object B_bullet, with real presheaf data.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def systemRing : Sheaf (coefficientSequenceTopology J) CommRingCat.{r} :=
  ⟨ringPresheaf.{c, v, r} J B τ, ringPresheaf_isSheaf.{c, v, r} J B τ⟩

/-- Strict semilinear systems, realized as module sheaves on the sequence site.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
abbrev Systems := Mod.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ)

/-- D(S(B)), rather than a category of diagrams in derived categories.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
abbrev DS := D.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ)

set_option linter.unusedSectionVars false in
/-- The slice inclusion is continuous for the actual vertical topology.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: a covering sieve restricts to a covering sieve on its vertical slice by the
definition of coefficientSequenceTopology. The sheaf condition restricts accordingly. -/
theorem evaluation_continuous (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
    have he' : f₁.2 ≫ g₁ = f₂.2 ≫ g₂ := congrArg Prod.snd he
    have hx' := hx f₁.2 f₂.2 hg₁ hg₂ he'
    let q : X ⟶ (n, X.2) := Prod.mkHom f₁.1 (𝟙 _)
    have e₁ : q ≫ (Prod.sectR n C).map f₁.2 = f₁ := by
      ext <;> simp [q]
    have e₂ : q ≫ (Prod.sectR n C).map f₂.2 = f₂ := by
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp [q]
    rw [← e₁, ← e₂, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
    exact congrArg (G.obj.map q.op) hx'
  · constructor
    intro U S hS
    change (S.functorPushforward (Prod.sectR n C)).functorPullback (Prod.sectR n C) ∈ J U
    exact J.superset_covering (Sieve.le_functorPushforward_pullback _ S) hS

/-- Continuity used by continuous module pushforward along the vertical inclusion.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
instance evaluationContinuous (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  evaluation_continuous J n

/-- Evaluation of B_bullet is B_n, including its restriction maps.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: uncurry and ofOpSequence evaluate to B_n(U); the horizontal identity is the
identity ring map. Functor extensionality gives equality of the ring sheaves. -/
theorem evaluation_ring (n : ℕ) :
    ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r}
      J (coefficientSequenceTopology J)).obj
        (ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ)) =
        ring.{c, v, r} J (B n) := by
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro U V f
  simp only [Functor.sheafPushforwardContinuous_obj_obj_map, Prod.sectR_map,
    eqToHom_refl, Category.comp_id, Category.id_comp]
  change (forget₂ CommRingCat.{r} RingCat.{r}).map
      (((rings.{c, v, r} J B τ).map (𝟙 (op n))).hom.app U) ≫
        (forget₂ CommRingCat.{r} RingCat.{r}).map ((B n).obj.map f) =
      (forget₂ CommRingCat.{r} RingCat.{r}).map ((B n).obj.map f)
  rw [(rings.{c, v, r} J B τ).map_id]
  simp

/-- Actual evaluation, using the identity identification of its coefficient sheaf.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def evaluation (n : ℕ) : Systems.{c, v, r} J B τ ⥤ Mod.{c, v, r} J (B n) :=
  SheafOfModules.pushforward (F := Prod.sectR n C)
    (eqToHom (evaluation_ring.{c, v, r} J B τ n).symm)

private theorem sequenceEvaluation_exact
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{r}]
    [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{r}]
    (n : ℕ) {S : Sheaf J RingCat.{r}}
    {R : Sheaf (coefficientSequenceTopology J) RingCat.{r}}
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR n C).sheafPushforwardContinuous
      RingCat.{r} J (coefficientSequenceTopology J)).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{r} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{r} φ) := by
  constructor
  · let T := SheafOfModules.forget.{r} S ⋙ PresheafOfModules.toPresheaf S.obj
    have : PreservesFiniteLimits (SheafOfModules.pushforward.{r} φ ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{r} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (Prod.sectR n C).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let : (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) :=
      ⟨fun hS ↦ hS⟩
    let : ∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}),
        (Prod.sectR n C).op.HasPointwiseRightKanExtension F := fun F X ↦ by
      let : HasLimitsOfShape (StructuredArrow X (Prod.sectR n C).op)
          AddCommGrpCat.{r} := HasLimitsOfShape.of_essentiallySmall _ _
      infer_instance
    let H := (Prod.sectR n C).sheafPushforwardContinuous
      AddCommGrpCat.{r} J (coefficientSequenceTopology J)
    have : PreservesColimitsOfSize.{0, 0} H :=
      ((Prod.sectR n C).sheafAdjunctionCocontinuous AddCommGrpCat.{r}
        J (coefficientSequenceTopology J)).leftAdjoint_preservesColimits
    let T := SheafOfModules.toSheaf.{r} S
    have : PreservesFiniteColimits (SheafOfModules.pushforward.{r} φ ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf.{r} R ⋙ H)
      infer_instance
    have : ReflectsFiniteColimits T :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- Evaluation is additive and exact; kernels and cokernels are componentwise.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: kernels are sectionwise and cokernels are sheafifications of sectionwise
cokernels. Vertical sheafification computes the same sheafification at each level.
Addition of maps is sectionwise as well. -/
theorem evaluation_exact (n : ℕ) :
    (evaluation.{c, v, r} J B τ n).Additive ∧ PreservesFiniteLimits (evaluation.{c, v, r} J B τ n) ∧
      PreservesFiniteColimits (evaluation.{c, v, r} J B τ n) := by
  refine ⟨⟨by intros; ext U x; rfl⟩, ?_⟩
  exact sequenceEvaluation_exact J n
    (eqToHom (evaluation_ring.{c, v, r} J B τ n).symm)

/-- Additivity of the actual evaluation.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
instance evaluationAdditive (n : ℕ) : (evaluation.{c, v, r} J B τ n).Additive :=
  (evaluation_exact.{c, v, r} J B τ n).1

/-- Left exactness of the actual evaluation.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
instance evaluationLimits (n : ℕ) : PreservesFiniteLimits (evaluation.{c, v, r} J B τ n) :=
  (evaluation_exact.{c, v, r} J B τ n).2.1

/-- Right exactness of the actual evaluation.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
instance evaluationColimits (n : ℕ) : PreservesFiniteColimits (evaluation.{c, v, r} J B τ n) :=
  (evaluation_exact.{c, v, r} J B τ n).2.2

/-- Evaluation on the ordinary derived category, computed termwise by its construction.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
abbrev e (n : ℕ) : DS.{c, v, r} J B τ ⥤ D.{c, v, r} J (B n) :=
  letI := evaluationAdditive.{c, v, r} J B τ n
  letI := evaluationLimits.{c, v, r} J B τ n
  letI := evaluationColimits.{c, v, r} J B τ n
  letI := hasDerived.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ)
  letI := hasDerived.{c, v, r} J (B n)
  (evaluation.{c, v, r} J B τ n).mapDerivedCategory

/-- The coefficient homomorphism from m to n is the composite of the supplied tau maps.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def coefficientMap {m n : ℕ} (h : n ≤ m) : B m ⟶ B n :=
  (rings.{c, v, r} J B τ).map (homOfLE h).op

section Scalars

variable {J} {R R' : Sheaf J CommRingCat.{r}} (φ : R ⟶ R')

/-- The recorded, exact restriction-of-scalars functor.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
abbrev res : Mod.{c, v, r} J R' ⥤ Mod.{c, v, r} J R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Restriction leaves the underlying abelian sheaves unchanged, hence is exact.
Source: Stacks 03CZ (auxiliary; not a blueprint node).
Proof: kernels retain their sectionwise groups and cokernels retain their sheafified
sectionwise groups; only the ring action is restricted. -/
theorem res_exact : PreservesFiniteLimits (res.{c, v, r} φ) ∧
    PreservesFiniteColimits (res.{c, v, r} φ) := by
  let U := SheafOfModules.toSheaf.{r} (ring.{c, v, r} J R)
  have : PreservesFiniteLimits (res.{c, v, r} φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{r} (ring.{c, v, r} J R')))
  have : PreservesFiniteColimits (res.{c, v, r} φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{r} (ring.{c, v, r} J R')))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- Left exactness of scalar restriction.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
instance resLimits : PreservesFiniteLimits (res.{c, v, r} φ) := (res_exact.{c, v, r} φ).1

/-- Right exactness of scalar restriction.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
instance resColimits : PreservesFiniteColimits (res.{c, v, r} φ) := (res_exact.{c, v, r} φ).2

/-- Ordinary derived restriction of scalars, computed termwise.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
abbrev resD : D.{c, v, r} J R' ⥤ D.{c, v, r} J R :=
  (res.{c, v, r} φ).mapDerivedCategory

/-- The sectionwise generator 1 tensor x followed by the actual sheafification unit.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
def extensionUnit (M : Mod.{c, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (SheafOfModules.changeOfRings.{v, c, r} φ M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{r, v, r, c}
    (𝟙 (ring.{c, v, r} J R').obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{v, c, r} φ M)).app U
        ((1 : R'.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)

/-- A universal derived scalar-extension pair with its normalized adjunction.
The existing change-of-rings model fixes ordinary extension and its K-flat counit.
The unit-section equation fixes the ordinary adjunction. The representative equation
fixes the derived adjunction and hence its units, counits and transposes.
Source: Stacks 06YY and 07A6 (auxiliary; not a blueprint node). -/
structure ScalarData where
  /-- The dependency's actual everywhere-defined K-flat derived change of rings. -/
  model : @SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, r,
    max c v (r + 1), max c v (r + 1)} C _ (siteSmall.{c, v, r}) J _
      (locallyBijective.{c, v, r} J) (abelianSheafify.{c, v, r} J) R R' φ
      (hasDerived.{c, v, r} J R) (hasDerived.{c, v, r} J R')
  /-- Tensor/restriction adjunction before deriving. -/
  ordinaryAdjunction : model.E ⊣ res.{c, v, r} φ
  /-- The ordinary unit is x mapped to 1 tensor x in the sheafified tensor. -/
  unit_section : ∀ (M : Mod.{c, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U),
    (eqToHom (model.obj_eq M)).val.app U ((ordinaryAdjunction.unit.app M).val.app U x) =
      extensionUnit.{c, v, r} φ M U x
  /-- The derived extension/restriction adjunction. -/
  adjunction : model.T ⊣ resD.{c, v, r} φ
  /-- Its Hom equivalence is the derived ordinary tensor/restriction equivalence. -/
  transpose_model : ∀ (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (Q : CochainComplex (Mod.{c, v, r} J R') ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (R := R) P)
    (f : (model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
    (adjunction.homEquiv _ _) (model.ε.app P ≫ DerivedCategory.Q.map f) ≫
        (Functor.mapDerivedCategoryFactors (res.{c, v, r} φ)).hom.app Q =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f)

/-- The model's actual scalar-extension functor, with all projection universes fixed.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev ScalarData.T (A : ScalarData.{c, v, r} φ) :
    D.{c, v, r} J R ⥤ D.{c, v, r} J R' :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.T.{c, v, r,
    max c v (r + 1), max c v (r + 1)} C _ (siteSmall.{c, v, r}) J _
      (locallyBijective.{c, v, r} J) (abelianSheafify.{c, v, r} J) R R' φ
      (hasDerived.{c, v, r} J R) (hasDerived.{c, v, r} J R') A.model

end Scalars

/-- The canonical restriction-composition identification is the identity on sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node).
Proof: the tower functor sends composition to composition of ring maps. Both scalar
restrictions have the same section groups with this composite action. Identity section
maps therefore give an isomorphism, uniquely determined by the displayed formula. -/
theorem restrictionComposition_existsUnique {l m n : ℕ} (h : n ≤ m) (k : m ≤ l) :
    ∃! δ : res.{c, v, r} (coefficientMap.{c, v, r} J B τ h) ⋙
        res.{c, v, r} (coefficientMap.{c, v, r} J B τ k) ≅
      res.{c, v, r} (coefficientMap.{c, v, r} J B τ (h.trans k)),
      ∀ (M : Mod.{c, v, r} J (B n)) (U : Cᵒᵖ),
        HEq (fun x ↦ ((δ.hom.app M).val.app U) x) (fun x : M.val.obj U ↦ x) := by
  have hcomp : coefficientMap.{c, v, r} J B τ (h.trans k) =
      coefficientMap.{c, v, r} J B τ k ≫ coefficientMap.{c, v, r} J B τ h := by
    exact (rings.{c, v, r} J B τ).map_comp (homOfLE k).op (homOfLE h).op
  let δ : res.{c, v, r} (coefficientMap.{c, v, r} J B τ h) ⋙
      res.{c, v, r} (coefficientMap.{c, v, r} J B τ k) ≅
      res.{c, v, r} (coefficientMap.{c, v, r} J B τ (h.trans k)) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((coefficientMap.{c, v, r} J B τ k).hom.app U).hom
          ((coefficientMap.{c, v, r} J B τ h).hom.app U).hom
          ((coefficientMap.{c, v, r} J B τ (h.trans k)).hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) hcomp) (M.val.obj U)).symm)
        (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  refine ⟨δ, fun _ _ ↦ HEq.rfl, ?_⟩
  intro δ' hδ'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrFun (eq_of_heq (hδ' M U)) x

/-- Derived restriction composition is the localization of the section identity.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
def restrictionComposition {l m n : ℕ} (h : n ≤ m) (k : m ≤ l) :
    resD.{c, v, r} (coefficientMap.{c, v, r} J B τ h) ⋙
        resD.{c, v, r} (coefficientMap.{c, v, r} J B τ k) ≅
      resD.{c, v, r} (coefficientMap.{c, v, r} J B τ (h.trans k)) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (restrictionComposition_existsUnique.{c, v, r} J B τ h k).exists.choose

private theorem transition_generic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    {m n : ℕ} (S T : Sheaf J RingCat.{r})
    [Functor.IsContinuous (Prod.sectR m C) J (coefficientSequenceTopology J)]
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR m C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj R)
    (ψ : T ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj R)
    (κ : S ⟶ T) (α : Prod.sectR n C ⟶ Prod.sectR m C)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{r} J
      (coefficientSequenceTopology J)).app R = κ ≫ ψ) :
    ∃! δ : SheafOfModules.pushforward.{r} φ ⟶
        SheafOfModules.pushforward.{r} ψ ⋙ SheafOfModules.restrictScalars κ,
      ∀ (M : SheafOfModules.{r} R) (U : Cᵒᵖ),
        HEq (fun x ↦ ((δ.app M).val.app U) x)
          (fun x : M.val.obj (op (m, U.unop)) ↦ M.val.map (α.app U.unop).op x) := by
  let δ : SheafOfModules.pushforward.{r} φ ⟶
      SheafOfModules.pushforward.{r} ψ ⋙ SheafOfModules.restrictScalars κ :=
    SheafOfModules.pushforwardNatTrans φ α ≫
      (SheafOfModules.pushforwardCongr he).hom
  refine ⟨δ, fun _ _ ↦ HEq.rfl, ?_⟩
  intro δ' hδ'
  apply NatTrans.ext
  funext M
  ext U x
  exact congrFun (eq_of_heq (hδ' M U)) x

/-- The actual semilinear transition of module systems, specified on every section.
Source: Zheng 4.1 (auxiliary; not a blueprint node).
Proof: the horizontal presheaf restriction is linear over B_m after scalar
restriction to B_n. Site naturality gives a module-sheaf map. Its formula is natural
in the system, and sectionwise extensionality proves uniqueness. -/
theorem transition_exists {m n : ℕ} (h : n ≤ m) :
    ∃! δ : evaluation.{c, v, r} J B τ m ⟶
      evaluation.{c, v, r} J B τ n ⋙ res.{c, v, r} (coefficientMap.{c, v, r} J B τ h),
      ∀ (M : Systems.{c, v, r} J B τ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((δ.app M).val.app U) x)
          (fun x : M.val.obj (op (m, U.unop)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  let α : Prod.sectR n C ⟶ Prod.sectR m C :=
    { app := fun U ↦ Prod.mkHom (homOfLE h) (𝟙 U)
      naturality := fun {_ _} f ↦ by ext <;> simp }
  let φm := eqToHom (evaluation_ring.{c, v, r} J B τ m).symm
  let φn := eqToHom (evaluation_ring.{c, v, r} J B τ n).symm
  let κ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (coefficientMap.{c, v, r} J B τ h)
  have he : φm ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{r} J
      (coefficientSequenceTopology J)).app
        (ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ)) =
      κ ≫ φn := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hm : φm.hom.app U = 𝟙 _ := by
      dsimp only [φm]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hn : φn.hom.app U = 𝟙 _ := by
      dsimp only [φn]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change φm.hom.app U ≫ _ = _ ≫ φn.hom.app U
    rw [hm, hn, Category.id_comp, Category.comp_id]
    change (forget₂ CommRingCat.{r} RingCat.{r}).map
      ((ringPresheaf.{c, v, r} J B τ).map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) = _
    rw [show (ringPresheaf.{c, v, r} J B τ).map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
        ((coefficientMap.{c, v, r} J B τ h).hom.app U) from
      horizontal_map' (rings.{c, v, r} J B τ ⋙ sheafToPresheaf J CommRingCat.{r}) h U]
    rfl
  exact transition_generic J
    (ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ))
    (ring.{c, v, r} J (B m)) (ring.{c, v, r} J (B n)) φm φn κ α he

/-- The strict transition selected by its unique presheaf-restriction formula.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def transition {m n : ℕ} (h : n ≤ m) :=
  (transition_exists.{c, v, r} J B τ h).exists.choose

/-- The same transition on the ordinary localization, rather than an unrelated level map.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def derivedTransition {m n : ℕ} (h : n ≤ m) :
    e.{c, v, r} J B τ m ⟶
      e.{c, v, r} J B τ n ⋙ resD.{c, v, r} (coefficientMap.{c, v, r} J B τ h) :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Systems.{c, v, r} J B τ) (.up ℤ)) _ _
    (evaluation.{c, v, r} J B τ m).mapDerivedCategory
    ((evaluation.{c, v, r} J B τ n ⋙
      res.{c, v, r} (coefficientMap.{c, v, r} J B τ h)).mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (transition.{c, v, r} J B τ h) (.up ℤ))
        DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (evaluation.{c, v, r} J B τ n)
      (res.{c, v, r} (coefficientMap.{c, v, r} J B τ h))).inv

/-- The reduction of M is the extension/restriction transpose of its actual transition.
Source: Zheng 4.1; Stacks 07A6 (auxiliary; not a blueprint node). -/
def reduction {m n : ℕ} (h : n ≤ m)
    (A : ScalarData.{c, v, r} (coefficientMap.{c, v, r} J B τ h))
    (M : DS.{c, v, r} J B τ) :
    A.T.obj ((e.{c, v, r} J B τ m).obj M) ⟶ (e.{c, v, r} J B τ n).obj M :=
  (A.adjunction.homEquiv _ _).symm ((derivedTransition.{c, v, r} J B τ h).app M)

/-- Normalization quantifies over all reduction maps simultaneously.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def Normalized
    (A : ∀ {m n : ℕ} (h : n ≤ m),
      ScalarData.{c, v, r} (coefficientMap.{c, v, r} J B τ h))
    (M : DS.{c, v, r} J B τ) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m), IsIso (reduction.{c, v, r} J B τ h (A h) M)

section RingSystemMap

variable (F : ℕ → Sheaf J CommRingCat.{r})
  (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)

include hα

/-- A compatible coefficient map induces the unique sectionwise ring-system map.
Source: Zheng 4.1; Stacks 03CZ (auxiliary; not a blueprint node).
Proof: use α_n on each section at (n,U). Naturality in U is sheaf-map naturality;
horizontal naturality follows by induction from hα. Component extensionality proves
uniqueness. Thus this is the given coefficient map, not a chosen unrelated morphism. -/
theorem systemMap_existsUnique :
    ∃! f : systemRing.{c, v, r} J B τ ⟶ systemRing.{c, v, r} J F σ,
      ∀ (n : ℕ) (U : Cᵒᵖ), f.hom.app (op (n, U.unop)) = (α n).hom.app U := by
  let a : rings.{c, v, r} J B τ ⟶ rings.{c, v, r} J F σ :=
    NatTrans.ofOpSequence α (fun n ↦ by
      simpa only [rings, Functor.ofOpSequence_map_homOfLE_succ] using (hα n).symm)
  let f : systemRing.{c, v, r} J B τ ⟶ systemRing.{c, v, r} J F σ :=
    ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
      (Functor.uncurry.map (Functor.whiskerRight a (sheafToPresheaf J CommRingCat.{r})))⟩
  refine ⟨f, fun _ _ ↦ rfl, ?_⟩
  intro g hg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact hg U.unop.1 (op U.unop.2)

/-- The coefficient-system map uniquely specified by its components α_n.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
def systemMap : systemRing.{c, v, r} J B τ ⟶ systemRing.{c, v, r} J F σ :=
  (systemMap_existsUnique.{c, v, r} J B τ F σ α hα).exists.choose

/-- Restriction of scalars commutes with evaluation by the identity on sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node).
Proof: both functors keep the same section groups and restrict the B_n action along
α_n. The component identity is linear and natural, and determines the comparison
uniquely. Its inverse is the same section identity. -/
theorem restrictionEvaluation_existsUnique (n : ℕ) :
    ∃! δ : res.{c, v, r} (systemMap.{c, v, r} J B τ F σ α hα) ⋙
        evaluation.{c, v, r} J B τ n ≅
      evaluation.{c, v, r} J F σ n ⋙ res.{c, v, r} (α n),
      ∀ (M : Systems.{c, v, r} J F σ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((δ.hom.app M).val.app U) x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  let φB := eqToHom (evaluation_ring.{c, v, r} J B τ n).symm
  let φF := eqToHom (evaluation_ring.{c, v, r} J F σ n).symm
  let a := (sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{r} RingCat.{r})).map (systemMap.{c, v, r} J B τ F σ α hα)
  let b := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map (α n)
  have he : φB ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r}
      J (coefficientSequenceTopology J)).map a = b ≫ φF := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hB : φB.hom.app U = 𝟙 _ := by
      dsimp only [φB]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hF : φF.hom.app U = 𝟙 _ := by
      dsimp only [φF]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change φB.hom.app U ≫ _ = _ ≫ φF.hom.app U
    rw [hB, hF, Category.id_comp, Category.comp_id]
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{r} RingCat.{r}).map f)
      ((systemMap_existsUnique.{c, v, r} J B τ F σ α hα).exists.choose_spec n U)
  let δ : res.{c, v, r} (systemMap.{c, v, r} J B τ F σ α hα) ⋙
      evaluation.{c, v, r} J B τ n ≅
        evaluation.{c, v, r} J F σ n ⋙ res.{c, v, r} (α n) :=
    SheafOfModules.pushforwardComp (F := Prod.sectR n C) (G := 𝟭 (ℕ × C))
      (K' := coefficientSequenceTopology J)
      (R' := ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J F σ))
      φB a ≪≫
      SheafOfModules.pushforwardCongr he ≪≫
      (SheafOfModules.pushforwardComp (F := 𝟭 C) (G := Prod.sectR n C)
        (K := J) (K' := coefficientSequenceTopology J)
        (R := ring.{c, v, r} J (F n))
        (R' := ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J F σ))
        b φF).symm
  refine ⟨δ, fun _ _ ↦ HEq.rfl, ?_⟩
  intro δ' hδ'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext U x
  exact congrFun (eq_of_heq (hδ' M U)) x

/-- The derived restriction comparison is the localization of the identity on sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
def restrictionEvaluation (n : ℕ) :
    resD.{c, v, r} (systemMap.{c, v, r} J B τ F σ α hα) ⋙ e.{c, v, r} J B τ n ≅
      e.{c, v, r} J F σ n ⋙ resD.{c, v, r} (α n) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (restrictionEvaluation_existsUnique.{c, v, r} J B τ F σ α hα n).exists.choose ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end RingSystemMap

/-- Termwise localization with the standard derived-category instances explicit.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def derivedExact {C₂ : Type c₂} [Category.{v₂} C₂] [EssentiallySmall.{r} C₂]
    (J₂ : GrothendieckTopology C₂) (R : Sheaf J CommRingCat.{r})
    (R₂ : Sheaf J₂ CommRingCat.{r}) (F : Mod.{c, v, r} J R ⥤ Mod.{c₂, v₂, r} J₂ R₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    D.{c, v, r} J R ⥤ D.{c₂, v₂, r} J₂ R₂ :=
  @Functor.mapDerivedCategory _ _ _ (hasDerived.{c, v, r} J R)
    _ _ _ (hasDerived.{c₂, v₂, r} J₂ R₂) F _ _ _

end Foundation

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The dependency's actual derived internal Hom, on the displayed ringed site.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev internalHom (R : Sheaf J CommRingCat.{max c v r}) :
    (D.{c, v, max c v r} J R)ᵒᵖ × D.{c, v, max c v r} J R ⥤ D.{c, v, max c v r} J R :=
  @derivedInternalHomOfUniverses.{c, v, r, (max c v r) + 1} C _ J
    (abelianSheafify.{c, v, max c v r} J) (locallyBijective.{c, v, max c v r} J) R
      (hasDerived.{c, v, max c v r} J R)

/-- Closed tensor data for the actual derived internal Hom.
Source: Stacks 07A4, 08J9 (auxiliary; not a blueprint node). -/
abbrev Closed (R : Sheaf J CommRingCat.{max c v r}) :=
  CoefficientClosedStructure (internalHom.{c, v, r} J R)

/-- The recorded total-tensor/K-flat representative model of closed tensor.
Source: Stacks 06YS, 07A4 (auxiliary; not a blueprint node). -/
abbrev Models (R : Sheaf J CommRingCat.{max c v r}) (S : Closed.{c, v, r} J R) :=
  @CoefficientTensorModels.{r, c, v, (max c v r) + 1} C _ J
    (abelianSheafify.{c, v, max c v r} J) (locallyBijective.{c, v, max c v r} J) R
      (hasDerived.{c, v, max c v r} J R) S

/-- Ordinary sheaf tensor with the monoidal convention of the representative model.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev ordinaryTensor (R : Sheaf J CommRingCat.{max c v r})
    (M N : Mod.{c, v, max c v r} J R) : Mod.{c, v, max c v r} J R :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} J
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  (SheafOfModules.monoidalCategory.{v, c, max c v r} R).tensorObj M N

/-- A local pure tensor in the actual monoidal sheaf tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def tensorSection (R : Sheaf J CommRingCat.{max c v r})
    (M N : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (ordinaryTensor.{c, v, r} J R M N).val.obj U :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} J
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} (R := R) M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
      (𝟙 (ring.{c, v, max c v r} J R).obj)).unit.app (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- The recorded total tensor with the canonical coefficient-size instances.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
abbrev totalTensor (R : Sheaf J CommRingCat.{max c v r}) :=
  @coefficientTotalTensor.{r, c, v} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) R

/-- Tensor of ordinary morphisms in the same canonical monoidal structure.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def ordinaryTensorHom (R : Sheaf J CommRingCat.{max c v r})
    {M N M' N' : Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N') :
    ordinaryTensor.{c, v, r} J R M N ⟶ ordinaryTensor.{c, v, r} J R M' N' :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} J
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  (SheafOfModules.monoidalCategory.{v, c, max c v r} R).tensorHom f g

/-- The actual total-tensor summand inclusion, with the required instances explicit.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
def tensorSummand (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) :
    ordinaryTensor.{c, v, r} J R (P.X p) (Q.X q) ⟶
      ((totalTensor.{c, v, r} J R).obj (P, Q)).X k :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} J
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  letI := SheafOfModules.monoidalCategory.{v, c, max c v r} R
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  HomologicalComplex.ιMapBifunctor P Q (CategoryTheory.MonoidalCategory.curriedTensor _)
    (ComplexShape.up ℤ) p q k h

/-- The dependency's K-flat comparison with explicit coefficient-size instances.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
abbrev tensorModelIso (R : Sheaf J CommRingCat.{max c v r})
    (A : Closed.{c, v, r} J R) (T : Models.{c, v, r} J R A) :=
  @CoefficientTensorModels.iso.{r, c, v, (max c v r) + 1} C _ J
    (abelianSheafify.{c, v, max c v r} J) (locallyBijective.{c, v, max c v r} J) R
      (hasDerived.{c, v, max c v r} J R) A T

/-- The usual flat-term representative class, with independent site sizes.
Source: Stacks 03ER, 06YS, 0G7E (auxiliary; not a blueprint node). -/
def flatTerms (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ) : Prop :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} J
  ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
    (J := J) (R := R) (P.X p)

/-- Representative normalization of an exact tensor comparison. The chain map is
fixed on every total summand by the inverse ordinary comparison. Its localized
square fixes the derived comparison on K-flat representatives, on the system
category itself, rather than merely after evaluation.
Source: Stacks 03EL, 07A4 (auxiliary; not a blueprint node). -/
structure TensorComparisonModel {C' : Type c} [Category.{v} C']
    [EssentiallySmall.{max c v r} C'] (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J' S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : Closed.{c, v, r} J R) (A' : Closed.{c, v, r} J' S)
    (T : Models.{c, v, r} J R A) (T' : Models.{c, v, r} J' S A')
    (μ : A.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ A'.tensor) where
  /-- Ordinary tensor preservation; its canonical formula is imposed by the caller. -/
  ordinary : ∀ M N : Mod.{c, v, max c v r} J R,
    F.obj (ordinaryTensor.{c, v, r} J R M N) ≅ ordinaryTensor.{c, v, r} J' S (F.obj M) (F.obj N)
  /-- The inverse ordinary comparison on every summand gives this chain map. -/
  chain : ∀ P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ,
    (totalTensor.{c, v, r} J' S).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J R).obj (P, Q))
  /-- No sign or automorphism may be inserted in a total summand. -/
  summand : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k),
    tensorSummand.{c, v, r} J' S ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h ≫ (chain P Q).f k =
      (ordinary (P.X p) (Q.X q)).inv ≫ F.map (tensorSummand.{c, v, r} J R P Q p q k h)
  /-- Inverse image/evaluation preserves the representative class. -/
  kflat : ∀ (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J') (R := S)
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
  /-- The derived comparison is precisely the localization of that chain map. -/
  derived : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
    (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q),
    (tensorModelIso.{c, v, r} J' S A' T' ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) (kflat P hP flatP) (kflat Q hQ flatQ)).hom ≫
      A'.tensor.map (Prod.mkHom
        ((Functor.mapDerivedCategoryFactors F).inv.app P)
        ((Functor.mapDerivedCategoryFactors F).inv.app Q)) ≫
      μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      F.mapDerivedCategory.map ((tensorModelIso.{c, v, r} J R A T P Q hP hQ).inv) ≫
      (Functor.mapDerivedCategoryFactors F).hom.app
        ((totalTensor.{c, v, r} J R).obj (P, Q)) = DerivedCategory.Q.map (chain P Q)

/-- The section carried by a scalar-extension functor's ordinary unit.  The
object equality in the derived change-of-rings model is used explicitly, so
this is the actual model `E`, rather than an unrelated extension functor.
Source: Stacks 03CZ, 06YY (auxiliary; not a blueprint node). -/
def scalarExtensionSection {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{max c v r} C]
    {R R' : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ R')
    (A : ScalarData.{c, v, max c v r} φ)
    (M : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (A.model.E.obj M).val.obj U :=
  (eqToHom (A.model.obj_eq M).symm).val.app U
    (extensionUnit.{c, v, max c v r} φ M U x)

/-- The ordinary scalar/tensor comparison is fixed on pure tensors.  This is
the change-of-rings map `(x ⊗ y) ⊗ 1 ↦ (x ⊗ 1) ⊗ (y ⊗ 1)` on every generalized
section, with the actual sheafification unit and the chosen ordinary comparison.
Source: Stacks 03EK and 06YY (auxiliary; not a blueprint node). -/
def ScalarTensorPure {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{max c v r} C]
    {R R' : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ R')
    (A : ScalarData.{c, v, max c v r} φ)
    (ordinary : ∀ M N : Mod.{c, v, max c v r} J R,
      A.model.E.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} J R' (A.model.E.obj M) (A.model.E.obj N)) : Prop :=
  ∀ (M N : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    (ordinary M N).hom.val.app U
      (scalarExtensionSection.{c, v, r} φ A (ordinaryTensor.{c, v, r} J R M N) U
        (tensorSection.{c, v, r} J R M N U x y)) =
      tensorSection.{c, v, r} J R' (A.model.E.obj M) (A.model.E.obj N) U
        (scalarExtensionSection.{c, v, r} φ A M U x)
        (scalarExtensionSection.{c, v, r} φ A N U y)

/-- The K-flat counit of the actual scalar-extension model, packaged as an
isomorphism on a chosen K-flat representative; it is invertible there by the
model's `computes` field.
Source: Stacks 06YY, 07A6 (auxiliary; not a blueprint node). -/
noncomputable def scalarEpsilonIso {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{max c v r} C]
    {R R' : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ R')
    (A : ScalarData.{c, v, max c v r} φ)
    (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) P) :
    (DerivedCategory.Q ⋙ A.model.T).obj P ≅
      (A.model.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).obj P :=
  @asIso _ _ _ _ (A.model.ε.app P) (A.model.computes P hP)

/-- A scalar/tensor comparison carrying the K-flat representative square
and its pure-tensor ordinary normalization. Unlike an exact inverse-image
comparison, scalar extension is only required to preserve the K-flat class;
its derived comparison is written with the model counits `ε`.
Source: Stacks 03EK, 06YY, 07A4 (auxiliary; not a blueprint node). -/
structure ScalarTensorComparisonModel {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C)
    (R R' : Sheaf J CommRingCat.{max c v r}) (φ : R ⟶ R')
    (A : ScalarData.{c, v, max c v r} φ)
    (S : Closed.{c, v, r} J R) (S' : Closed.{c, v, r} J R')
    (T : Models.{c, v, r} J R S) (T' : Models.{c, v, r} J R' S')
    (μ : S.tensor ⋙ A.T ≅ (A.T.prod A.T) ⋙ S'.tensor) where
  /-- Ordinary scalar-extension/tensor comparison; fixed by `ordinary_pure`. -/
  ordinary : ∀ M N : Mod.{c, v, max c v r} J R,
    A.model.E.obj (ordinaryTensor.{c, v, r} J R M N) ≅
      ordinaryTensor.{c, v, r} J R' (A.model.E.obj M) (A.model.E.obj N)
  /-- The inverse ordinary comparison on every summand gives this chain map. -/
  chain : ∀ P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ,
    (totalTensor.{c, v, r} J R').obj
      ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P,
        (A.model.E.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (A.model.E.mapHomologicalComplex (.up ℤ)).obj
        ((totalTensor.{c, v, r} J R).obj (P, Q))
  /-- No sign or automorphism may be inserted in a total summand. -/
  summand : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k),
    tensorSummand.{c, v, r} J R'
        ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((A.model.E.mapHomologicalComplex (.up ℤ)).obj Q) p q k h ≫
      (chain P Q).f k =
      (ordinary (P.X p) (Q.X q)).inv ≫
        A.model.E.map (tensorSummand.{c, v, r} J R P Q p q k h)
  /-- Scalar extension preserves flat-term K-flat representatives. -/
  kflat : ∀ (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R') ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- The derived comparison is the localization of that chain map, via the model counits. -/
  derived : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) Q)
    (flatP : flatTerms.{c, v, r} J R P)
    (flatQ : flatTerms.{c, v, r} J R Q)
    (hPQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) ((totalTensor.{c, v, r} J R).obj (P, Q))),
    (tensorModelIso.{c, v, r} J R' S' T'
      ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P)
      ((A.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
      (kflat P hP flatP) (kflat Q hQ flatQ)).hom ≫
      S'.tensor.map (Prod.mkHom
        (scalarEpsilonIso.{c, v, r} φ A P hP).inv
        (scalarEpsilonIso.{c, v, r} φ A Q hQ).inv) ≫
      μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      A.model.T.map
        (tensorModelIso.{c, v, r} J R S T P Q hP hQ).inv ≫
      (scalarEpsilonIso.{c, v, r} φ A
        ((totalTensor.{c, v, r} J R).obj (P, Q)) hPQ).hom =
    DerivedCategory.Q.map (chain P Q)
  /-- The ordinary comparison sends `(x ⊗ y) ⊗ 1` to `(x ⊗ 1) ⊗ (y ⊗ 1)`. -/
  ordinary_pure : ScalarTensorPure.{c, v, r} φ A ordinary

end WeilConjectures.SemilinearSections
