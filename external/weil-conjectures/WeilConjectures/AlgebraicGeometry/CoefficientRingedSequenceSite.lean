/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Homology.RhomGlobalSections
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # The coefficient ringed sequence site and canonical functors

Source: Stacks Project, Tags 0941, 06YY, 079P and 07A6
(auxiliary; not a blueprint node).

## Main definitions

- `coefficientSequenceTopology`: the product sequence site with vertical covers.
- `coefficientSequenceCommRingSheaf`: the actual quotient coefficient ring sheaf.
- `coefficientSequenceModules`: module sheaves on this ringed site.
- `coefficientSequenceEvaluation`: exact restriction to the nth vertical slice.
- `coefficientSequenceLimit`: total derived limit after exact scalar restriction.
- `coefficientSequenceProjection`: its canonical, resolution-normalized projections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The vertical covering condition for a sequence site.
Source: Stacks 0941, sequence-site construction
(auxiliary; not a blueprint node). -/
def coefficientSequenceCovering {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (X : ℕ × C) (S : Sieve X) : Prop :=
  S.functorPullback (Prod.sectR X.1 C) ∈ J X.2

/-- The vertical covering condition satisfies the topology axioms.
Source: Stacks 0941 (auxiliary; not a blueprint node).
Proof: the slice of the maximal sieve is maximal. For pullback along (h,f), the
vertical slice contains the pullback along f of the old vertical slice, so covering
stability and upward closure apply. For local character, test the supplied condition
on every vertical arrow in the covering slice and apply local character in J. -/
theorem coefficientSequenceTopologyAxioms {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (∀ X : ℕ × C, coefficientSequenceCovering J X ⊤) ∧
    (∀ {X Y : ℕ × C} {S : Sieve X} (f : Y ⟶ X),
      coefficientSequenceCovering J X S → coefficientSequenceCovering J Y (S.pullback f)) ∧
    (∀ {X : ℕ × C} {S : Sieve X}, coefficientSequenceCovering J X S →
      ∀ R : Sieve X,
        (∀ {Y : ℕ × C} {f : Y ⟶ X}, S f →
          coefficientSequenceCovering J Y (R.pullback f)) →
        coefficientSequenceCovering J X R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    change (⊤ : Sieve X.2) ∈ J X.2
    exact J.top_mem X.2
  · intro X Y S f hS
    apply J.superset_covering _ (J.pullback_stable f.2 hS)
    intro Z g hg
    change S ((Prod.sectR Y.1 C).map g ≫ f)
    have hs := S.downward_closed hg (Prod.mkHom f.1 (𝟙 Z))
    have he : (Prod.sectR Y.1 C).map g ≫ f =
        Prod.mkHom f.1 (𝟙 Z) ≫ (Prod.sectR X.1 C).map (g ≫ f.2) := by
      ext <;> simp
    exact he.symm ▸ hs
  · intro X S hS R hR
    apply J.transitive hS
    intro Y f hf
    have hr := hR (f := (Prod.sectR X.1 C).map f) hf
    change (R.functorPullback (Prod.sectR X.1 C)).pullback f ∈ J Y
    change (R.pullback ((Prod.sectR X.1 C).map f)).functorPullback
      (Prod.sectR X.1 C) ∈ J Y at hr
    rwa [Sieve.functorPullback_pullback] at hr

/-- The actual sequence topology, with covering determined by the vertical slice.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def coefficientSequenceTopology {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) : GrothendieckTopology (ℕ × C) where
  sieves X := {S | coefficientSequenceCovering J X S}
  top_mem' := (coefficientSequenceTopologyAxioms J).1
  pullback_stable' := fun {_ _ _} f h ↦ (coefficientSequenceTopologyAxioms J).2.1 f h
  transitive' := fun {_ _} h R hh ↦
    (coefficientSequenceTopologyAxioms J).2.2 h R (fun {_ _} hf ↦ hh hf)

set_option backward.defeqAttrib.useBackward true in
private theorem sequenceInclusion_continuous {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
    have h := hx f₁.2 f₂.2 hg₁ hg₂ (congrArg (fun f ↦ f.2) he)
    have h' := congrArg (G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op) h
    change G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
      (G.obj.map (Prod.mkHom (𝟙 n) f₁.2).op (x g₁ hg₁)) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₂.2).op (x g₂ hg₂)) at h'
    have he₁ : Prod.mkHom f₁.1 (𝟙 X.2) ≫ Prod.mkHom (𝟙 n) f₁.2 = f₁ := by
      ext <;> simp
    have he₂ : Prod.mkHom f₁.1 (𝟙 X.2) ≫ Prod.mkHom (𝟙 n) f₂.2 = f₂ := by
      ext
      · exact Subsingleton.elim _ _
      · simp
    have hp₁ : G.obj.map f₁.op (x g₁ hg₁) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₁.2).op (x g₁ hg₁)) := by
      conv_lhs => rw [← he₁, op_comp, G.obj.map_comp]
      rfl
    have hp₂ : G.obj.map f₂.op (x g₂ hg₂) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₂.2).op (x g₂ hg₂)) := by
      conv_lhs => rw [← he₂, op_comp, G.obj.map_comp]
      rfl
    exact hp₁.trans (h'.trans hp₂.symm)
  · constructor
    intro X S hS
    change (S.functorPushforward (Prod.sectR n C)).functorPullback
      (Prod.sectR n C) ∈ J X
    exact J.superset_covering
      (fun _ _ hf ↦ Sieve.image_mem_functorPushforward (Prod.sectR n C) S hf) hS

private theorem diagrams_isGrothendieckAbelian
    (A : Type c) [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (D : Type u) [SmallCategory D] : IsGrothendieckAbelian.{u} (D ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : D ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (D ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u, u} (D ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u, u} (D ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The unchanged sequence site fits in the coefficient universe.
Source: the size convention, Stacks 0941
(auxiliary; not a blueprint node). -/
noncomputable instance (priority := low) coefficientSequenceEssentiallySmall :
    EssentiallySmall.{max u (t + 1)} (ℕ × W.ProEt) := essentiallySmallSelf _

/-- The standard localization at each finite coefficient ring.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
noncomputable instance coefficientFiniteHasDerived (n : ℕ) :
    HasDerivedCategory (SheafOfModules.{max u (t+1)}
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat RingCat)).obj (integralCoefficientCommRingSheaf l E W n))) :=
  HasDerivedCategory.standard _

/-- The vertical inclusion is continuous, so restriction is coefficient evaluation.
Source: Stacks 0941 (auxiliary; not a blueprint node).
Proof: a sequence sheaf restricts to a sheaf on every vertical slice, by the defining
covering condition. The product-site sheaf condition checked above applies to set
sheaves as well as ring sheaves; this is exactly continuity. -/
@[instance]
theorem coefficientSequenceEvaluationContinuous (n : ℕ) :
    (Prod.sectR n W.ProEt).IsContinuous (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) := by
  exact sequenceInclusion_continuous (Scheme.ProEt.topology W) n

/-- The simultaneous resolution instance for the actual constant-coefficient towers.
Source: Stacks 079P and 0941
(auxiliary; not a blueprint node). -/
noncomputable instance coefficientConstantTowersKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ scalarReductionSource l E W) := by
  let A := scalarReductionSource l E W
  let : IsGrothendieckAbelian.{max u (t + 1)} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ A) := by
    have := diagrams_isGrothendieckAbelian A (AsSmall.{max u (t + 1)} ℕᵒᵖ)
    exact IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)
  infer_instance

/-- The standard unbounded localization of constant coefficient towers.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
noncomputable instance coefficientConstantTowerDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  HasDerivedCategory.standard _

/-- The additive structure on the ordinary inverse-limit functor.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
noncomputable instance coefficientConstantTowerLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).Additive := by
  constructor
  intro M N f g
  apply limit.hom_ext
  intro n
  simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

end WeilConjectures
