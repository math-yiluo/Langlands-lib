import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationPresentation
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleTensor
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup

/-! # Actual line bundles of normalized dual-number cocycles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

namespace CocycleGluing

variable {X : Scheme.{u}} {ι : Type u} (T : ι → X.Opens)

/-- Gluing the unit transition cochain on an actual cover gives the structure module. -/
def gluedOneIso (hT : (⨆ i, T i) = ⊤) :
    glued (fun i j ↦ (1 : Γ(X, T i ⊓ T j)ˣ)) ≅ structureModule X := by
  let s : ∀ i, Γ(structureModule X, T i) := fun i ↦ (1 : Γ(X, T i))
  have hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (T i) := by
    intro i W hWU hWV
    change Function.Bijective (fun a : Γ(X, W) ↦
      a * X.presheaf.map (homOfLE hWU).op 1)
    simp only [map_one, mul_one]
    exact Function.bijective_id
  apply (frameIso hs (g := fun i j ↦ (1 : Γ(X, T i ⊓ T j)ˣ)) ?_ hT).symm
  intro i j
  change X.presheaf.map (homOfLE inf_le_right).op 1 =
    (1 : Γ(X, T i ⊓ T j)) * X.presheaf.map (homOfLE inf_le_left).op 1
  simp only [map_one, mul_one]

end CocycleGluing

namespace DualNumberThickening

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type u} (T : ι → X.Opens)

/-- The zero-section pullback of a normalized unit cochain has all transitions equal to one. -/
lemma pullbackCocycle_closedPoint_unitCochain
    (z : ∀ i j, Γ(X, T i ⊓ T j)) :
    CocycleGluing.pullbackCocycle (closedPoint f) (unitCochain f T z) =
      fun i j ↦ 1 := by
  funext i j
  apply Units.ext
  change (closedPoint f).appLE (projection f ⁻¹ᵁ (T i ⊓ T j))
      (closedPoint f ⁻¹ᵁ (projection f ⁻¹ᵁ T i) ⊓
        closedPoint f ⁻¹ᵁ (projection f ⁻¹ᵁ T j)) _
      (coefficientUnit f (T i ⊓ T j) (z i j)).val = 1
  have h : ∀ (V : X.Opens), V = T i ⊓ T j →
      ∀ hV : V ≤ closedPoint f ⁻¹ᵁ projection f ⁻¹ᵁ (T i ⊓ T j),
      (closedPoint f).appLE (projection f ⁻¹ᵁ (T i ⊓ T j)) V hV
        (coefficientUnit f (T i ⊓ T j) (z i j)).val = 1 := by
    rintro V rfl hV
    exact congrArg Units.val (coefficientUnit_reduction f (T i ⊓ T j) (z i j))
  exact h _ (congrArg₂ (· ⊓ ·) (closedPoint_preimage_projection f (T i))
    (closedPoint_preimage_projection f (T j))) _

/-- The glued actual line bundle of an additive cocycle. -/
def cocycleBundle (hT : (⨆ i, T i) = ⊤) (z : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z) : LineBundle (thickening f) :=
  ⟨CocycleGluing.glued (unitCochain f T z),
    CocycleGluing.isLocallyFreeRankOne_glued (unitCochain f T z)
      ((projection f).iSup_preimage_eq_top hT) ((isCocycle_unitCochain_iff f T z).mpr hz)⟩

/-- Its actual zero-section pullback is trivial. -/
def cocycleBundleReductionIso (hT : (⨆ i, T i) = ⊤)
    (z : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z) :
    (Scheme.Modules.pullback (closedPoint f)).obj (cocycleBundle f T hT z hz).obj ≅
      structureModule X :=
  CocycleGluing.pullbackIso (closedPoint f) (unitCochain f T z)
      ((projection f).iSup_preimage_eq_top hT) ((isCocycle_unitCochain_iff f T z).mpr hz) ≪≫
    eqToIso (congrArg CocycleGluing.glued (pullbackCocycle_closedPoint_unitCochain f T z)) ≪≫
      CocycleGluing.gluedOneIso _
        ((closedPoint f).iSup_preimage_eq_top ((projection f).iSup_preimage_eq_top hT))

/-- Addition of coefficients multiplies the actual unit cochains. -/
lemma unitCochain_add (z w : ∀ i j, Γ(X, T i ⊓ T j)) :
    unitCochain f T (fun i j ↦ z i j + w i j) = unitCochain f T z * unitCochain f T w := by
  funext i j
  exact coefficientUnit_add f (T i ⊓ T j) (z i j) (w i j)

/-- The actual tensor product realizes addition of coefficient cocycles. -/
def cocycleBundleTensorIso (hT : (⨆ i, T i) = ⊤)
    (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T w) :
    tensorObj (cocycleBundle f T hT z hz).obj (cocycleBundle f T hT w hw).obj ≅
      CocycleGluing.glued (unitCochain f T (fun i j ↦ z i j + w i j)) :=
  CocycleGluing.tensorIso ((isCocycle_unitCochain_iff f T z).mpr hz)
      ((isCocycle_unitCochain_iff f T w).mpr hw)
      ((projection f).iSup_preimage_eq_top hT) ≪≫
    eqToIso (congrArg CocycleGluing.glued (unitCochain_add f T z w).symm)

/-- On actual line-bundle isomorphism classes the coefficient addition law is tensor product. -/
lemma isoClass_cocycleBundle_add
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (hT : (⨆ i, T i) = ⊤) (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T w)
    (hzw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T (fun i j ↦ z i j + w i j)) :
    LineBundle.isoClass preservation (cocycleBundle f T hT _ hzw) =
      LineBundle.isoClass preservation (cocycleBundle f T hT z hz) *
        LineBundle.isoClass preservation (cocycleBundle f T hT w hw) :=
  LineBundle.isoClass_eq_of_iso
    (ObjectProperty.isoMk _ (cocycleBundleTensorIso f T hT z w hz hw).symm)

/-- Two cocycles give the same actual line-bundle class exactly when their difference is
an additive coboundary. -/
lemma isoClass_cocycleBundle_eq_iff
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (hT : (⨆ i, T i) = ⊤) (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T w) :
    LineBundle.isoClass preservation (cocycleBundle f T hT z hz) =
        LineBundle.isoClass preservation (cocycleBundle f T hT w hw) ↔
      Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCoboundary
        (G := structureSheaf X) T (fun i j ↦ w i j - z i j) := by
  rw [LineBundle.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact (nonempty_iso_unitCochain_iff f T z w hz hw).mp
      ⟨(LineBundle.forget _).mapIso e⟩
  · intro h
    obtain ⟨e⟩ := (nonempty_iso_unitCochain_iff f T z w hz hw).mpr h
    exact ⟨ObjectProperty.isoMk _ e⟩

end DualNumberThickening

end Langlands.AlgebraicGeometry.Picard
