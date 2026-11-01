import Langlands.AlgebraicGeometry.Picard.DualNumberAffineFrames
import Langlands.AlgebraicGeometry.Picard.DualNumberCocycles
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame

/-! # Exhaustive normalized-cocycle presentation of actual deformations -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Recover any actual unit reducing to one from its first-order coefficient. -/
lemma coefficientUnit_unitCoefficient_of_reduction_eq_one (U : X.Opens)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)ˣ) (ha : unitReduction f U a = 1) :
    coefficientUnit f U (unitCoefficient f U a).toAdd = a := by
  change ((unitKernelEquiv f U) ((unitKernelEquiv f U).symm (normalizeUnit f U a))).val = a
  rw [MulEquiv.apply_symm_apply]
  change a * (liftUnit f U (unitReduction f U a))⁻¹ = a
  rw [ha, map_one, inv_one, mul_one]

variable {ι : Type u} (T : ι → X.Opens) (M : (thickening f).Modules)
  (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
  (s : ∀ i, Γ(M, thickenedOpens f T i))

/-- Transitions between sections normalized by an actual reduction trivialization reduce to one. -/
lemma unitReduction_eq_one_of_normalized_transition
    (hn : ∀ i, reducedCoefficient f (T i) M e (s i) = 1)
    (g : ∀ i j, Γ(thickening f, thickenedOpens f T i ⊓ thickenedOpens f T j)ˣ)
    (hg : CocycleGluing.IsTransition s g) (i j : ι) :
    unitReduction f (T i ⊓ T j) (g i j) = 1 := by
  apply Units.ext
  let a : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))ˣ := g i j
  have h := congrArg (reducedCoefficient f (T i ⊓ T j) M e) (hg i j)
  change reducedCoefficient f (T i ⊓ T j) M e
      (M.presheaf.map ((Opens.map (projection f).base).map
        (homOfLE (inf_le_right : T i ⊓ T j ≤ T j))).op (s j)) =
    reducedCoefficient f (T i ⊓ T j) M e
      ((a : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) •
        M.presheaf.map ((Opens.map (projection f).base).map
          (homOfLE (inf_le_left : T i ⊓ T j ≤ T i))).op (s i)) at h
  rw [reducedCoefficient_smul, reducedCoefficient_naturality,
    reducedCoefficient_naturality, hn i, hn j, map_one, map_one, mul_one] at h
  exact h.symm

/-- The additive coefficient cochain extracted from the actual frame transitions. -/
def frameCoefficientCochain
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (thickenedOpens f T i))
    (i j : ι) : Γ(X, T i ⊓ T j) :=
  (unitCoefficient f (T i ⊓ T j) (CocycleGluing.frameCocycle s hs i j)).toAdd

/-- The actual transitions of normalized frames are exactly their coefficient units. -/
lemma unitCochain_frameCoefficientCochain
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (thickenedOpens f T i))
    (hn : ∀ i, reducedCoefficient f (T i) M e (s i) = 1) :
    unitCochain f T (frameCoefficientCochain f T M s hs) =
      CocycleGluing.frameCocycle s hs := by
  funext i j
  exact coefficientUnit_unitCoefficient_of_reduction_eq_one f (T i ⊓ T j) _
    (unitReduction_eq_one_of_normalized_transition f T M e s hn _
      (CocycleGluing.isTransition_frameCocycle hs) i j)

/-- The coefficients of the actual normalized frame transitions form an additive cocycle. -/
lemma isCocycle_frameCoefficientCochain
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (thickenedOpens f T i))
    (hn : ∀ i, reducedCoefficient f (T i) M e (s i) = 1) :
    CechDegreeOne.IsCocycle (G := structureSheaf X) T
      (frameCoefficientCochain f T M s hs) := by
  apply (isCocycle_unitCochain_iff f T _).mp
  rw [unitCochain_frameCoefficientCochain f T M e s hs hn]
  exact CocycleGluing.isCocycle_of_isTransition hs
    (CocycleGluing.isTransition_frameCocycle hs)

/-- Reconstruct the actual sheaf from its normalized additive transition cocycle. -/
def normalizedFrameIso
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (thickenedOpens f T i))
    (hn : ∀ i, reducedCoefficient f (T i) M e (s i) = 1)
    (hT : (⨆ i, T i) = ⊤) :
    M ≅ CocycleGluing.glued (unitCochain f T (frameCoefficientCochain f T M s hs)) :=
  CocycleGluing.frameIso hs
    (by rw [unitCochain_frameCoefficientCochain f T M e s hs hn]
        exact CocycleGluing.isTransition_frameCocycle hs)
    ((projection f).iSup_preimage_eq_top hT)

/-- Every actual zero-section-trivial line bundle has a normalized additive-cocycle
presentation on any prescribed affine cover. -/
lemma exists_cocycle_presentation (hT : (⨆ i, T i) = ⊤)
    (haff : ∀ i, IsAffineOpen (T i)) (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    ∃ z : ∀ i j, Γ(X, T i ⊓ T j),
      CechDegreeOne.IsCocycle (G := structureSheaf X) T z ∧
        Nonempty (L.obj ≅ CocycleGluing.glued (unitCochain f T z)) := by
  let s := fun i ↦ affineNormalizedFrame f (T i) (haff i) L e
  have hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (thickenedOpens f T i) :=
    fun i ↦ affineNormalizedFrame_isFrame f (T i) (haff i) L e
  have hn : ∀ i, reducedCoefficient f (T i) L.obj e (s i) = 1 :=
    fun i ↦ reducedCoefficient_affineNormalizedFrame f (T i) (haff i) L e
  exact ⟨frameCoefficientCochain f T L.obj s hs,
    isCocycle_frameCoefficientCochain f T L.obj e s hs hn,
    ⟨normalizedFrameIso f T L.obj e s hs hn hT⟩⟩

/-- Two normalized additive cocycle presentations of the same actual sheaf differ by
an additive coboundary, regardless of the chosen reduction trivializations or frames. -/
lemma isCoboundary_of_presentations
    (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : CechDegreeOne.IsCocycle (G := structureSheaf X) T z)
    (hw : CechDegreeOne.IsCocycle (G := structureSheaf X) T w)
    (ez : M ≅ CocycleGluing.glued (unitCochain f T z))
    (ew : M ≅ CocycleGluing.glued (unitCochain f T w)) :
    CechDegreeOne.IsCoboundary (G := structureSheaf X) T (fun i j ↦ w i j - z i j) :=
  (nonempty_iso_unitCochain_iff f T z w hz hw).mp ⟨ez.symm ≪≫ ew⟩

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
