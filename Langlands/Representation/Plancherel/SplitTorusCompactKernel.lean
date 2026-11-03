import Langlands.Representation.Plancherel.SplitTorusCompactUnits

/-! # Compact norm kernels of arbitrary actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The common norm kernel is preserved by every actual point map. -/
theorem map_mem_commonNormKernel (f : G ⟶ H) {a : rationalPoints G}
    (ha : a ∈ rationalCommonNormKernel G) :
    rationalPoints.map f a ∈ rationalCommonNormKernel H := by
  rw [mem_rationalCommonNormKernel_iff_valuation] at ha ⊢
  intro χ
  rw [← rationalCharacterValuation_characterRestrict f χ a]
  exact ha (characterRestrict f χ)

variable [IsAffine G.X.left] [IsAffine H.X.left]

/-- An actual group-scheme isomorphism is a homeomorphism on canonical points. -/
def isoPointsHomeomorph (e : G ≅ H) :
    letI := rationalPointTopology F G.X
    letI := rationalPointTopology F H.X
    rationalPoints G ≃ₜ rationalPoints H := by
  letI := rationalPointTopology F G.X
  letI := rationalPointTopology F H.X
  exact
    { toEquiv := (isoPointsEquiv e (Over.mk (𝟙 (Spec (CommRingCat.of F))))).toEquiv
      continuous_toFun := continuous_rationalPointMap F e.hom.hom.hom
      continuous_invFun := continuous_rationalPointMap F e.inv.hom.hom }

theorem commonNormKernel_eq_preimage_iso (e : G ≅ H) :
    (rationalCommonNormKernel G : Set (rationalPoints G)) =
      isoPointsHomeomorph e ⁻¹'
        (rationalCommonNormKernel H : Set (rationalPoints H)) := by
  ext a
  constructor
  · exact map_mem_commonNormKernel e.hom
  · intro ha
    have hk := map_mem_commonNormKernel e.inv ha
    change (isoPointsEquiv e _).symm ((isoPointsEquiv e _) a) ∈
      rationalCommonNormKernel G at hk
    change a ∈ rationalCommonNormKernel G
    simpa only [MulEquiv.symm_apply_apply] using hk

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]

/-- Compactness uses a splitting only in its proof; the subgroup is intrinsic. -/
theorem isCompact_commonNormKernel (hA : IsSplitTorus A.toGrp) :
    letI := rationalPointTopology F A.X
    IsCompact (rationalCommonNormKernel A.toGrp : Set (rationalPoints A.toGrp)) := by
  let := rationalPointTopology F A.X
  obtain ⟨I, hI, ⟨e⟩⟩ := hA
  let := Fintype.ofFinite I
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of F)) I).X.hom :=
    isAffineHom_splitTorus _ _
  let : IsAffine (splitTorus (Spec (CommRingCat.of F)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of F)) I).X.hom
  let := rationalPointTopology F (splitTorus (Spec (CommRingCat.of F)) I).X
  rw [commonNormKernel_eq_preimage_iso e]
  exact (isoPointsHomeomorph e).isCompact_preimage.mpr
    (isCompact_splitCommonNormKernel F I)

/-- Every smooth character has norm one on the actual split torus's norm kernel. -/
theorem norm_eq_one_on_commonNormKernel (hA : IsSplitTorus A.toGrp) :
    letI := rationalPointTopology F A.X
    ∀ (χ : rationalPoints A.toGrp →* ℂˣ),
      IsOpen (χ.ker : Set (rationalPoints A.toGrp)) →
      ∀ {a : rationalPoints A.toGrp}, a ∈ rationalCommonNormKernel A.toGrp →
        ‖(χ a : ℂ)‖ = 1 := by
  let := rationalPointTopology F A.X
  let : Smooth A.X.hom := hA.smooth
  let : IsTopologicalGroup (rationalPoints A.toGrp) :=
    rationalPoint_isTopologicalGroup F A.toGrp
  intro χ hχ a ha
  exact norm_eq_one_on_compact_subgroup χ hχ (rationalCommonNormKernel A.toGrp)
    (isCompact_commonNormKernel hA) ha

end Langlands.Plancherel.SplitTorus
