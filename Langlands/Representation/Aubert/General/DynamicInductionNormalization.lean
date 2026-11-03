import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Langlands.Representation.Twist.PullbackProof
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof

/-! # Full-parabolic and Levi-inflated dynamic induction normalization -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General.DynamicNormalization

section GeneralGroup

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H}

/-- Induction after twisting the Levi by its half modulus and inflating the
resulting representation along the actual Levi projection. -/
def leviTwistedInductionFunctor (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set H)) :
    SmoothRep.{0, u, uV} ℂ M ⥤ SmoothRep.{0, u, max u uV} ℂ H :=
  SmoothRep.twistFunctor
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer)
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU M h.levi_le_normalizer) ⋙
    inflationFunctor h ⋙ Induction.smoothInductionFunctor P

/-- On a unimodular radical, twisting on the full parabolic or first twisting
on the Levi gives naturally isomorphic actual induced representations. -/
def normalizedInductionLeviTwistIso (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set H)) (hδ : IsUnimodularModulus U hU) :
    normalizedInductionFunctor.{u, uV} h hU ≅ leviTwistedInductionFunctor h hU := by
  refine NatIso.ofComponents (fun A =>
    (Induction.smoothInductionFunctor P).mapIso
      (Rep.mkIso (equivOfRepresentationEq ?_))) ?_
  · change Langlands.twist _ (A.representation.comp h.projection) =
      (Langlands.twist _ A.representation).comp h.projection
    rw [Langlands.twist_comp, inductionCharacter_toMonoidHom,
      closedHalfCharacter_eq_comp_projection h hU hδ]
  · intro A B f
    ext v
    rfl

end GeneralGroup

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The actual dynamic radical is unimodular at precisely the topology and
typing hypotheses of the final induction target. -/
theorem dynamicUnipotent_isUnimodular :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Set (RationalPoint F G.X))),
      IsUnimodularModulus
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  intro _ _ hU
  exact isUnimodularModulus_of_isLimitOfCompactSubgroups _ hU
    (BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG χ)

/-- The actual full-parabolic half character equals the Levi half character
inflated along the dynamic projection, without an added unimodularity premise. -/
theorem dynamicClosedHalfCharacter_eq_comp_projection :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    let h := dynamic_isSemidirectDecomposition χ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Set (RationalPoint F G.X))),
      HaarModulus.closedHalfCharacter _ hU _ h.le_normalizer =
        (HaarModulus.closedHalfCharacter _ hU _ h.levi_le_normalizer).comp
          h.projection := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  dsimp only
  intro _ _ hU
  exact closedHalfCharacter_eq_comp_projection _ hU
    (dynamicUnipotent_isUnimodular F G hG χ hU)

/-- The normalization comparison for every actual dynamic parabolic, with
unimodularity discharged by compact containment of its radical. -/
def dynamicNormalizedInductionLeviTwistIso :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    let h := dynamic_isSemidirectDecomposition χ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Set (RationalPoint F G.X))),
      normalizedInductionFunctor.{u, uV} h hU ≅ leviTwistedInductionFunctor h hU := by
  haveI := hG.isAffineHom
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  dsimp only
  intro _ _ hU
  exact normalizedInductionLeviTwistIso _ hU
    (dynamicUnipotent_isUnimodular F G hG χ hU)

end Langlands.Aubert.General.DynamicNormalization
