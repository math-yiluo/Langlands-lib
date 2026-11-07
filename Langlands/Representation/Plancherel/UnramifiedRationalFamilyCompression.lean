import Langlands.Representation.Plancherel.UnramifiedRationalCompactSpecialization
import Langlands.Representation.Plancherel.UnramifiedCompressionCriterion
import Langlands.Representation.Plancherel.UnramifiedRationalCoefficientAlgebra

/-! Compression stability for the actual universal rational induced family. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance familyAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance familyPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

attribute [local instance] compactTensorAddCommGroup compactInducedAddCommGroup
  compactInducedModule compactInducedSMul compactInducedMulAction
  compactInducedComplexModule compactInducedComplexSMul compactInducedScalarTower
  compactInducedSMulCommClass compactInducedCompatible compactFixedModule

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))

local instance familyNativeFixedModule (H : Subgroup (rationalPoints G)) :
    Module (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) H) :=
  Submodule.module _

variable
  {N L Nbar : Subgroup (rationalPoints G)}
  (hN : IsClosed (N : Set (rationalPoints G)))
  (hLN : L ≤ Subgroup.normalizer N) (hL : IsClosed (L : Set (rationalPoints G)))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  {g : rationalPoints G}
  (hc : Jacquet.IsIwahoriContraction K N L Nbar g)
  (hcentral : ∀ m ∈ L, m * g = g * m)

include hL hc hcentral in
/-- The two native finite fixed modules give stability of the actual universal
compression, with Noetherianity supplied by its complete regular algebra. -/
theorem inducedCompressedAction_eventuallyStable_of_native_finite
    [Module.Finite (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) K.toSubgroup)]
    [Module.Finite (RegularAlgebra r)
      (fixedVectors
        (UnramifiedNormalized.jacquetRepresentation (parabolicLeviRationalNormCharacters r)
          (inducedRepresentation r h hU π.representation) N L hN hLN)
        (K.toSubgroup.comap L.subtype))] :
    LinearAlgebra.StableEndomorphism.EventuallyStable
      (Jacquet.compressedAction (inducedComplexRepresentation r h hU π)
        (isSmooth_inducedComplexRepresentation r h hU π) K hK g) := by
  let := regularAlgebra_isNoetherianRing r
  exact UnramifiedNormalized.compressedAction_eventuallyStable_of_normalized_finite
    (parabolicLeviRationalNormCharacters r) (inducedRepresentation r h hU π.representation)
    (isSmooth_inducedRepresentation r h hU π.representation) hN hLN hL K hK hc hcentral

include hL hc hcentral in
/-- One positive universal exponent is chosen before every unramified character.
Each genuine specialization transfers that same exponent. -/
theorem complexInducedCompressedAction_uniform_of_native_finite
    [Module.Finite (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) K.toSubgroup)]
    [Module.Finite (RegularAlgebra r)
      (fixedVectors
        (UnramifiedNormalized.jacquetRepresentation (parabolicLeviRationalNormCharacters r)
          (inducedRepresentation r h hU π.representation) N L hN hLN)
        (K.toSubgroup.comap L.subtype))]
    (hbij : ∀ χ, InducedSpecializationBijective r h hU π χ) :
    ∃ b : ℕ, 0 < b ∧
      ∀ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r),
        LinearAlgebra.StableEndomorphism.Stable
          (Jacquet.compressedAction (complexInduced r h hU π χ).representation
            (complexInduced r h hU π χ).isSmooth K hK g ^ b) := by
  obtain ⟨b, hb, hstable⟩ :=
    inducedCompressedAction_eventuallyStable_of_native_finite r h hU π
      hN hLN hL K hK hc hcentral
  exact ⟨b, hb, fun χ =>
    inducedCompressedAction_stablePower r h hU π χ K hK (hbij χ) g b hstable⟩

end Langlands.Plancherel.RationalNormalized
