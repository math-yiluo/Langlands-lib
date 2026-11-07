import Langlands.Representation.Plancherel.RationalDynamicSourceHaar
import Langlands.Representation.Plancherel.UnramifiedRationalFamilyCompression
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetFinitenessStatement
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFinitenessProof
import Langlands.Representation.Plancherel.RationalNormalizedInducedSpecializationProof
import Langlands.Representation.Aubert.General.DynamicLeviTopology

/-! Uniform compression of actual rational induced families at dynamic parabolics. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance dynamicCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance dynamicCompressionPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance dynamicCompressionFieldT2 : T2Space F := BruhatTits.localField_t2Space F

/-- The literal compact-open intersection with the output dynamic Levi,
regarded as an open subgroup of that Levi. -/
def outputLeviCompactOpen
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) : OpenSubgroup (outputLeviPoints ξ) :=
  K.comap (outputLeviPoints ξ).subtype continuous_subtype_val

/-- The actual dynamic centralizer point subgroup is closed. -/
theorem isClosed_outputLeviPoints
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    IsClosed (outputLeviPoints ξ : Set (rationalPoints G)) :=
  RationalDynamicSource.isClosed_levi ξ

/-- The compactness of the ambient open subgroup pulls back through the
closed embedding of the literal output Levi. -/
theorem isCompact_outputLeviCompactOpen
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    IsCompact (outputLeviCompactOpen ξ K : Set (outputLeviPoints ξ)) :=
  (isClosed_outputLeviPoints ξ).isClosedEmbedding_subtypeVal.isCompact_preimage hK

variable
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M P U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))

/-- The native output-Jacquet finiteness conclusion gives a single positive
compression exponent for all unramified specializations. Induced finiteness and
full actual specialization are supplied by their published proofs. -/
theorem complexInducedCompressedAction_uniform_of_dynamic_jacquet_finite
    (hG : IsConnectedReductive G)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hπ : π.IsAdmissible)
    (hJac : UniversalInducedJacquetFiniteness r h hU π.representation)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g : rationalPoints G)
    (hc : Jacquet.IsIwahoriContraction K
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
    (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m) :
    ∃ b : ℕ, 0 < b ∧
      ∀ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r),
        LinearAlgebra.StableEndomorphism.Stable
          (Jacquet.compressedAction (complexInduced r h hU π χ).representation
            (complexInduced r h hU π χ).isSmooth K hK g ^ b) := by
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hCompact
  have hIndK := (universalInducedCoefficientFiniteness F G hG A M P U p l a n r hn
    h hU hr π hπ).2 K hK |>.1
  have hJacK :=
    hJac ξ (outputLeviCompactOpen ξ K) (isCompact_outputLeviCompactOpen ξ K hK)
  refine @complexInducedCompressedAction_uniform_of_native_finite
    F _ _ _ _ A G M P U _ _ p l a r _ _ n h hU π _ _ _
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints ξ)
    (Aubert.General.dynamic_isSemidirectDecomposition ξ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).levi_le_normalizer
    (isClosed_outputLeviPoints ξ) K hK g hc hcentral hIndK hJacK ?_
  intro χ
  exact rationalNormalizedInducedSpecialization F G hG M P U A p l a r n h hU
    hr hCompact π χ

end Langlands.Plancherel.RationalNormalized
