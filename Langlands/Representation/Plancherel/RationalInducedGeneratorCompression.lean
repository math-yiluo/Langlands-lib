import Langlands.Representation.Plancherel.RationalInducedGeneratorComparison
import Langlands.Representation.Plancherel.UnramifiedRationalDynamicCompression
import Langlands.Representation.Jacquet.StableCompressionPropagation

/-! Dynamic compression on the actual norm-kernel induced generator. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.Plancherel.RationalNormalized

private theorem stablePower_of_representationEquiv
    {H X Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ H X} {σ : Representation ℂ H Y}
    (e : ρ.Equiv σ) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : H) (b : ℕ)
    (hb : Stable (Jacquet.compressedAction σ hσ K hK g ^ b)) :
    Stable (Jacquet.compressedAction ρ hρ K hK g ^ b) := by
  apply stable_of_equiv (Langlands.fixedVectorsEquiv e.symm K.toSubgroup) _ _ ?_ hb
  apply LinearMap.ext
  intro v
  exact Jacquet.compressedAction_pow_natural σ ρ hσ hρ K hK g
    e.symm.toIntertwiningMap b v

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance generatorCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance generatorCompressionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance generatorCompressionLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X
local instance generatorCompressionFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

attribute [local instance] compactTensorAddCommGroup compactInducedAddCommGroup
  compactInducedModule compactInducedSMul compactInducedMulAction
  compactInducedComplexModule compactInducedComplexSMul compactInducedScalarTower
  compactInducedSMulCommClass compactInducedCompatible compactFixedModule

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

/-- Native output-Jacquet finiteness gives eventual stability of the universal
action itself, before any specialization of its coefficients. -/
theorem inducedCompressedAction_eventuallyStable_of_dynamic_jacquet_finite
    (πL : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hπ : πL.IsAdmissible)
    (hJac : UniversalInducedJacquetFiniteness r h hU πL.representation)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g : rationalPoints G)
    (hc : Jacquet.IsIwahoriContraction K
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
    (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m) :
    EventuallyStable
      (Jacquet.compressedAction (inducedComplexRepresentation r h hU πL)
        (isSmooth_inducedComplexRepresentation r h hU πL) K hK g) := by
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hCompact
  have hIndK := (universalInducedCoefficientFiniteness F G hG A M P U p l a n r hn
    h hU hr πL hπ).2 K hK |>.1
  have hJacK :=
    hJac ξ (outputLeviCompactOpen ξ K) (isCompact_outputLeviCompactOpen ξ K hK)
  exact @inducedCompressedAction_eventuallyStable_of_native_finite
    F _ _ _ _ A G M P U _ _ p l a r _ _ n h hU πL _ _ _
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints ξ)
    (Aubert.General.dynamic_isSemidirectDecomposition ξ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).levi_le_normalizer
    (isClosed_outputLeviPoints ξ) K hK g hc hcentral hIndK hJacK

variable [LocallyOfFiniteType M.X.hom]
  (π : SmoothRep.{0, u, uV} ℂ (rationalPoints M))

local instance generatorCompressionLeviTopologicalGroup :
    IsTopologicalGroup (rationalPoints M) := rationalPoint_isTopologicalGroup F M

/-- The actual generator comparison restricted to fixed vectors, retaining
the full native universal induced carrier on its target. -/
def rationalNormKernelCompressedFixedEquiv (K : Subgroup (rationalPoints G)) :
    fixedVectors
      (((Aubert.General.rationalInertiaInductionFunctor M h hU
        (parabolicLeviPointHomeomorph r).symm).obj
          (CuspidalSupport.rationalNormKernelCompactInduction M π)).representation) K ≃ₗ[ℂ]
      fixedVectors (inducedComplexRepresentation r h hU (literalLeviRep r π)) K :=
  Langlands.fixedVectorsEquiv (rationalNormKernelInducedEquiv r π h hU) K

/-- The exact inertia-induction functor image of the norm-kernel generator is
eventually stable, under the native output-Jacquet finiteness premise. -/
theorem rationalNormKernelInducedCompressedAction_eventuallyStable
    (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hπ : π.IsAdmissible)
    (hJac : UniversalInducedJacquetFiniteness r h hU (literalLeviRep r π).representation)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g : rationalPoints G)
    (hc : Jacquet.IsIwahoriContraction K
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
    (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m) :
    EventuallyStable
      (Jacquet.compressedAction
        (((Aubert.General.rationalInertiaInductionFunctor M h hU
          (parabolicLeviPointHomeomorph r).symm).obj
            (CuspidalSupport.rationalNormKernelCompactInduction M π)).representation)
        (((Aubert.General.rationalInertiaInductionFunctor M h hU
          (parabolicLeviPointHomeomorph r).symm).obj
            (CuspidalSupport.rationalNormKernelCompactInduction M π)).isSmooth) K hK g) := by
  have hπL : (literalLeviRep r π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv π.representation
      (parabolicLeviPointHomeomorph r).symm hπ
  obtain ⟨b, hb, hpower⟩ :=
    inducedCompressedAction_eventuallyStable_of_dynamic_jacquet_finite r h hU
      (literalLeviRep r π) hG hn hr hCompact hπL hJac ξ K hK g hc hcentral
  refine ⟨b, hb, ?_⟩
  exact stablePower_of_representationEquiv (rationalNormKernelInducedEquiv r π h hU)
    _ (isSmooth_inducedComplexRepresentation r h hU (literalLeviRep r π)) K hK g b hpower

end Langlands.Plancherel.RationalNormalized
