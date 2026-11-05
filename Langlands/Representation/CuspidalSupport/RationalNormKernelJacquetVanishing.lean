import Langlands.Representation.CuspidalSupport.RationalNormKernelEscapingBasis
import Langlands.Representation.Jacquet.OpenSubgroupIwahoriTransport
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.Representation.Aubert.General.StandardFamilyStructure

/-! # Compact coefficients and actual norm-kernel Jacquet vanishing -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

section KernelGroups

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

/-- The actual intersection of a standard unipotent subgroup with the common
rational norm kernel, as a subgroup of that kernel. -/
def normKernelUnipotent : Subgroup (Plancherel.rationalCommonNormKernel G) :=
  (unipotent i ν I).comap (Plancherel.rationalCommonNormKernel G).subtype

/-- The actual intersection of a standard Levi subgroup with the common
rational norm kernel, as a subgroup of that kernel. -/
def normKernelLevi : Subgroup (Plancherel.rationalCommonNormKernel G) :=
  (levi i ν I).comap (Plancherel.rationalCommonNormKernel G).subtype

theorem normKernelLevi_le_normalizer :
    normKernelLevi i ν I ≤ Subgroup.normalizer (normKernelUnipotent i ν I) :=
  Jacquet.normalizer_comap_subtype _ _ _ (levi_le_normalizer i ν I)

end KernelGroups

section Data

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)}

local instance : TopologicalSpace (RationalPoint F G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)]
    (d : NormKernelEscapingOppositeIwahoriData i ν I)

/-- The specified ambient basis in the escaping data restricts to the actual
norm kernel, using its proved openness in the canonical topology. -/
theorem NormKernelEscapingOppositeIwahoriData.kernel_basis :
    Jacquet.HasOppositeIwahoriContractionBasis (normKernelUnipotent i ν I)
      (normKernelLevi i ν I)
      ((oppositeUnipotent i d.cocharacter).comap
        (Plancherel.rationalCommonNormKernel G).subtype) d.element := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact d.basis.comap_open (Plancherel.rationalCommonNormKernel G)
    (Plancherel.isOpen_rationalCommonNormKernelConditional G) d.element

include d in
/-- Compact smooth-dual coefficients on the actual norm kernel force the
coinvariants of the actual intersected standard radical to vanish. -/
theorem NormKernelEscapingOppositeIwahoriData.subsingleton_coinvariants
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Plancherel.rationalCommonNormKernel G) V)
    (hρ : IsSmooth ρ) (hc : HasCompactSmoothDualCoefficients ρ) :
    Subsingleton (Jacquet.Coinvariants ρ (normKernelUnipotent i ν I)) :=
  Jacquet.subsingleton_coinvariants_of_compact_escaping_basis ρ hρ hc
    (normKernelUnipotent i ν I) (normKernelLevi i ν I)
    ((oppositeUnipotent i d.cocharacter).comap
      (Plancherel.rationalCommonNormKernel G).subtype)
    (normKernelLevi_le_normalizer i ν I) d.element d.kernel_basis d.escapes

end Data

/-- Every proper actual standard root subset has zero Jacquet coinvariants
in every smooth compact-coefficient representation of the actual norm kernel.
The representation carrier has an independent universe. -/
theorem subsingleton_normKernel_coinvariants_of_compact
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint F G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{uF}) (_hRoots : HasRelativeRootSystem i)
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (_hproper : ∃ α ∈ simpleRelativeRoots i ν, α ∉ rootSet i ν I)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Plancherel.rationalCommonNormKernel G) V)
      (_hρ : IsSmooth ρ) (_hc : HasCompactSmoothDualCoefficients ρ),
      Subsingleton (Jacquet.Coinvariants ρ (normKernelUnipotent i ν I)) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots I hU hproper V _ _ ρ hρ hc
  obtain ⟨d⟩ := nonempty_normKernelEscapingOppositeIwahoriData
    F G hG T i hi ν hν hStandard hRoots I hU hproper
  exact d.subsingleton_coinvariants ρ hρ hc

end Langlands.Aubert.General.RationalPointFamily
