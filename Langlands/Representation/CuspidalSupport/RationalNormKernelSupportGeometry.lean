import Langlands.Representation.CuspidalSupport.RationalNormKernelSupportSandwich
import Langlands.Representation.CuspidalSupport.RationalNormKernelCartanCover
import Langlands.Representation.CuspidalSupport.RationalNormKernelUniformSupportStatement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Representation.Aubert.General.StandardFamilyStructure

/-! # Uniform norm-kernel support from one joint special-compact geometry -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}

local instance normKernelSupportGeometryPointTopology :
    TopologicalSpace (RationalPoint F G.X) := pointTopology

/-- One geometric package for the support argument: corrected fundamental
generators, one compact ambient subgroup carrying a simultaneous standard basis,
and finite central Cartan charts for exactly that orthant and subgroup. -/
structure NormKernelUniformSupportGeometry (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)] where
  generators : NormKernelFundamentalCocharacters i ν
  compactSubgroup : Subgroup (RationalPoint F G.X)
  isCompact : IsCompact (compactSubgroup : Set (RationalPoint F G.X))
  basis : SimultaneousStandardBasisAt i ν compactSubgroup
  cover : NormKernelCentralCartanCover generators compactSubgroup

variable {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} [Fintype (SimpleRoot i ν)]

namespace NormKernelUniformSupportGeometry

/-- The joint special-compact witness at one special vertex supplies all three
pieces of the package with the same compact subgroup. -/
theorem nonempty_of_joint
    (hjoint : JointSpecialCompactBasisExistenceStatement.{uF})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{uF})
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i) :
    Nonempty (NormKernelUniformSupportGeometry i ν) := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨d⟩ := nonempty_normKernelFundamentalCocharacters hG hi hν hStandard hRoots
  obtain ⟨D, x, Z, j, s, -, -, hsj, h, -, hsc, -, -, -, -, hcompat, hbasis⟩ :=
    hjoint F G hG T i hi ν hν
  obtain ⟨F₀, hF₀⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  obtain ⟨R, hR, hcover⟩ :=
    d.exists_finite_centralCartanFactorization hG hi hν hStandard D x j s h hsj
      hcompat hF₀
  refine ⟨{ generators := d
            compactSubgroup := D.specialCompactSubgroup x
            isCompact := hsc.2.1.1
            basis := hbasis
            cover := { residual := R, finite := hR, cover := fun g => ?_ } }⟩
  obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hg⟩ := hcover g
  exact ⟨k₁, hk₁, k₂, hk₂, t, ht, n, z, hz, hg⟩

variable [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]

/-- The package gives one compact support at every prescribed open level of the
actual norm kernel. The kernel carries its Borel σ-algebra and Haar measure. -/
theorem hasUniformSupport (P : NormKernelUniformSupportGeometry i ν)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{uF})
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (U : OpenSubgroup (Plancherel.rationalCommonNormKernel G)) :
    CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport.{uF, uV}
      U.toSubgroup := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨L⟩ := nonempty_normKernelCompressionLevel hG hi hν hStandard hRoots
    P.generators P.compactSubgroup P.basis U
  let : MeasurableSpace (Plancherel.rationalCommonNormKernel G) := borel _
  have : BorelSpace (Plancherel.rationalCommonNormKernel G) := ⟨rfl⟩
  have : LocallyCompactSpace (Plancherel.rationalCommonNormKernel G) :=
    (Plancherel.isOpen_rationalCommonNormKernel G).locallyCompactSpace
  exact L.hasUniformSupport_of_centralCartanCover hG P.isCompact P.cover
    (Measure.haar (G := Plancherel.rationalCommonNormKernel G))

end NormKernelUniformSupportGeometry

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.CuspidalSupport

open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

/-- The joint special-compact basis existence statement implies the exact
uniform-support target, with an independent representation-carrier universe. -/
theorem rationalNormKernelUniformSupport_of_joint
    (hjoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}) :
    RationalNormKernelUniformSupportStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots _ K _
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : Finite (SimpleRoot i ν) := finite_simpleRoot hG hi ν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  obtain ⟨P⟩ := NormKernelUniformSupportGeometry.nonempty_of_joint hjoint hG hi hν
    hStandard hRoots
  exact P.hasUniformSupport hG hi hν hStandard hRoots K

end Langlands.CuspidalSupport
