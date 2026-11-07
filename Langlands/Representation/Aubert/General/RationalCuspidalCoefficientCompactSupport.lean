import Langlands.Representation.Aubert.General.RationalCuspidalCartanBound
import Langlands.Representation.Aubert.General.RationalCartanCentralSupport
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Cuspidal coefficient norms on the full central quotient -/

noncomputable section

universe u v

namespace Langlands

/-- Every coefficient norm associated with a unitary central character and a
smooth dual functional has compact support on the quotient by the full center. -/
def HasCompactUnitaryCoefficientsModCenter
    {G : Type u} [Group G] [TopologicalSpace G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∀ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ) (w : V),
    HasCompactSupport (c.coefficientNorm ℓ.1 w)

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice S)

local instance rationalCuspidalCoefficientCompactSupportPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]

/-- Proper-standard cuspidality and the stated actual Cartan and simultaneous
basis data give compact coefficient norms on the full central quotient. -/
theorem compactUnitaryCoefficients_centerQuotient_of_isCuspidal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (K0 : Subgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : FiniteCartanCovering F i ν K0) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    let h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν
    ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
      HasCompactUnitaryCoefficientsModCenter A.representation := by
  have := hG.smooth
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  dsimp only
  intro A hA c ℓ w
  apply hasCompactSupport_centerQuotient_of_finiteCartanCovering i ν
    hG hi hν hRoots K0 hK0 hcover (c.coefficientNorm ℓ.1 w)
  intro F₀
  let Fset : Set (rationalPoints G) := Subtype.val '' (F₀ : Set (centralizerPoints i))
  have hfinite : Fset.Finite := F₀.finite_toSet.image _
  have hcentral : Fset ⊆ centralizerPoints i := by
    rintro _ ⟨f, _, rfl⟩
    exact f.property
  obtain ⟨B, hB⟩ := exists_rational_compact_translate_pairing_bound i ν hG hi hν hStandard
    hRoots hU hbasis hfinite hcentral (K0 : Set (rationalPoints G)) hK0 A hA ℓ.1 ℓ.2 w
  refine ⟨B, fun k₁ k₂ f x hk₁ hk₂ hf hx hnonzero => ?_⟩
  apply hB k₁ hk₁ k₂ hk₂ x hx f ⟨f, hf, rfl⟩
  simpa only [UnitaryCentralCharacter.coefficientNorm_mk, norm_ne_zero_iff] using hnonzero

end Langlands.Aubert.General
