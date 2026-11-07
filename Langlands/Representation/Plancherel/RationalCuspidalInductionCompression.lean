import Langlands.Representation.Plancherel.RationalInducedGeneratorCompression
import Langlands.Representation.CuspidalSupport.RationalCuspidalCompression
import Langlands.Representation.CuspidalSupport.RationalCuspidalSubquotients

/-! # Actual cuspidal induction compression from native generator finiteness -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.Plancherel.RationalNormalized

open Aubert.General Aubert.General.RationalPointFamily CuspidalSupport

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance cuspidalInductionCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance cuspidalInductionCompressionAmbientTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance cuspidalInductionCompressionLeviTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance cuspidalInductionCompressionFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
  {n : U ⟶ P}
  (h : IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ M) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hL : ∀ J, IsSemidirectDecomposition
    (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hUL : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints M)))

/-- The two retained native coefficient inputs for every irreducible
cuspidal representative of the actual rational inducing Levi. -/
def RationalCuspidalNativeJacquetInputs : Prop :=
  ∀ π : SmoothRep.{0, u, max u uV} ℂ (rationalPoints M),
    π.IsIrreducible →
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL π →
    π.IsAdmissible ∧
      UniversalInducedJacquetFiniteness r h hU (literalLeviRep r π).representation

/-- Actual whole-cuspidal decomposition and native irreducible generator
finiteness give compression stability for induction of every cuspidal object. -/
theorem rationalCuspidalInduction_eventuallyStable_of_nativeJacquet
    (hStandard : StandardCocharacterStatement.{u}) (hRed : IsConnectedReductive M)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hdecomp : IsRationalCuspidalInertiaProductDecomposition.{u, max u uV}
      M i ν hL hUL)
    (hfinite : ∀ Q : OpenSubgroup (rationalPoints M),
      IsCompact (Q : Set (rationalPoints M)) →
      Set.Finite {c : RationalIrreducibleInertiaClass.{u, max u uV} M |
        ∃ (D : SmoothRep.{0, u, max u uV} ℂ (rationalPoints M))
          (hD : D.IsIrreducible),
          IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL D ∧
          rationalIrreducibleInertiaClass M D hD = c ∧
          Nontrivial (fixedVectors D.representation Q.toSubgroup)})
    (hgen : ∀ π : SmoothRep.{0, u, max u uV} ℂ (rationalPoints M),
      π.IsIrreducible →
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL π →
      IsRationalNormKernelSmallProgenerator M π)
    (hNative : RationalCuspidalNativeJacquetInputs.{u, uV} r h hU i ν hL hUL)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g : rationalPoints G)
    (hc : Jacquet.IsIwahoriContraction K
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
    (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m)
    (E : SmoothRep.{0, u, max u uV} ℂ (rationalPoints M))
    (hE : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL E) :
    EventuallyStable (Jacquet.compressedAction
      (((rationalInertiaInductionFunctor M h hU
        (parabolicLeviPointHomeomorph r).symm).obj E).representation)
      (((rationalInertiaInductionFunctor M h hU
        (parabolicLeviPointHomeomorph r).symm).obj E).isSmooth) K hK g) := by
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hCompact
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hp
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hp
  have hs : RationalCuspidalGeneratorImageEventuallyStable.{u, uV}
      M i ν hL hUL h hU (parabolicLeviPointHomeomorph r).symm K hK g := by
    intro π hπ hcπ
    obtain ⟨ha, hj⟩ := hNative π hπ hcπ
    exact rationalNormKernelInducedCompressedAction_eventuallyStable
      r h hU π hG hn hr hCompact ha hj ξ K hK g hc hcentral
  exact rationalAllCuspidalInduction_eventuallyStable_of_generators
    M i ν hL hUL h hU (parabolicLeviPointHomeomorph r).symm K hK g
    hStandard hRed hi hν (compactOpenCofinal_of_nonarchimedean (rationalPoints G))
    hP hr (isClosed_parabolicLeviPointSubgroup r) hdecomp hfinite hgen hs E
    ((rationalAllCuspidalSubquotientProperty_iff_isCuspidal
      M i ν hStandard hRed hi hν hL hUL E).mpr hE)

end Langlands.Plancherel.RationalNormalized
