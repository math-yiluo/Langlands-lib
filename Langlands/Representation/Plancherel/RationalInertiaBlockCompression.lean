import Langlands.Representation.Plancherel.RationalInducedGeneratorCompression

/-! # Dynamic compression on the induced image of an actual inertia block -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance inertiaBlockCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance inertiaBlockCompressionAmbientTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance inertiaBlockCompressionLeviTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance inertiaBlockCompressionFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  (π : SmoothRep.{0, u, uV} ℂ (rationalPoints M))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (g : rationalPoints G)

/-- One positive stationary threshold for the actual induced image of every
object in the lifted rational inertia block of the supplied representative. -/
def RationalInducedInertiaBlockEventuallyStationary : Prop :=
  ∃ b : ℕ, 0 < b ∧
    ∀ B : CuspidalSupport.RationalInertiaBlock M
        (CuspidalSupport.rationalInertiaBaseLift M π),
      Jacquet.CompactCompressionStationaryFrom
        (((Aubert.General.rationalInertiaInductionFunctor M h hU
          (parabolicLeviPointHomeomorph r).symm).obj B.obj).representation)
        (((Aubert.General.rationalInertiaInductionFunctor M h hU
          (parabolicLeviPointHomeomorph r).symm).obj B.obj).isSmooth) K hK g b

/-- Native output-Jacquet finiteness and the exact small-progenerator property
give a threshold before every object in the actual induced inertia block. -/
theorem rationalInducedInertiaBlock_stationary_of_nativeJacquet
    (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hgen : CuspidalSupport.IsRationalNormKernelSmallProgenerator M π)
    (hπ : π.IsAdmissible)
    (hJac : UniversalInducedJacquetFiniteness r h hU (literalLeviRep r π).representation)
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hc : Jacquet.IsIwahoriContraction K
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
      (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
    (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m) :
    RationalInducedInertiaBlockEventuallyStationary r h hU π K hK g := by
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hCompact
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hp
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hp
  exact Aubert.General.rationalInertiaInduction_stationary_of_normKernel
    M h hU (parabolicLeviPointHomeomorph r).symm π K hK g
    (Aubert.General.compactOpenCofinal_of_nonarchimedean (rationalPoints G)) hP hr hgen
    (rationalNormKernelInducedCompressedAction_eventuallyStable
      r h hU π hG hn hr hCompact hπ hJac ξ K hK g hc hcentral)

end Langlands.Plancherel.RationalNormalized
