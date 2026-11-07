import Langlands.Representation.Geometric.RepresentedParabolicCoinvariants
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStabilizerCoefficient

/-! # The original normalized quotient and ordinary projection-kernel coinvariants -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance kernelCoinvariantsAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

local notation "d" => isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
local notation "π" => IsSemidirectDecomposition.projection d
local notation "rad" => parabolicRadicalPoints p r
local notation "κ" => leviInverseHalfCharacter p l r hp hr hl

omit [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The original radical inside the original parabolic is exactly the kernel
of its original Levi projection. -/
theorem parabolicRadicalPoints_eq_projectionKernel : rad = (π).ker := by
  ext x
  exact ((d).projection_eq_one_iff x).symm

/-- Ordinary coinvariants by the actual projection kernel, restricted through
the original Levi point map and twisted by its original inverse Haar half. -/
def leviProjectionKernelCoinvariantsFunctor :
    letI := leviPointTopology l hl
    Rep.{v} ℂ (pointImage p) ⥤ Rep.{v} ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  exact Rep.quotientToCoinvariantsFunctor ℂ (π).ker ⋙
    Rep.resFunctor ((QuotientGroup.mk' (π).ker).comp (leviToParabolicPoints p l)) ⋙
    (κ).twistFunctor

/-- This is the full original inverse-half twist of ordinary kernel
coinvariants, evaluated through the original Levi point inclusion. -/
theorem leviProjectionKernelCoinvariantsFunctor_obj_representation
    (A : Rep.{v} ℂ (pointImage p)) :
    letI := leviPointTopology l hl
    ((leviProjectionKernelCoinvariantsFunctor p l r hp hr hl hmul).obj A).ρ =
      Langlands.twist (κ).toMonoidHom
        ((A.ρ.toCoinvariants (π).ker).comp (leviToParabolicPoints p l)) := by
  let := leviPointTopology l hl
  rfl

@[simp]
theorem leviProjectionKernelCoinvariantsFunctor_map_mk
    {A B : Rep.{v} ℂ (pointImage p)} (f : A ⟶ B) (a : A) :
    letI := leviPointTopology l hl
    ((leviProjectionKernelCoinvariantsFunctor p l r hp hr hl hmul).map f).hom
        (Jacquet.mk A.ρ (π).ker a) =
      Jacquet.mk B.ρ (π).ker (f.hom a) := by
  let := leviPointTopology l hl
  rfl

/-- The quotient comparison uses the same original representative, through
the genuine radical-kernel equality and trivial-character quotient comparison. -/
def leviParabolicProjectionKernelEquiv (A : Rep.{v} ℂ (pointImage p)) :
    letI := leviPointTopology l hl
    Representation.Equiv
      (((leviParabolicCoinvariantsFunctor p l r hp hr hl hmul).obj A).ρ)
      (((leviProjectionKernelCoinvariantsFunctor p l r hp hr hl hmul).obj A).ρ) := by
  letI := leviPointTopology l hl
  let eK := MulEquiv.subgroupCongr (parabolicRadicalPoints_eq_projectionKernel p l r hp hr hmul)
  let eT := Jacquet.Localization.transportEquiv A.ρ A.ρ rad (π).ker 1 1 eK
    (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl)
  let hn : (⊤ : Subgroup (pointImage p)) ≤ Subgroup.normalizer (π).ker := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  let eO := Jacquet.Localization.trivialEquiv A.ρ (π).ker ⊤ hn
  refine { toLinearEquiv := eT.trans eO.toLinearEquiv, isIntertwining' := ?_ }
  intro m
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective A.ρ rad 1 x
  change (eT.trans eO.toLinearEquiv)
      ((((κ).toMonoidHom m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk A.ρ rad 1 (A.ρ (leviToParabolicPoints p l m) a)) =
    (((κ).toMonoidHom m : ℂˣ) : ℂ) •
      Jacquet.mk A.ρ (π).ker (A.ρ (leviToParabolicPoints p l m) a)
  rw [map_smul]
  rfl

@[simp]
theorem leviParabolicProjectionKernelEquiv_mk (A : Rep.{v} ℂ (pointImage p)) (a : A) :
    letI := leviPointTopology l hl
    leviParabolicProjectionKernelEquiv p l r hp hr hl hmul A
        (Jacquet.Localization.mk A.ρ rad 1 a) =
      Jacquet.mk A.ρ (π).ker a := by
  let := leviPointTopology l hl
  rfl

/-- The original normalized radical quotient is naturally the normalized
ordinary projection-kernel quotient on the original Levi's own points. -/
def leviParabolicProjectionKernelIso :
    letI := leviPointTopology l hl
    leviParabolicCoinvariantsFunctor.{u,v} p l r hp hr hl hmul ≅
      leviProjectionKernelCoinvariantsFunctor p l r hp hr hl hmul := by
  letI := leviPointTopology l hl
  refine NatIso.ofComponents
    (fun A => Rep.mkIso (leviParabolicProjectionKernelEquiv p l r hp hr hl hmul A)) ?_
  intro A B f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective A.ρ rad 1 x
  rfl

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  {Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  (z : rationalPoints G)

/-- The actual normalized orbit source, expressed using ordinary coinvariants
by the original target projection kernel. -/
def orbitProjectionKernelCoinvariantsFunctor :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    SmoothRep.{0,u,v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L) := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  exact stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z ⋙
    Induction.compactInductionFunctor
      (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) ⋙ SmoothRep.toRep ⋙
    leviProjectionKernelCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ

/-- The exact left functor of the represented local statement naturally
becomes the actual normalized ordinary-kernel orbit quotient. -/
def orbitParabolicProjectionKernelIso :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    smoothLeviInducingFunctor.{u,v} p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ ⋙
          leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ ≅
      orbitProjectionKernelCoinvariantsFunctor p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ z := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  exact Functor.isoWhiskerRight
      (orbitPieceTwistedCoefficientIso p l r hp hr hl hmul q z)
      (leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ) ≪≫
    Functor.isoWhiskerLeft
      (stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z ⋙
        Induction.compactInductionFunctor
          (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) ⋙ SmoothRep.toRep)
      (leviParabolicProjectionKernelIso q lQ rQ hq hrQ hlQ hmulQ)

end Langlands.Aubert.General.RepresentedParabolic
