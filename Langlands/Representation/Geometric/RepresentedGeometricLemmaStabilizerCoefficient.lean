import Langlands.Representation.Geometric.RepresentedParabolicSupportOrbit
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarCharacters

/-! # The original normalized coefficient on the full orbit stabilizer -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance stabilizerCoefficientAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

/-- The original parabolic projection, transported to the Levi's own points. -/
def parabolicToLeviPoints :
    letI := leviPointTopology l hl
    pointImage p →* rationalPoints M := by
  letI := leviPointTopology l hl
  exact (leviPointsEquiv p l hp hl).symm.toMonoidHom.comp
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
theorem continuous_parabolicToLeviPoints :
    letI := leviPointTopology l hl
    Continuous (parabolicToLeviPoints p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  exact (leviPointsEquiv p l hp hl).symm.continuous.comp
    (continuous_projection_pointImage p l r hp hl hr hmul)

/-- The full normalized inducing action is the original Levi half-twist
inflated through the actual projection. -/
theorem leviInducingFunctor_eq_twist_comp
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((leviInducingFunctor p l r hp hr hl hmul).obj A).ρ =
      (Langlands.twist
        (leviInducingHalfCharacter p l r hp hr hl).toMonoidHom A.representation).comp
        (parabolicToLeviPoints p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  let d := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hδ := isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro a
  change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hc
      (pointImage p) d.le_normalizer x : ℂˣ) : ℂ) •
      A.representation ((leviPointsEquiv p l hp hl).symm (d.projection x)) a =
    ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hc
      (pointImage (l ≫ p)) d.levi_le_normalizer
        ((leviPointsEquiv p l hp hl)
          ((leviPointsEquiv p l hp hl).symm (d.projection x))) : ℂˣ) : ℂ) •
      A.representation ((leviPointsEquiv p l hp hl).symm (d.projection x)) a
  rw [closedHalfCharacter_eq_comp_projection d hc hδ,
    MonoidHom.comp_apply, ContinuousMulEquiv.apply_symm_apply]

variable (q : Q ⟶ G) (z : rationalPoints G)

/-- Inverse orbit conjugation followed by the actual original Levi projection. -/
def stabilizerToLeviPoints :
    letI := leviPointTopology l hl
    Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹ →* rationalPoints M := by
  letI := leviPointTopology l hl
  exact (parabolicToLeviPoints p l r hp hr hl hmul).comp
    (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
    [LocallyCompactSpace (rationalPoints G)] in
theorem continuous_stabilizerToLeviPoints :
    letI := leviPointTopology l hl
    Continuous (stabilizerToLeviPoints p l r hp hr hl hmul q z) := by
  let := leviPointTopology l hl
  apply (continuous_parabolicToLeviPoints p l r hp hr hl hmul).comp
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, Geometric.stabilizerToInducing_apply, inv_inv]
  exact (continuous_const.mul
    (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const

/-- The full orbit coefficient on the source carrier, with its original half. -/
def stabilizerTwistedCoefficientFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      Rep.{v} ℂ (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) := by
  letI := leviPointTopology l hl
  let χ := leviInducingHalfCharacter p l r hp hr hl
  exact SmoothRep.twistFunctor χ.toMonoidHom χ.isOpen_ker ⋙ SmoothRep.toRep ⋙
    Rep.resFunctor (stabilizerToLeviPoints p l r hp hr hl hmul q z)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isSmooth_stabilizerTwistedCoefficientFunctor_obj
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    IsSmooth ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ := by
  let := leviPointTopology l hl
  let χ := leviInducingHalfCharacter p l r hp hr hl
  exact isSmooth_comp
    (stabilizerToLeviPoints p l r hp hr hl hmul q z)
    (continuous_stabilizerToLeviPoints p l r hp hr hl hmul q z)
    (A.twist χ.toMonoidHom χ.isOpen_ker).isSmooth

/-- The original normalized stabilizer coefficient is naturally the half-twist
pulled back through its actual map into the source Levi's own points. -/
def stabilizerCoefficientTwistIso :
    letI := leviPointTopology l hl
    leviInducingFunctor.{u, v} p l r hp hr hl hmul ⋙
        Rep.resFunctor (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹) ≅
      stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z := by
  letI := leviPointTopology l hl
  refine NatIso.ofComponents (fun A => Rep.mkIso (equivOfRepresentationEq ?_)) ?_
  · change (((leviInducingFunctor p l r hp hr hl hmul).obj A).ρ).comp _ = _
    rw [leviInducingFunctor_eq_twist_comp p l r hp hr hl hmul A]
    rfl
  · intro A B f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl

/-- The actual orbit piece is compact induction of that explicit coefficient,
with the same stabilizer subgroup and inverse representative. -/
def orbitPieceTwistedCoefficientIso :
    letI := leviPointTopology l hl
    smoothLeviInducingFunctor.{u, v} p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ ≅
      stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z ⋙
        Induction.compactInductionFunctor
          (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) ⋙ SmoothRep.toRep := by
  letI := leviPointTopology l hl
  exact Functor.isoWhiskerRight (stabilizerCoefficientTwistIso p l r hp hr hl hmul q z)
    (Induction.compactInductionFunctor
      (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) ⋙ SmoothRep.toRep)

end Langlands.Aubert.General.RepresentedParabolic
