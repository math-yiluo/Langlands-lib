import Langlands.Representation.Geometric.RepresentedGeometricLemmaLeviProjection
import Langlands.Representation.Geometric.RepresentedParabolicSupportOrbit
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups

/-! # The normalized coefficient on the target intersection -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance coefficientAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

/-- The actual normalized inducing covariance is trivial on the source radical. -/
theorem leviInducingFunctor_radical_apply
    (A : letI := leviPointTopology l hl
      SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (n : pointImage (r ≫ p)) (a : A) :
    letI := leviPointTopology l hl
    ((leviInducingFunctor p l r hp hr hl hmul).obj A).ρ
      ⟨n, pointImage_comp_le p r n.property⟩ a = a := by
  let := leviPointTopology l hl
  let d := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hδ := isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hc
    (pointImage p) d.le_normalizer ⟨n, d.unipotent_le n.property⟩ : ℂˣ) : ℂ) •
      A.representation ((leviPointsEquiv p l hp hl).symm
        (d.projection ⟨n, d.unipotent_le n.property⟩)) a = a
  rw [closedHalfCharacter_unipotent d hc hδ n, d.projection_unipotent]
  simp only [map_one, Units.val_one, one_smul, Module.End.one_apply]

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

/-- Restrict the original normalized coefficient to the target intersection. -/
def targetIntersectionCoefficientFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      Rep.{v} ℂ
        ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) := by
  letI := leviPointTopology l hl
  exact leviInducingFunctor p l r hp hr hl hmul ⋙
    Rep.resFunctor D.targetParabolicPointsToSource

/-- The original normalized coefficient on the actual common Levi. -/
def commonLeviCoefficientFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      Rep.{v} ℂ
        ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) := by
  letI := leviPointTopology l hl
  exact D.targetIntersectionCoefficientFunctor ⋙
    Rep.resFunctor (Subgroup.inclusion D.targetPoints_isSemidirectDecomposition.levi_le)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The target intersection radical acts trivially on the original coefficient. -/
theorem targetIntersectionCoefficient_radical_apply
    (A : letI := leviPointTopology l hl
      SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (n : ↥(pointImage (lQ ≫ q) ⊓
      (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom)) (a : A) :
    letI := leviPointTopology l hl
    ((D.targetIntersectionCoefficientFunctor).obj A).ρ
      ⟨n, D.targetPoints_isSemidirectDecomposition.unipotent_le n.property⟩ a = a := by
  let := leviPointTopology l hl
  let x : ↥(pointImage (lQ ≫ q) ⊓
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) :=
    ⟨n, D.targetPoints_isSemidirectDecomposition.unipotent_le n.property⟩
  have hx : (D.targetParabolicPointsToSource x : rationalPoints G) ∈ pointImage (r ≫ p) := by
    rw [D.targetParabolicPointsToSource_apply_coe]
    have hn := Subgroup.mem_map_equiv.mp n.property.2
    simpa only [MulAut.conj_symm_apply, inv_inv] using hn
  change ((leviInducingFunctor p l r hp hr hl hmul).obj A).ρ
    (D.targetParabolicPointsToSource x) a = a
  exact leviInducingFunctor_radical_apply (p := p) (l := l) (r := r)
    (hp := hp) (hr := hr) (hl := hl) (hmul := hmul)
    A ⟨D.targetParabolicPointsToSource x, hx⟩ a

/-- On actual carriers the normalized coefficient is inflated from the common Levi. -/
theorem targetIntersectionCoefficient_eq_comp_projection
    (A : letI := leviPointTopology l hl
      SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((D.targetIntersectionCoefficientFunctor).obj A).ρ =
      (((D.commonLeviCoefficientFunctor).obj A).ρ).comp
        D.targetPoints_isSemidirectDecomposition.projection := by
  let := leviPointTopology l hl
  let d := D.targetPoints_isSemidirectDecomposition
  let σ := ((D.targetIntersectionCoefficientFunctor).obj A).ρ
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro a
  let m : ↥(pointImage (lQ ≫ q) ⊓
      (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) :=
    ⟨d.projection x, d.levi_le (d.projection x).property⟩
  let n : ↥(pointImage (lQ ≫ q) ⊓
      (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) :=
    ⟨(m : rationalPoints G)⁻¹ * (x : rationalPoints G), d.projection_inv_mul_mem x⟩
  have hx : x = m * ⟨n, d.unipotent_le n.property⟩ := by
    apply Subtype.ext
    change (x : rationalPoints G) = (m : rationalPoints G) *
      ((m : rationalPoints G)⁻¹ * (x : rationalPoints G))
    exact (mul_inv_cancel_left _ _).symm
  change σ x a = σ m a
  rw [hx, map_mul, Module.End.mul_apply, D.targetIntersectionCoefficient_radical_apply A n a]

/-- Inflation from the actual common Levi is natural in every smooth coefficient. -/
def targetIntersectionCoefficientInflationIso :
    letI := leviPointTopology l hl
    D.targetIntersectionCoefficientFunctor.{u, v} ≅
      D.commonLeviCoefficientFunctor ⋙
        Rep.resFunctor D.targetPoints_isSemidirectDecomposition.projection := by
  letI := leviPointTopology l hl
  refine NatIso.ofComponents (fun A =>
    Rep.mkIso (equivOfRepresentationEq (D.targetIntersectionCoefficient_eq_comp_projection A))) ?_
  intro A B f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  rfl

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
