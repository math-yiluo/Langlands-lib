import Langlands.GroupScheme.Dynamic.SignedNoncontainment
import Langlands.GroupScheme.Dynamic.HomogeneousCurveUnipotent
import Langlands.GroupScheme.Reductive.RankOneSignedTangentDimension
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Positive roots from a prescribed homogeneous quotient curve -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HomogeneousQuotient

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A selected signed direction outside the prescribed subgroup, together with
its actual small unipotent representative and moving quotient-curve orbit. -/
structure SignedCurveUnipotentData
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (b : B ⟶ G)
    (q : G.X ⟶ Q) (a : SchemeAction G Q) where
  direction : Dynamic.NoncontainedSignedDirection i ν b
  curve : CurveUnipotentData
    (CommGroupScheme.groupHom direction.cocharacter ≫ i) q a

/-- The selected actual representative bounds at least one of the two
intrinsic signed dynamic tangent dimensions. -/
theorem SignedCurveUnipotentData.finrank_tangent_le_one_or_neg
    [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {b : B ⟶ G}
    {q : G.X ⟶ Q} {a : SchemeAction G Q}
    (D : SignedCurveUnipotentData i ν b q a) :
    Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) ≤ 1 ∨
    Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i))) ≤ 1 := by
  have hdim := D.curve.finrank_tangent_le_one
  change Module.finrank k (RelativeRoot.tangentSubmodule
    (Dynamic.unipotent (CommGroupScheme.groupHom D.direction.cocharacter ≫ i))) ≤ 1
    at hdim
  rcases D.direction.signed with h | h
  · rw [h] at hdim
    exact Or.inl hdim
  · rw [h] at hdim
    exact Or.inr hdim

variable [IsAlgClosed k]
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

/-- Construct the signed curve data from an actual proper subgroup containing
the dynamic centralizer; no noncontainment sign is supplied as an input. -/
def signedCurveUnipotentData
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hproper : ¬ IsIso b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hz : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    SignedCurveUnipotentData (t ≫ b) ν b q
      (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib) := by
  letI : Smooth G.X.hom := hG.smooth
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : ConnectedSpace G.X.left := hG.connectedSpace
  letI : IsClosedImmersion b.hom.hom.left := hb
  letI : Mono b.hom.hom := Over.mono_of_mono_left _
  letI : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  letI : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  let D := Dynamic.noncontainedSignedDirection hT (t ≫ b) ν b hb hproper hz
  exact ⟨D, curveUnipotentData b q hfib htorus hG hb hB hT t
    D.cocharacter hdimQ D.noncontained⟩

include q hfib in
/-- A homogeneous quotient curve of a prescribed proper solvable subgroup
gives original-cocharacter positive-root uniqueness, under the explicit
normal-solvable-torus and symmetrized-centralizer inputs. -/
theorem positive_roots_eq_of_rankOne_curve_quotient
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsConnectedReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hproper : ¬ IsIso b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B)
    (hi : IsMaximalTorus (t ≫ b))
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots (t ≫ b), ∀ β ∈ roots (t ≫ b),
        ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints (t ≫ b))
    (hn : (QuotientGroup.mk n : relativeWeylGroup (t ≫ b)) ≠ 1)
    (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hz : Dynamic.centralizer (CommGroupScheme.groupHom
        (normalizerSymmetrizedCocharacter (t ≫ b) n ν) ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots (t ≫ b) → β ∈ roots (t ≫ b) →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let D := signedCurveUnipotentData b q hfib htorus hG.isPseudoReductive hb hB
    hproper hT t (normalizerSymmetrizedCocharacter (t ≫ b) n ν) hdimQ hz
  intro α β
  exact hG.positive_roots_eq_of_signed_normalizerSymmetrized_unipotent_finrank_le_one
    (t ≫ b) hi hT hdep n hn ν D.finrank_tangent_le_one_or_neg

end HomogeneousQuotient

end Langlands.GroupScheme
