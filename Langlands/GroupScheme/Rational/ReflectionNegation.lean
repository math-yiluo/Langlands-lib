import Langlands.GroupScheme.Rational.RelativeReflection
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # Negation of actual relative roots from normalizer reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- A normalizing point that negates a root proves that its opposite is an
actual relative root. -/
theorem neg_mem_relativeRoots_of_weylAction_eq_neg
    {α : characterLattice T} (hα : α ∈ relativeRoots i)
    (n : normalizerPoints i) (hn : weylAction i n α = -α) :
    -α ∈ relativeRoots i := by
  rw [← hn]
  exact weylAction_mapsTo_relativeRoots i n hα

/-- A reflection in an actual relative root proves membership of its opposite
when rationalization of the character lattice is injective. -/
theorem IsRelativeReflection.neg_mem_relativeRoots
    {α : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i α w) (hT : IsSplitTorus T.toGrp) :
    -α ∈ relativeRoots i := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hself := congrArg Subtype.val h.relativeWeylAction_apply_self
  change toRat (weylAction i n α) = -toRat α at hself
  apply neg_mem_relativeRoots_of_weylAction_eq_neg i h.mem_relativeRoots n
  apply hT.character_toRat_injective
  simpa only [map_neg] using hself

/-- Integral normalizer reflection data give negation stability directly,
without finiteness or a full relative-root-system realization. -/
theorem RelativeRootReflectionData.neg_mem_relativeRoots
    (D : RelativeRootReflectionData i) {α : characterLattice T}
    (hα : α ∈ relativeRoots i) :
    -α ∈ relativeRoots i := by
  apply neg_mem_relativeRoots_of_weylAction_eq_neg i hα (D.representative ⟨α, hα⟩)
  rw [D.action]
  change α - latticePairing T α (D.coroot ⟨α, hα⟩) • α = -α
  have hpair : latticePairing T α (D.coroot ⟨α, hα⟩) = 2 := D.pair_self ⟨α, hα⟩
  rw [hpair, two_zsmul]
  abel

/-- The opposite-root permutation of the actual relative roots, constructed
from integral normalizer reflection data. -/
def RelativeRootReflectionData.negEquiv (D : RelativeRootReflectionData i) :
    relativeRoots i ≃ relativeRoots i where
  toFun α := ⟨-α.val, D.neg_mem_relativeRoots i α.property⟩
  invFun α := ⟨-α.val, D.neg_mem_relativeRoots i α.property⟩
  left_inv α := Subtype.ext (neg_neg α.val)
  right_inv α := Subtype.ext (neg_neg α.val)

@[simp]
theorem RelativeRootReflectionData.coe_negEquiv_apply
    (D : RelativeRootReflectionData i) (α : relativeRoots i) :
    (D.negEquiv i α : characterLattice T) = -α.val :=
  rfl

/-- The full published structural target implies the focused negation target.
This adapter retains the full structural assertion as a premise. -/
theorem relativeRootNegationStatement_of_relativeRootSystemStatement
    (h : RelativeRootSystemStatement.{u}) :
    RelativeRootNegationStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  exact fun _ hα =>
    (h k G hG T i hi).neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα

end Langlands.GroupScheme
