import Langlands.Group.TitsSystem
import Langlands.GroupScheme.Rational.RelativeReflection

/-!
# Statement: the relative Tits system of a reductive group

For a maximal split torus `i` of a connected reductive group `G` over a field `k` and a generic
cocharacter `ν`, the rational points of the minimal standard parabolic `P_∅`, the normalizing
points of `i`, the quotient map onto `relativeWeylGroup i = N(k)/Z(k)` and the reflections in
the simple relative roots form a Tits system, and each simple relative root has exactly one
reflection, distinct simple roots having distinct reflections.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The relative Tits system of `i` and `ν` on actual rational points: with
`B = standardParabolicPoints i ν ∅`, `N = normalizerPoints i`, the quotient map
`N → relativeWeylGroup i = N(k)/Z(k)` and `S = simpleRelativeReflections i ν`, the quadruple
`(G(k), B, N, S)` is a Tits system; every simple relative root has exactly one relative
reflection; and two simple relative roots with a common reflection are equal. -/
def HasRelativeTitsSystem (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (ν : cocharacterLattice T) : Prop :=
  Langlands.Group.IsTitsSystem (standardParabolicPoints i ν ∅) (normalizerPoints i)
      (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
      (simpleRelativeReflections i ν) ∧
    (∀ α ∈ simpleRelativeRoots i ν, ∃! w : relativeWeylGroup i, IsRelativeReflection i α w) ∧
    ∀ α ∈ simpleRelativeRoots i ν, ∀ β ∈ simpleRelativeRoots i ν, ∀ w : relativeWeylGroup i,
      IsRelativeReflection i α w → IsRelativeReflection i β w → α = β

/-- **The relative Tits system** (Borel–Tits 5.15–5.16 and 5.18, Renard V.4.1). For a maximal
split torus `i` of a connected reductive group `G` over a field and a generic cocharacter `ν`
of it, `(G(k), P_∅(k), N(k), S)` is a Tits system with Weyl group `N(k)/Z(k)`, where `S`
consists of the reflections in the simple relative roots, and these reflections correspond
bijectively to the simple relative roots. -/
def RelativeTitsSystemStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν → HasRelativeTitsSystem i ν

namespace HasRelativeTitsSystem

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ν : cocharacterLattice T}

theorem isTitsSystem (h : HasRelativeTitsSystem i ν) :
    Langlands.Group.IsTitsSystem (standardParabolicPoints i ν ∅) (normalizerPoints i)
      (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
      (simpleRelativeReflections i ν) :=
  h.1

theorem existsUnique_isRelativeReflection (h : HasRelativeTitsSystem i ν)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) :
    ∃! w : relativeWeylGroup i, IsRelativeReflection i α w :=
  h.2.1 α hα

theorem eq_of_isRelativeReflection (h : HasRelativeTitsSystem i ν) {α β : characterLattice T}
    (hα : α ∈ simpleRelativeRoots i ν) (hβ : β ∈ simpleRelativeRoots i ν)
    {w : relativeWeylGroup i} (hαw : IsRelativeReflection i α w)
    (hβw : IsRelativeReflection i β w) : α = β :=
  h.2.2 α hα β hβ w hαw hβw

/-- `B ∩ N = Z(k)`: the normalizing points in the minimal standard parabolic are exactly the
centralizing points. -/
theorem inf_eq (h : HasRelativeTitsSystem i ν) :
    standardParabolicPoints i ν ∅ ⊓ normalizerPoints i = centralizerPoints i :=
  h.1.inf_eq (QuotientGroup.ker_mk' _) (centralizerPoints_le_normalizerPoints i)

/-- Rank zero: without simple relative roots the relative Weyl group is trivial. -/
theorem eq_one_of_simpleRelativeRoots_eq_empty (h : HasRelativeTitsSystem i ν)
    (hν : simpleRelativeRoots i ν = ∅) (w : relativeWeylGroup i) : w = 1 := by
  have h1 := h.1
  rw [simpleRelativeReflections_eq_empty hν] at h1
  exact h1.eq_one_of_empty w

/-- Rank zero: without simple relative roots the minimal standard parabolic has all rational
points. -/
theorem eq_top_of_simpleRelativeRoots_eq_empty (h : HasRelativeTitsSystem i ν)
    (hν : simpleRelativeRoots i ν = ∅) : standardParabolicPoints i ν ∅ = ⊤ := by
  have h1 := h.1
  rw [simpleRelativeReflections_eq_empty hν] at h1
  exact h1.eq_top_of_empty

end HasRelativeTitsSystem

end Langlands.GroupScheme
