import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.GroupScheme.Rational.RootProductStatement

/-! # The distance of two minimal semi-standard parabolics is a Weyl length

Renard VII.3.5, opening paragraph, for a minimal Levi subgroup, in corrected form. For
minimal semi-standard parabolic subgroups `P` and `Q` with the same Levi factor
`M = Z_G(A_∅)`, `d(P, Q) = |Σ(P) ∩ Σ(Q̄)|` is the length of the unique `w ∈ W` with
`w · P = Q`, the length being taken for the simple reflections of `P`. Equivalently,
`d(uP_∅, vP_∅) = ℓ(u⁻¹v)` for the length defined by the simple roots of `P_∅`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VII.3.5, opening paragraph, minimal Levi factor, corrected form. Let `G` be
connected reductive over a field `k` with maximal split torus `i : A_∅ → G`, and let
`W = relativeWeylGroup i = N(k)/Z(k)`. The minimal semi-standard parabolic subgroups are
the dynamic parabolics `P_ξ = P(ξ)` of generic cocharacters `ξ` of `A_∅`; their common
Levi factor is `Z_G(A_∅)`, the unipotent radical of `P_ξ` is `U(ξ)` and that of the
opposite parabolic `P̄_ξ` is `U(-ξ)`. Put
`d(P_ξ, P_ξ') = |Σ(P_ξ) ∩ Σ(P̄_ξ')|`, the number of reduced roots of `A_∅` in the Lie
algebras of both `U(ξ)` and `U(-ξ')`. Say that `w ∈ W` moves `P_ξ` to `P_ξ'` when some
representative `n ∈ N(k)` of `w` satisfies `n P_ξ(k) n⁻¹ = P_ξ'(k)`. Then for generic
`ξ`, `ξ'`:

* exactly one `w ∈ W` moves `P_ξ` to `P_ξ'`;
* if `w` moves `P_ξ` to `P_ξ'`, then `d(P_ξ, P_ξ') = ℓ(w)` for every Coxeter system on `W`
  realizing the root action with simple roots those of `ξ` (the simple roots of `P_ξ`);
* for every generic `ν` (the standard minimal parabolic `P_∅ = P_ν`), if `u` moves `P_ν` to
  `P_ξ` and `v` moves `P_ν` to `P_ξ'`, then `d(P_ξ, P_ξ') = ℓ(u⁻¹v)` for every Coxeter
  system on `W` realizing the root action with simple roots those of `ν`. -/
def MinimalParabolicDistanceLengthStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    let parabolicPoints : cocharacterLattice T → Subgroup (RationalPoint k G.X) := fun ξ =>
      (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier (Over.mk (𝟙 _))
    let d : cocharacterLattice T → cocharacterLattice T → ℕ := fun ξ ξ' =>
      (RelativeRoot.intertwiningRelativeRoots i
          (Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i))
          (Dynamic.unipotent (CommGroupScheme.groupHom (-ξ') ≫ i)) ∩
        RelativeRoot.indivisibleRoots i).ncard
    let Moves : relativeWeylGroup i → cocharacterLattice T → cocharacterLattice T → Prop :=
      fun w ξ ξ' => ∃ n : normalizerPoints i,
        (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
          (parabolicPoints ξ).map
              (MulAut.conj (n : RationalPoint k G.X) : RationalPoint k G.X →* RationalPoint k G.X) =
            parabolicPoints ξ'
    ∀ ξ ξ' : cocharacterLattice T, IsGenericCocharacter i ξ → IsGenericCocharacter i ξ' →
      (∃! w : relativeWeylGroup i, Moves w ξ ξ') ∧
      (∀ w : relativeWeylGroup i, Moves w ξ ξ' →
        ∀ (C : CoxeterMatrix (SimpleRoot i ξ)) (cs : CoxeterSystem C (relativeWeylGroup i)),
          IsRelativeWeylCoxeterRealization i ξ cs → d ξ ξ' = cs.length w) ∧
      ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
        ∀ u v : relativeWeylGroup i, Moves u ν ξ → Moves v ν ξ' →
        ∀ (C : CoxeterMatrix (SimpleRoot i ν)) (cs : CoxeterSystem C (relativeWeylGroup i)),
          IsRelativeWeylCoxeterRealization i ν cs → d ξ ξ' = cs.length (u⁻¹ * v)

end Langlands.GroupScheme
