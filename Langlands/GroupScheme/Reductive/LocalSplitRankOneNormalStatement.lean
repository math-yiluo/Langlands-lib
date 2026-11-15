import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily

/-! # Statement: rank-one normalization of Weyl-normalized simple root data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- **Rank-one normalization at a root `a`.** For a family `v` of maps `𝔾ₐ → G`, with
`N = v_{-a}(-1) v_a(1) v_{-a}(-1)` (`weylPoint (v a) (v (-a))`, where `-a` is the index
`P.reflectionPerm a a`):
1. `N v_a(x) N⁻¹ = v_{-a}(-x)` over every ring over `R`;
2. `N v_{-a}(x) N⁻¹ = v_a(-x)` over every ring over `R`;
3. `N² = a^∨(-1)`, the image under the torus `i` of the cocharacter point of the coroot of
   `a` at `-1`. -/
def RankOneNormal (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (v : J → (Ga R ⟶ G)) (a : J) : Prop :=
  (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v a) (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v (P.reflectionPerm a a)) (Over.mk s) (-x)) ∧
  (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v (P.reflectionPerm a a)) (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v a) (Over.mk s) (-x)) ∧
  weylPoint (v a) (v (P.reflectionPerm a a)) * weylPoint (v a) (v (P.reflectionPerm a a)) =
    cocharPoint (P.coroot a) (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1) ≫ i.hom.hom

end LocalSplitCell

open LocalSplitCell

/-- **Rank-one normalization over a local ring.** Let `G` be a reductive group scheme over a
commutative local ring `R`, with affine structure morphism, a closed coordinate split torus
`i : T_I → G` that is maximal on every residue-field fibre, and a fibrewise root datum `P`.
Let `b` be a base and `u : J → (𝔾ₐ ⟶ G)` Weyl-normalized simple-root data: for every
simple root `a`, `u a` and `u (-a)` are root parametrizations of `i` for `a` and `-a`, and
`u_{-a}(-1) u_a(1) u_{-a}(-1)` is a Weyl point of `i` acting by `s_a`. Then `u` is rank-one
normal (`RankOneNormal`) at every simple root. -/
def LocalSplitRankOneNormalStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ (b : P.Base) (u : J → (Ga R ⟶ G)),
        (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
          IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) →
        (∀ a ∈ b.support,
          IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)) →
        ∀ a ∈ b.support, RankOneNormal i P u a

end Langlands.GroupScheme
