import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily

/-! # Statement: the rank-one Bruhat relation for Weyl-normalized simple root data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- **The rank-one Bruhat relation at a root `a`.** For a family `v` of maps `𝔾ₐ → G`, over
every ring over `R`, whenever `d = 1 + x y` is a unit,
`v_a(x) v_{-a}(y) = v_{-a}(d⁻¹ y) · a^∨(d) · v_a(d⁻¹ x)`. Here `-a` is the index
`P.reflectionPerm a a` and `a^∨(d)` is the image under the torus `i` of the cocharacter point of
the coroot of `a` at `d`. -/
def RankOneBruhat (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (v : J → (Ga R ⟶ G)) (a : J) : Prop :=
  ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) (d : (Γ((Over.mk s).left, ⊤))ˣ),
    (d : Γ((Over.mk s).left, ⊤)) = 1 + x * y →
    rootPoint (v a) (Over.mk s) x * rootPoint (v (P.reflectionPerm a a)) (Over.mk s) y =
      rootPoint (v (P.reflectionPerm a a)) (Over.mk s) ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * y) *
        (cocharPoint (P.coroot a) (Over.mk s) d ≫ i.hom.hom) *
        rootPoint (v a) (Over.mk s) ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * x)

end LocalSplitCell

open LocalSplitCell

/-- **The rank-one Bruhat relation over a local ring.** Let `G` be a reductive group scheme
over a commutative local ring `R`, with affine structure morphism, a closed coordinate split
torus `i : T_I → G` that is maximal on every residue-field fibre, and a fibrewise root datum
`P`. Let `b` be a base and `u : J → (𝔾ₐ ⟶ G)` Weyl-normalized simple-root data: for every
simple root `a`, `u a` and `u (-a)` are root parametrizations of `i` for `a` and `-a`, and
`u_{-a}(-1) u_a(1) u_{-a}(-1)` is a Weyl point of `i` acting by `s_a`. Then `u` satisfies the
rank-one Bruhat relation (`RankOneBruhat`) at every simple root. -/
def LocalSplitRankOneBruhatStatement : Prop :=
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
        ∀ a ∈ b.support, RankOneBruhat i P u a

end Langlands.GroupScheme
