import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Statement: rank-one subgroups through coroots of anisotropic quadratic tori

Let `G` be a simply connected group over a field `F`, and `T` a maximal `F`-torus of `G`
that splits over a quadratic Galois extension `L` and is anisotropic over `F`. The module
states that every endomorphism `π` of `T` whose base change to `L` factors as a character
followed by a coroot `α^∨` of `(G_L, T_L)` maps `T` into a simply connected, absolutely
almost simple closed `F`-subgroup of `G` of inner type `A_1`. It proves nothing.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The base change of an affine group scheme along a field extension is affine; this lets
`IsRootDatumOf` be stated for the base-changed maximal torus. -/
local instance quadraticAnisotropicCorootRankOneSubgroupAffine {k L : Type u} [Field k]
    [Field L] [Algebra k L] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- Let `F` be a field, `G` a simply connected group over `F`, `L/F` a Galois extension of
degree `2`, and `i : T → G` a maximal `F`-torus whose base change to `L` is split and which
is anisotropic over `F`. Let `P` be a root datum of the split maximal torus `i_L` of `G_L`,
`j` an index of `P` and `χ` a character of `T_L`. If an endomorphism `π` of `T` over `F` has
base change `χ ≫ P.coroot j`, then `π ≫ i` factors through a closed `F`-subgroup `D` of `G`
that is simply connected and absolutely almost simple and has a Tits index of inner type
`A_1`. The subgroup is the rank-one subgroup `G(α)` of the root `α = P.root j`, generated
over `L` by the root subgroups of `α` and `-α`; it is defined over `F` because the
nontrivial element of `Gal(L/F)` acts on `X^*(T_L)` as `-1`. This is the rank-one input of
the componentwise argument in Platonov–Rapinchuk, *Algebraic Groups and Number Theory*,
proof of Proposition 6.25 (printed p. 394), in the quadratic case. -/
def QuadraticAnisotropicCorootRankOneSubgroupStatement : Prop :=
  ∀ (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalTorus i →
        IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj T.toGrp) →
        IsAnisotropic T.toGrp →
        ∀ (J : Type u)
          (P : RootDatum J
            (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T))
            (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T))),
          IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T)
            ((GroupScheme.baseChange (algebraBaseMap F L)).map i) P →
          ∀ (j : J)
            (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T))
            (π : T ⟶ T),
            (CommGroupScheme.baseChange (algebraBaseMap F L)).map π = χ ≫ P.coroot j →
            ∃ (D : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffineHom D.X.hom)
              (_ : LocallyOfFiniteType D.X.hom) (d : D ⟶ G) (t : T.toGrp ⟶ D),
              IsClosedSubgroup d ∧ t ≫ d = CommGroupScheme.groupHom π ≫ i ∧
                IsSimplyConnected D ∧ IsAbsolutelyAlmostSimple D ∧
                  ∃ x : TitsIndexData D, x.HasInnerTypeA 1

end Langlands.GroupScheme
