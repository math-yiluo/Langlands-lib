# The integral closed factor of a generically conjugate torus family

Let `S` be a scheme in universe `u`, and let `G`, `D`, `Q` and `L` be group
schemes over `S`. Let `M` be a scheme over `S`, `K` a group scheme over `M`,
and `j : K ⟶ L_M` a closed subgroup family. Let `A` be a valuation subring of
a field `Ω`. Write `s : Spec Ω ⟶ Spec A` for the map induced by the inclusion
`A → Ω`.

## The structure

For a map `a : Spec A ⟶ S` and a point `b : Over.mk a ⟶ M` over `S`, write
`B = K_{b}` for the source of the evaluated inclusion
`familyHom j b : B ⟶ L_A`. Given a homomorphism `m : Q ⟶ L`, the structure
`TorusSubgroupModuli.IntegralFactor A D m j a b` consists of

- `factor : B ⟶ Q_A`, a homomorphism of group schemes over `Spec A`;
- `fac : factor ≫ m_A = familyHom j b`;
- `isClosedSubgroup_factor : IsClosedSubgroup factor`;
- `genericIso : B_Ω ≅ (D_A)_Ω`, an isomorphism of group schemes over `Spec Ω`.

Here `Q_A`, `L_A` and `D_A` are base changes along `a`, and the
`Ω`-subscript is base change along `s`. The structure records no
compatibility between `genericIso` and `factor`. It records only that the
generic fibre of `B` is isomorphic to the generic fibre of `D_A`.

## The constructions

`TorusSubgroupModuli.integralFactor` takes homomorphisms `q : G ⟶ Q`,
`d : D ⟶ Q` and `m : Q ⟶ L`. It assumes that `m` is a monomorphism on total
spaces, that `Q` is quasi-compact and locally of finite type over `S`, and
that `L` is quasi-separated over `S`. Moreover `j` is a closed subgroup family
with torus source `K`, `d ≫ m` is a closed subgroup, and the evaluated family
of `f : G.X ⟶ M` is, on all tests, the range of the conjugate family of
`d ≫ m` by the group-valued parameter `q ≫ m`. Then for every point
`b : Over.mk a ⟶ M` and every point `g : Over.mk (s ≫ a) ⟶ G.X` with
`g ≫ f` equal to the restriction of `b` along `s`, it constructs an
`IntegralFactor A D m j a b`.

`TorusSubgroupModuli.integralFactorOfPoints` is the same construction for
points as they appear in
`SelfCentralizingConjugacyValuationLiftStatement`: `g : Spec Ω ⟶ G.X.left`
and `b : Spec A ⟶ M.left` with `s ≫ b = g ≫ f.left`. It uses
`a := b ≫ M.hom` and the point `Over.homMk b rfl`.

`TorusGraphQuotient.GroupFactorization.integralFactor` specializes this to a
graph factorization `F` of homomorphisms `ρ : G ⟶ L` and `e : D ⟶ L` with
`D` commutative. It uses `Q := F.quotient`, `q := F.projection`,
`d := F.torus` and `m := F.embedding`. Its hypotheses are that `e` is a
closed subgroup and that the evaluated family of `f` is the range of the
conjugate family of `e` by `ρ`. The required monomorphism, quasi-compactness
and smoothness of `F.quotient` come from the fields of `F`. The equations
`F.torus_fac` and `F.projection_fac` rewrite `d ≫ m` and `q ≫ m` as `e` and
`ρ`.

## The proof

`restrictedFamilyFactorization` gives the generic data. It provides an
isomorphism `B_Ω ≅ (D_A)_Ω`, which becomes `genericIso`. It also provides a
homomorphism `B_Ω ⟶ (Q_A)_Ω` whose composite with `(m_A)_Ω` is the base
change of `familyHom j b`. The source `B` is a torus over `Spec A`, so it is
smooth with geometrically connected fibres.

The base change `m_A` is a monomorphism. It is quasi-compact and locally of
finite type because its composite with the quasi-separated structure map of
`L_A` is the structure map of `Q_A`. Composing the generic factor with the
first projection of `Q_A` gives a morphism `pullback B.X.hom s ⟶ Q_A`. The
generic factorization and the naturality of base-change projections turn
this morphism into a generic lift of `familyHom j b` through `m_A`. A valuation
ring is an integrally closed domain with fraction field `Ω`. Thus
`genericGroupMonoLift` (module `Langlands.GroupScheme.GenericGroupMonoLift`) extends this lift to a homomorphism
`factor : B ⟶ Q_A` with `factor ≫ m_A = familyHom j b`. The composite is a
closed immersion by `isClosedSubgroup_familyHom`, and `m_A` is separated
because it is a monomorphism. Hence `factor` is a closed immersion.

## Provenance and scope

This is an internal construction for the valuative argument toward the
affineness of the quotient by the normalizer of a self-centralizing maximal
torus in a smooth separated group. It gives the first steps of the route
through the valuative form of SGA 3, Exposé XVI, Lemma 3.2. It assembles the Library
lemmas `restrictedFamilyFactorization`, `genericGroupMonoLift` and
`isClosedSubgroup_familyHom`, and it is not a transcription of a literature
theorem. It does not show that `factor` is a conjugate of `d_A`. It does not
use henselian or algebraically closed residue fields, and it does not choose
the lifted point of `G`.
