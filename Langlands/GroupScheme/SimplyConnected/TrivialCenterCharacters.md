# Trivial centre from trivial geometric centre characters

Module: `Langlands.GroupScheme.SimplyConnected.TrivialCenterCharacters`.

The centre of a reductive group is of multiplicative type. If it has no nontrivial character
over the separable closure, it is the trivial group. Then the identity homomorphism kills the
centre, and an adjoint quotient of the group is an isomorphism. Compare J. Tits,
*Classification of algebraic semisimple groups* (1966), §1.5.5, printed p.38 (source
`tits-1966-classification-algebraic-semisimple`): the centre of a semisimple group over an
algebraically closed field `K` is `Hom(C*(G), K*)`, where `C*(G)` is its group of centre
characters. This module proves these
facts for the Library's toral centre `d.toralCenter` of Tits index data
`d : TitsIndexData G` (modules `Langlands.GroupScheme.Reductive.TitsIndex` and
`Langlands.GroupScheme.Reductive.CenterInMaximalTorus`). The toral centre is a commutative
group scheme `d.toralCenter.group` over `K` with a homomorphism `d.toralCenter.torusMap` to
the maximal torus of `d`. Its composite with the torus inclusion is a scheme-theoretic centre
of `G` (`d.toralCenter.isCenter`).

Notation: `Ω` is `SeparableClosure K` and `BC` is base change of commutative group schemes
from `K` to `Ω`. The hypothesis of the main results is
`Subsingleton (characterLattice ((BC).obj d.toralCenter.group))`: the base change of the toral
centre to `Ω` has only the trivial character. For a simply connected group, the number of
these characters is the absolute value of the determinant of the Cartan matrix
(`TitsIndexData.natCard_centerCharacter_eq_cartanDet`, module
`Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan`).

## `Diagonalizable.points_eq_one_of_subsingleton`

```lean
theorem Diagonalizable.points_eq_one_of_subsingleton (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] [Subsingleton Λ] (T : Over (Spec R))
    (x : T ⟶ (Diagonalizable.groupScheme R Λ).X) : x = 1
```

The diagonalizable group scheme `D(Λ)` over `R` with trivial character group `Λ` has only the
identity as a point, on every test scheme `T`. Its points over `T` correspond to monoid
homomorphisms `Multiplicative Λ →* Γ(T)ˣ` (`Corepresented.pointsEquiv`). There is only one such
homomorphism when `Λ` is trivial.

## `TitsIndexData.toralCenter_baseChange_points_eq_one`

If the characters of the toral centre over `Ω` are trivial, then every point of its base change
to `Ω` is the identity. Proof:

1. The toral centre is a closed subgroup of the maximal torus of `d`
   (`TitsIndexData.toralCenter_isClosedSubgroup`). Over `Ω` it is a closed subgroup of the split
   torus of the pinning (`IsClosedSubgroup.baseChange`).
2. A closed subgroup of a split torus is diagonalizable
   (`exists_diagonalizableIso_of_isClosedSubgroup_splitTorus`, module
   `Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups`). This gives an isomorphism
   `eZ` from the base-changed centre to `D(Λ)`.
3. The character group of `D(Λ)` is `Λ` (`DiagonalizableCharacter.evalCharacterEquiv`), and
   characters transport along `eZ` (`characterLattice.congr`). So `Λ` is trivial.
4. A point `x` maps under `eZ` to a point of `D(Λ)`, which is `1` by
   `Diagonalizable.points_eq_one_of_subsingleton`. Mapping back by `eZ⁻¹` gives `x = 1`.

## `TitsIndexData.toralCenter_points_eq_one`

Under the same hypothesis, every point of `d.toralCenter.group` over every `K`-scheme is the
identity. The base change of the full subgroup functor `⊤` of the toral centre to `Ω` is the
full subgroup functor of the base change (`SubgroupFunctor.top_baseChange`). By the previous
result it is `⊥`. `Spec Ω → Spec K` is faithfully flat and quasi-compact
(`fieldExtension_fpqc`), and fpqc base change reflects triviality of subgroup functors
(`SubgroupFunctor.eq_bot_of_baseChange_eq_bot`, module
`Langlands.GroupScheme.Reductive.GroundFieldRadical`). So `⊤ = ⊥`.

## `TitsIndexData.center_points_eq_one`

Under the same hypothesis, every central point of `G` over every `K`-scheme is the identity.
The centre functor of `G` is the range of the toral centre (`d.toralCenter.isCenter`). So a
central point `x` is `y ≫ m` for a point `y` of the toral centre and its map `m` to `G`. Then
`y = 1` and `x = 1`.

## `TitsIndexData.killsCenter_id`

Under the same hypothesis, `KillsCenter (𝟙 G)` (module `Langlands.GroupScheme.Adjoint.Quotient`):
every central point maps to `1` under the identity. This is a restatement of the previous result.

## `IsAdjointQuotient.isIso_of_killsCenter_id`

```lean
theorem isIso_of_killsCenter_id {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (h : KillsCenter (𝟙 G)) : IsIso q
```

Over a field `k`, an adjoint quotient `q : G ⟶ A` of a group whose identity kills the centre is
an isomorphism. The universal property of the adjoint quotient (`IsAdjointQuotient.desc`) gives
`g : A ⟶ G` with `q ≫ g = 𝟙 G`. Then `g ≫ q = 𝟙 A`, because both composites `q ≫ g ≫ q` and
`q ≫ 𝟙 A` equal `q`, and homomorphisms out of `A` are determined by their composite with `q`
(`IsAdjointQuotient.hom_ext`).
