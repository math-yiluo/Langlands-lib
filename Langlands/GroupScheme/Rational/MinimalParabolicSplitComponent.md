# Minimal parabolics and ambient maximality of Levi split components

This internal deduction works over every field `k : Type u`. It turns a
genuinely parabolic compatible cocharacter of an ambient split extension
into centrality in a specified connected reductive subgroup. Applied to a
Levi split component, it proves ambient maximal splitness and constructs
the original torus's actual factor through a specified solvable radical.
The original whole-torus centralizer and the geometric compatible
cocharacter are supplied inputs.

All subgroup inclusions and equalities are assertions on every test
scheme. Whole-torus centralizers also test commutation after every
refinement of the test scheme. No perfectness, splitness of the field,
or density of rational points is assumed.

## Full dynamic parabolics

`Dynamic.parabolic_eq_top_iff_centralizer_eq_top` says that for any smooth
affine group `G` with `HasTrivialUnipotentRadical G` and any actual
cocharacter `χ : Gm ⟶ G`,

```
Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤.
```

The contracting subgroup has an actual closed affine representative.
The published theorem `Dynamic.isUnipotent_unipotentRepresentative`
proves that this representative is unipotent, using the proved
torus-action unipotence result. The published full-parabolic criterion
then applies: when the dynamic parabolic is full, its contracting
subgroup is normal in `G`; smoothness and connectedness of that
subgroup and the trivial-radical hypothesis make it trivial. The limit
decomposition identifies the centralizer with the parabolic.
The converse is the published centralizer-to-parabolic inclusion.
This lemma has no unipotence or dynamic-centralizer reductivity premise.

`Dynamic.range_le_centralizer_of_range_le_parabolic` applies this fact
inside a closed subgroup `i : L ⟶ G`. Here `L` is smooth affine with
trivial ground-field unipotent radical, and `χ` is a cocharacter of `L`.
If the range of `i` lies in `Dynamic.parabolic (χ ≫ i)`, then it lies
in `Dynamic.centralizer (χ ≫ i)`. The closed-subgroup dynamic theorem
identifies `Dynamic.parabolic χ` with the pullback of the ambient
parabolic. The supplied containment makes this pullback full. The
preceding criterion makes the centralizer in `L` full, and functoriality
maps it into the ambient centralizer. No structure hypothesis on the
ambient `G` is required by this lemma.

## Minimality and a split extension

Let `j : P ⟶ G` be an actual minimal rational parabolic, and
`i : L ⟶ G` a closed inclusion with connected reductive `L` whose
all-test range is contained in the range of `j`. Let `a : A.toGrp ⟶ G`
be a homomorphism from a commutative group scheme, and suppose `i`
represents `torusCentralizer a`.

`IsMinimalParabolicSubgroup.represents_torusCentralizer_of_compatible_extension`
takes a split subtorus `b : B.toGrp ⟶ G`, an actual extension map
`f : A.toGrp ⟶ B.toGrp` with `f ≫ b = a`, and a cocharacter `ν` of `B`
satisfying all three of the following conditions:

- `Dynamic.centralizer (groupHom ν ≫ b) = torusCentralizer b`;
- `Dynamic.parabolic (groupHom ν ≫ b)` is an `IsParabolicFunctor`;
- this dynamic parabolic is contained in the range of `j`.

It proves that the same `i` represents `torusCentralizer b`.
Commutativity of `B` puts its range in the centralizer of `a`, so the
published closed-subgroup factor constructs `bL : B.toGrp ⟶ L` with
`bL ≫ i = b`. Minimality of `j` applies to the supplied genuinely
parabolic functor and makes it equal to the range of `j`. It therefore
contains `L`. A connected reductive group has trivial ground-field
unipotent radical. Applying the preceding closed-subgroup lemma to
`groupHom ν ≫ bL` makes `L` centralize `ν`, and the supplied centralizer
equality makes `L` centralize `B`. The reverse containment follows by
centralizer contravariance from the extension map `f`.

The construction uses reductivity of the given `L`. It does not require
constructing a second rational Levi or proving connected reductivity of
a new dynamic centralizer.

## Ambient maximality

`IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_extension`
uses the preceding result when `a : A.toGrp ⟶ L` is a split component
and `b` is an ambient maximal split extension of `a ≫ i`. The original
centralizer hypothesis now concerns `a ≫ i`. The new centralizer
representation constructs an actual central split factor
`bL : B.toGrp ⟶ L` whose composite with `i` is `b`. Monicity of `i`
cancels the ambient composites and gives `f ≫ bL = a`. Maximality of
the split component among central split subtori of `L` makes `f` an
isomorphism. The published transfer across its inverse proves
`IsMaximalSplitTorus (a ≫ i)`.

`IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_compatible_extensions`
assumes that `G` is affine and locally of finite type. Its compatibility
premise supplies a cocharacter with the three properties above for
every ambient maximal split extension and its actual extension map.
The published maximal-split-extension existence theorem supplies such
an extension, and the one-extension result proves ambient maximality.
This is a criterion with an actual extension witness; no inference
from a possibly empty collection of maximal extensions is used.

## The specified solvable radical

`IsRationalLeviSubgroup.splitComponentRadicalWitness_of_minimalParabolic`
specializes to a rational Levi `l : L ⟶ P`, a minimal parabolic
`j : P ⟶ G`, a specified ground-field solvable radical `r : R ⟶ P`,
and a split component `a : A.toGrp ⟶ L`. Assume that `l ≫ j`
represents the whole-torus centralizer of `a ≫ l ≫ j`, and retain
the preceding compatibility premise for ambient maximal split
extensions. Affineness and local finite type of `G` are also retained.

The definition returns an actual map `aR : A.toGrp ⟶ R` from the
original torus, together with

```
aR ≫ r = a ≫ l,
IsMaximalSplitTorus (aR ≫ r ≫ j),
torusCentralizer (aR ≫ r ≫ j) = range (l ≫ j).
```

The published central-Levi-torus radical factor constructs `aR` and its
exact composite. The previous maximality criterion applies to
`i = l ≫ j`: rational Levi and parabolic inclusions are closed, `L`
is connected reductive, and its range lies in `P`. Rewriting by the
exact composite transfers maximality and the original centralizer
equality to the radical factor. A specified geometric solvable radical
supplies the ground-field radical hypothesis as its first conjunct.

## Provenance and remaining inputs

The module is an internal consequence of the imported published
dynamic, reductive, split-extension and central-Levi-radical
constructions. The proof route is the one described above.

The original identification `Z_G(A) = L`, and the existence of a
cocharacter of each maximal split extension whose dynamic parabolic
is genuinely parabolic and lies in `P`, remain geometric obligations.
Dynamic inclusion alone does not imply `IsParabolicFunctor`, and
minimality is used only after that predicate is supplied. This module
does not prove `MinimalParabolicLeviCentralizerStatement`.
