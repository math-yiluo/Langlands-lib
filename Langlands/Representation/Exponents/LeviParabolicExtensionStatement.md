# Actual nested-parabolic extension through a rational Levi

Original formulation by Worker 1758; Markdown expanded by Worker 1801.
`LeviParabolicExtensionStatement` is a proposition defining a geometric
prerequisite for represented induction in stages. It is unproved in this
file, and nothing here asserts that it has been proved.

## Statement

For every field `k`, connected reductive group scheme `G`, actual rational
parabolic `P = M U` of `G`, and actual rational parabolic `Q = N V` of `M`,
the statement supplies a rational parabolic `R` of `G` whose Levi group
scheme is exactly the original `N`. Every input and output parabolic carries
a rational Levi inclusion, matching geometric unipotent radical and an
isomorphism from the Levi-radical multiplication. The output radical group
scheme is existential; no identification of it with the original `V` or
`U` is asserted.

## Quantifiers

All group schemes are over `Spec k`.

- `k : Type u` is an arbitrary field in an arbitrary universe `u`.
- `G` is a group scheme with `IsConnectedReductive G`: smooth, affine,
  connected, with trivial unipotent radical over the algebraic closure.
- `P`, `M`, `U` with `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` form the outer
  parabolic:
  - `IsParabolicSubgroup p`: `p` is a smooth closed subgroup whose base
    change to the algebraic closure contains a Borel subgroup;
  - `IsRationalLeviSubgroup l`: `P` is affine, `l` is a closed subgroup,
    `M` is connected reductive, and the multiplication with some geometric
    unipotent radical of `P` is an isomorphism;
  - `LeviSubgroup.IsGeometricUnipotentRadical r`: `r` is the greatest
    smooth connected unipotent normal closed subgroup of `P`, both over `k`
    and after base change to the algebraic closure;
  - `IsIso (subgroupMultiplication l r)`: the scheme morphism
    `M × U → P`, `(m, u) ↦ l(m) r(u)`, is an isomorphism for the supplied
    radical `r`.
- `Q`, `N`, `V` with `q : Q ⟶ M`, `n : N ⟶ Q`, `s : V ⟶ Q` form the inner
  parabolic of the original `M`, with the same four kinds of hypotheses:
  `IsParabolicSubgroup q`, `IsRationalLeviSubgroup n`,
  `LeviSubgroup.IsGeometricUnipotentRadical s` and
  `IsIso (subgroupMultiplication n s)`.

No hypothesis relates `Q` to `P` beyond the morphism `q` into the supplied
Levi `M`. Neither input parabolic is required to be proper, so `P = G` or
`Q = M` is allowed. There are no local-field, topology, cocharacter,
standardness, presentation-existence or representation-theoretic
hypotheses.

## Conclusion

There exist group schemes `R`, `W` and morphisms `pR : R ⟶ G`,
`nR : N ⟶ R`, `rR : W ⟶ R` such that `IsParabolicSubgroup pR`,
`IsRationalLeviSubgroup nR`, `LeviSubgroup.IsGeometricUnipotentRadical rR`
and `IsIso (subgroupMultiplication nR rR)` hold. The Levi of `R` is the
original group scheme `N`, not an isomorphic copy. The three compatibility
conclusions use the original morphisms:

- `nR ≫ pR = n ≫ q ≫ l ≫ p`: the composite `N → R → G` equals
  `N → Q → M → P → G`;
- `SubgroupFunctor.range pR ≤ SubgroupFunctor.range p`: the subgroup
  functor represented by `R → G` is contained in that represented by
  `P → G`;
- `SubgroupFunctor.range (q ≫ l ≫ p) =
  SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range pR`: the
  intersection of the subgroup functors represented by `M → P → G` and
  `R → G` is exactly that represented by `Q → M → P → G`.

`SubgroupFunctor.range f` assigns to every test scheme `T` over `k` the
subgroup of `T`-points of `G` that factor through `f`; `≤` and `⊓` are
pointwise on every test scheme. Consequently the last two conclusions are
stronger than containment and equality of rational-point subgroups.

## Provenance

The statement is derived, not a literal transcription of a numbered result.

The geometric source is Borel and Tits, *Groupes réductifs* (1965),
Proposition 4.4(c), printed pp.86–87 / PDF pp.33–34. There `G` is connected
reductive (opening of §4, printed p.85 / PDF p.32), parabolic means
containing a Borel subgroup (4.1), and 4.4(c) says: the parabolic subgroups
of `G` contained in `P` are the semidirect products of the parabolic
subgroups of a Levi subgroup `L` of `P` by `R_u(P)`. The source is
registered as `borel-tits-1965-groupes-reductifs`, SHA256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

Proposition 4.4 is a statement about algebraic groups over an algebraically
closed field. The arbitrary-field rationality framework is Proposition 4.7,
printed p.88 / PDF p.35: for `k`-parabolics `P`, `P'`, the groups
`P ∩ P'`, `R(P ∩ P')` and `R_u(P ∩ P')` are defined over `k`, and
`P ∩ P'` has `k`-Levi subgroups, any two conjugate by a unique element of
`R_u(P ∩ P')(k)`. With `P' = P` this makes `R_u(P)` and Levi
decompositions of `P` rational. The present statement is a `k`-rational,
scheme-theoretic version of the half of 4.4(c) saying that each semidirect
product of a parabolic of the Levi with `R_u(P)` is a parabolic of `G`:
from a rational parabolic `Q` of the supplied rational Levi `M`, it
produces a rational parabolic `R` of `G` inside `P` with `R ∩ M = Q`.

The intended construction is `R = Q ⋉ U`, the inverse image of `Q` under
the projection `P ≅ M ⋉ U → M` given by the supplied multiplication
isomorphism, with radical `W = V ⋉ U` and Levi `N`. A proof must construct
these actual group schemes and morphisms over the original arbitrary field,
verify the rational parabolic, Levi and geometric radical predicates (the
radical over both `k` and its algebraic closure), retain the exact original
`N`, and prove the multiplication isomorphism. It must also establish the
displayed subgroup-functor identities on arbitrary test schemes. The
source's algebraic-group description alone does not supply those Lean
proofs. Descent and the identities on nonreduced test schemes cannot be
replaced by rational-point density, particularly over finite fields.

## Corrections checked

Borel and Tits, *Compléments à l'article « Groupes réductifs »* (1972), §5,
printed pp.274–275 / PDF pp.23–24, registered as
`borel-tits-1972-complements-groupes-reductifs`, SHA256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`.

- (5.5) replaces the Bourbaki reference on the last lines of printed pp.85
  and 86 by `[6; VI, 1.7, Prop. 20]`. The p.86 occurrence is in the proof
  of 4.4(b). This changes only a citation; it does not change 4.4(c) or
  4.7. The other page-line corrections in (5.5) do not concern printed
  pp.86–88.
- (5.1) replaces the second equality (2) of 1965 §3.8 by an inclusion. It
  is unrelated to 4.4 and is not used to infer any equality here.

## Representation-theoretic motivation

Renard (9 July 2026), VI.6.2, printed p.178 / PDF p.184: after embedding an
irreducible representation of `M` into induction from a supercuspidal of a
further Levi of `M`, the proof uses induction in stages to obtain an
induction in `G` from that Levi. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard VI.1.4, printed pp.136–137 / PDF pp.142–143, starts with supplied
nested semistandard parabolics `P ⊂ Q`; it does not literally assert this
inverse geometric existence statement.

## Relation to other declarations

Evaluating the last two conclusions on the identity test scheme gives the
point-image containment and intersection hypotheses of the separate
`LeviParabolicTransitivityStatement`, and the first conclusion gives its
common-Levi embedding equality. This statement provides no functor
isomorphism, cuspidal embedding or finite-length result. The existing
`DynamicLeviParabolicCorrespondenceStatement` starts with a supplied
dynamic presentation, while `RealizedLeviNesting` works with supplied
compatible data; their retained inputs are not discharged here.
