# Proof: the multiplicative part of a commutative algebraic group

`Langlands.GroupScheme.commutativeMultiplicativePartCharacterization` proves exactly
`Langlands.GroupScheme.CommutativeMultiplicativePartCharacterizationStatement.{u}`, imported
unchanged from
[`Langlands.GroupScheme.Commutative.MultiplicativePartCharacterizationStatement`](MultiplicativePartCharacterizationStatement.md),
for every universe `u` (Milne, *Algebraic Groups* (2017), Note 16.17 and the remark after the
proof of Theorem 16.13, p.329).

The setting is as follows. `k : Type u` is a field. `G` is a group scheme over `Spec k` with
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and `[IsCommMonObj G.X]`. There are
`s : S ⟶ G` and `q : G ⟶ Q` with `IsClosedSubgroup s`, `IsMultiplicativeType S`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q` and `IsUnipotent Q`. Under these
hypotheses the theorem proves all five parts of the statement:

1. the largest subgroup of multiplicative type;
2. the smallest subgroup with an fppf quotient onto a unipotent group;
3. base change to every field `K : Type u`;
4. `Smooth G.X.hom → Smooth S.X.hom`;
5. `ConnectedSpace G.X.left → ConnectedSpace S.X.left`.

No hypothesis is added. `Q` is not assumed affine or of finite type; this is derived. The
characteristic and perfectness of `k` are arbitrary. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Files

- [`MultiplicativePartQuotient`](MultiplicativePartQuotient.md): the given quotient is
  affine and of finite type, multiplicative type survives every field extension, and
  Milne 14.18 applied to a specified fppf quotient.
- [`MultiplicativePartHopf`](MultiplicativePartHopf.md): over an algebraically closed field,
  characters of `S` lift to group-like elements of the coordinate Hopf algebra of `G`. Their
  torsion is controlled by reducedness (smooth `G`) or connectedness of that algebra.
- `MultiplicativePartCharacterizationProof` (this file): field-extension transport and
  assembly.

## Proof

First, `quotient_affine_finiteType` gives `IsAffineHom Q.X.hom`.

**Part 1.** If `h : H ⟶ G` has `IsMultiplicativeType H`, then
`range_le_of_isUnipotent_quotient h hH s q hq hQ` gives `range h ≤ range s`: `h ≫ q` is
trivial by Milne 14.18, so `range h` lies in the kernel of `q`, which is `range s`.

**Part 2.** If `h : H ⟶ G` is a closed subgroup with an fppf quotient `q' : G ⟶ Q'` and
`IsUnipotent Q'`, then `Q'` is affine (`quotient_affine_finiteType h hh hq'`). The same lemma,
with `S` in place of `H`, gives `range s ≤ range h`.

**Part 3.** Let `K` be a field over `k` and `b = Spec.map (CommRingCat.ofHom (algebraMap k K))`.
`isMultiplicativeType_baseChange hS K` gives `IsMultiplicativeType S_K`. For `h : H ⟶ G_K` with
`IsMultiplicativeType H`:

- the base change of `q` is an fppf quotient with kernel `range (s_K)`, by the Library's
  `RelativeRoot.IsFppfQuotient.baseChange` and `SubgroupFunctor.range_baseChangeHom`;
- `Q_K` is affine (`DynamicBaseSmoothConnected.isAffineHom_baseChange`);
- `Q_K` is unipotent (`IsUnipotent.baseChange`, which needs `Q` affine).

So `range_le_of_isUnipotent_quotient` applies over `K` and gives `range h ≤ range (s_K)`.

**Parts 4 and 5** (`MultiplicativePart.smooth_connected`). Let `L = AlgebraicClosure k` and
`p = ringExpChar L`. Base change along `Spec L ⟶ Spec k`, which is surjective, flat and
quasi-compact (`fieldExtension_fpqc`):

- `S_L` is of multiplicative type, hence `eS0 : S_L ≅ D_L(N)` for a finitely generated `N`
  (`MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`);
- `G_L` and `Q_L` are affine and `G_L` is commutative (`Functor.isCommMonObj_obj`);
- `s_L` is a closed subgroup (`IsClosedSubgroup.baseChange`), `q_L` is an fppf quotient by it,
  and `Q_L` is unipotent.

The published `Diagonalizable.diagonalizableSmoothConnectedCriteria L p N` (Milne 12.5) states:

- `D_L(N)` is smooth if and only if `N` has no nonzero element killed by `p`;
- `D_L(N)` is connected if and only if every torsion element of `N` is killed by a power
  of `p`.

The scheme isomorphism underlying `eS0` transports smoothness (the structure map of `S_L` is
the isomorphism followed by that of `D_L(N)`) and connectedness.

- If `G` is smooth, so is `G_L` (`DynamicBaseSmoothConnected.smooth_baseChange`).
  `eq_zero_of_smooth` gives the criterion for `N`, so `S_L` is smooth. Smoothness descends to
  `S` along the fpqc map (`smooth_of_baseChange`, Rational/UnipotentRadicalProperties).
- If `G` is connected, its unit section `η[G.X].left` makes it geometrically connected
  (`Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section`). So `G_L` is
  connected (`connectedSpace_baseChange` in this file, through
  `DynamicBaseSmoothConnected.connectedSpace_baseChange`).
  `exists_pow_nsmul_eq_zero_of_connected` gives the criterion for `N`, so `S_L` is connected.
  Connectedness descends to `S` along the surjection `S_L ⟶ S` (`connectedSpace_of_baseChange`).

## Comparison with the source route

Milne's route for parts 4 and 5 uses `G_{k^a} = G_u × G_s` (Theorem 16.13(b)), so that `S_{k^a}`
is a quotient of `G_{k^a}`. That theorem is the subject of a separate, still unproved Library
target. The proof here avoids it. Over `k^a`, each character of `S` extends to `G`, by the
grading of the coordinate Hopf algebra by the characters of `S`. An extension that is trivial
on `S` factors through the unipotent quotient, so it is trivial. Reducedness or connectedness
of the coordinate ring of `G_{k^a}` then rules out the torsion that would make `D(N)`
non-smooth or disconnected. Parts 1–3 follow Milne's indicated route (14.17, 14.18).
