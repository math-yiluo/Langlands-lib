# The Borel axioms of the relative Tits system from the Bruhat decomposition

This internal auxiliary module supports the proof task for
`Langlands.GroupScheme.RelativeTitsSystemStatement`. It combines two internal modules.
`Langlands.GroupScheme.Rational.RelativeTitsCoxeterReduction` reduces the relative Tits system,
under a Coxeter realization of the relative Weyl group, to the predicate
`HasRelativeTitsBorelAxioms`. `Langlands.GroupScheme.Rational.RelativeTitsBruhatReduction`
derives the kernel and generation axioms from the rational Bruhat decomposition. Two Borel axioms
remain: the multiplication axiom and the nondegeneracy axiom. This module groups them as the new
predicate `HasRelativeTitsCellAxioms`.

The module proves none of `RelativeWeylCoxeterStatement`, `StandardParabolicEndpointsStatement`,
`RationalBruhatStatement` or the cell axioms. It therefore does not prove
`RelativeTitsSystemStatement`; it reduces that statement to these four inputs. It adds no
axioms.

## The predicate `HasRelativeTitsCellAxioms`

`HasRelativeTitsCellAxioms i ν` is an internal packaging predicate, not a statement from the
literature. Write `B = standardParabolicPoints i ν ∅`, `N = normalizerPoints i`,
`π = QuotientGroup.mk'` from `N` onto `relativeWeylGroup i = N(k)/Z(k)` and
`S = simpleRelativeReflections i ν`. The predicate is the conjunction of two fields of
`Langlands.Group.IsTitsSystem B N π S`, copied literally:

1. `mul_mem_cell`: for `s ∈ S`, normalizing points `n, m` with `π n = s` and `b ∈ B`, the
   product `n * b * m` lies in `cell B π (π m) ∪ cell B π (s * π m)`;
2. `conj_not_le`: for `s ∈ S` and every normalizing point `n` with `π n = s`, some `b ∈ B` has
   `n * b * n⁻¹ ∉ B`.

Here `Langlands.Group.TitsSystem.cell B π w` is the set of products `b * n * b'` with
`b, b' ∈ B` and `π n = w`, so it uses all representatives of `w`.

## Results without structural hypotheses

- `hasRelativeTitsBorelAxioms_iff`: `HasRelativeTitsBorelAxioms i ν` is equivalent to the
  conjunction of `ker π = B.subgroupOf N`, `B ⊔ N = ⊤` and `HasRelativeTitsCellAxioms i ν`. Both
  sides unfold to the same conjunction, so the proof is `Iff.rfl`.
- `HasRelativeTitsBorelAxioms.hasRelativeTitsCellAxioms`: the Borel axioms contain the cell
  axioms (projection).
- `HasRelativeTitsSystem.hasRelativeTitsCellAxioms`: a relative Tits system satisfies the cell
  axioms. It composes the projection above with
  `HasRelativeTitsSystem.hasRelativeTitsBorelAxioms`.

## Results under the Bruhat decomposition

The next three results assume two hypotheses:

- `hB`: the minimal endpoint identity `B = (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))`,
  that is, `P_∅(k) = P(ν)(k)`;
- `hBr : HasRationalBruhatDecomposition i ν`.

They are:

- `hasRelativeTitsBorelAxioms_of_bruhat`: with `hcell : HasRelativeTitsCellAxioms i ν`, the
  Borel axioms hold. The kernel axiom is `relativeTits_ker_eq_of_bruhat i ν hBr`, which needs
  only `hBr`. The generation axiom is `relativeTits_sup_eq_of_bruhat i ν hB hBr`. Both come from
  `RelativeTitsBruhatReduction`. The cell axioms are `hcell`.
- `hasRelativeTitsBorelAxioms_iff_of_bruhat`: hence the Borel axioms are equivalent to the cell
  axioms.
- `HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem_iff_hasRelativeTitsCellAxioms`: if also
  `h : HasRelativeWeylCoxeterSystem i ν` and `hT : IsSplitTorus T.toGrp`, then
  `HasRelativeTitsSystem i ν ↔ HasRelativeTitsCellAxioms i ν`. It composes
  `HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem_iff` (from
  `RelativeTitsCoxeterReduction`) with the previous equivalence.

## Statement-level reduction

`relativeTitsSystemStatement_of_statements` assumes `RelativeWeylCoxeterStatement.{u}`,
`StandardParabolicEndpointsStatement.{u}` and `RationalBruhatStatement.{u}`. It also assumes
`hcell`: for every field `k`, connected reductive `G`, maximal split torus `i` and generic
cocharacter `ν`, `HasRelativeTitsCellAxioms i ν`. The quantifiers and `haveI` instances are
those of the target statement. Under these assumptions it proves
`RelativeTitsSystemStatement.{u}`.

The proof applies `relativeTitsSystemStatement_of_relativeWeylCoxeter` from
`RelativeTitsCoxeterReduction`, so it only has to supply `HasRelativeTitsBorelAxioms i ν` for
fixed data. The first conjunct of the endpoint statement says that the standard parabolic
subgroup scheme for `∅` equals the dynamic parabolic of `ν`. Rewriting
`standardParabolicPoints` with it gives `hB`. The Bruhat statement gives `hBr`, `hcell` gives
the cell axioms, and `hasRelativeTitsBorelAxioms_of_bruhat` concludes.

`RelativeTitsSystemStatement.hasRelativeTitsCellAxioms` is the converse: the target statement
gives the cell axioms in the same generality, by `HasRelativeTitsSystem.hasRelativeTitsCellAxioms`.
So, given the three structural statements, the target statement is equivalent to the cell
axioms for all such data.

## Provenance

These results are internal and derived. They compose published definitions with two internal
reduction modules; they assert no new structural theorem. The classical source is Borel–Tits,
*Groupes réductifs* (1965), checked against the scan in the central library. Theorem 5.15
(printed pp. 100–101) is the Bruhat decomposition `G(k) = ⋃ P(k) w P(k)`, here the hypothesis
`RationalBruhatStatement`. Proposition 5.16 (printed p. 101) gives, for a fundamental reflection
`r`, (i) `r P(k) {w, r w} P(k) = P(k) {w, r w} P(k)` and (ii) `r P(k) r ≠ P(k)`. These are the
contents of the two fields of `HasRelativeTitsCellAxioms`. The Lean field (i) states only the
inclusion `n B m ⊆ B m B ∪ B s m B` with Weyl classes. The Lean field (ii) states that
`n B n⁻¹` is not contained in `B`. The remark after 5.18 (printed p. 101) states that 5.15 and
5.16 verify Tits's axioms. In this module, the cell axioms are a hypothesis and are not proved.
