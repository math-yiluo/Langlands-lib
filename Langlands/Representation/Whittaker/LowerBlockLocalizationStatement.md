# JPSS arbitrarily small lower-block Whittaker localization

Author: Worker 644. Worker 53 contributed the specification, source rereading,
and the explicit arbitrary-neighborhood requirement. The actual chart and its
proved entry formulas are the published work of Worker 121.

`Langlands.Whittaker.LowerBlockWhittakerLocalizationStatement.{uF,uV}` is a
closed Prop-valued definition of the canonical p-adic specialization of the
lemma in JPSS section 9.2. This module states the localization lemma. Its
proof is a separate obligation.

## Original source and reading

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (2)
(1983), 367–464, section 9.2, printed pages 454–455 (one-based PDF pages
89–90). The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both pages were read visually. Section 2.1, printed pages 385–386 (PDF pages
20–21), was also read visually to verify the representation hypotheses and
the coefficient-image meaning of the Whittaker space.

The project and public-Library `notes/errata` directories are absent in the
checked snapshot. A bounded filename search of the retained literature,
Central-Library, and project/public notes found no source-specific erratum.
The registered source pointer adds no correction to section 9.2. This records
the available errata check, without asserting that no erratum exists elsewhere.

The source's lemma explicitly permits both compact open subgroups to be
arbitrarily small for each fixed input function. Its proof recursively
averages against Schwartz–Bruhat functions and uses a Fourier-transform
identity on printed 455; it leaves the ascending-induction details to the
reader. This proposition includes the lemma's full smallness conclusion;
it does not formalize those proof steps.

## Complete proposition and quantifier order

For every prime `p`, take a field `F : PadicField.{uF} p` and install exactly
`F.canonicalTopologicalData.topology`. Quantify over every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`; this bundle includes
continuity, nontriviality, and unit-circle values.

Take positive integers `a,d,c` and put `b = a+d`, `r = (a+d)+c`. Thus the
source's inequalities `0 < a < b < r` are encoded by the positivity of the
three block sizes. The Lean telescope quantifies over `a d c₀ : ℕ`, assumes
`0 < a` and `0 < d`, and defines `c := c₀+1`. Every positive `c` is covered
by `c₀ = c-1`. This indexing makes the Whittaker predecessor rank
`a+d+c₀` have successor definitionally equal to `r`. It introduces no
transport of the representation, its coefficients, or the chart.

For every complex module `V : Type uV` and every representation
`π : Representation ℂ (GeneralLinear r F.Carrier) V`, assume exactly

```text
IsOfWhittakerType (a+d+c₀) (standardCharacter ψ (a+d+c₀)) π.
```

By the published definition, this means admissibility, finite generation
over the actual complex group algebra acting on `π.asModule`, and a linear
equivalence of the full standard Whittaker-functional space with `ℂ`.
Admissibility includes smoothness. Irreducibility is not required; the
source defines Whittaker type with these hypotheses on printed 385.
The field universe `uF` and representation-carrier universe `uV` are
independent.

For every `W ∈ RankinSelberg.whittakerSet ψ (a+d+c₀) π`, and then for every
pair of sets

```text
Ux ∈ 𝓝 (0 : Matrix (Fin d) (Fin a) F.Carrier),
Uh ∈ 𝓝 (1 : lowerTriangularSubgroup d F.Carrier),
```

there exist an additive subgroup `Ω₁` of that matrix space and a subgroup
`Ω₂` of that actual lower-triangular group, both compact and open in their
respective spaces, with `Ω₁ ⊆ Ux` and `Ω₂ ⊆ Uh`, and there exists
`W₀ ∈ RankinSelberg.whittakerSet ψ (a+d+c₀) π`, such that for every
`g : GeneralLinear a F.Carrier`, every matrix `x`, and every
`h : lowerTriangularSubgroup d F.Carrier`,

```text
W₀(lowerBlockLocalization c g x h) =
  W(lowerBlockLocalization c g 0 1)  if x ∈ Ω₁ and h ∈ Ω₂,
  0                                otherwise.
```

Lean expresses the two cases as two implications under the universal
`g,x,h` quantifiers. The second has premise `¬ (x ∈ Ω₁ ∧ h ∈ Ω₂)`.
Thus the vanishing is global on the chart outside the indicated product,
including points outside either prescribed neighborhood. There is no
restriction on `g` and no restriction on `x,h` in these universal binders.
The subgroups and `W₀` may depend on `W`, `Ux`, and `Uh`, but are selected
before `g,x,h`. The neighborhoods need not themselves be open. This is the
explicit neighborhood formulation of arbitrary smallness for each fixed `W`.

## Actual matrices, inclusions, and topology

The construction is the published
`Langlands.GeneralLinear.lowerBlockLocalization` from
`Langlands.Group.GL.LowerBlockLocalizationCoordinates`:

```text
lowerBlockLocalization c g x h = [[g, 0, 0],
                                 [x, h, 0],
                                 [0, 0, I_c]].
```

Its total rank is the left-associated `(a+d)+c`. The source names the
rectangular space `M(a × (b-a),F)` next to its display. The displayed
lower-left block has `d=b-a` rows and `a` columns. Lean uses that displayed
row/column convention: `x : Matrix (Fin d) (Fin a) F.Carrier`, with `x i j`
in middle-block row `i` and first-block column `j`. No transpose is applied.

The group `lowerTriangularSubgroup d F.Carrier` consists of actual
invertible matrices with entries zero when row index is less than column
index. `Ω₂` is a subgroup of this group, not a subgroup of an abstract
replacement carrier. Its inclusions into the triangular group and then into
`GeneralLinear d F.Carrier` are the ordinary subgroup subtype inclusions.
Likewise `Ω₁` is an actual additive subgroup of the rectangular matrices.

The topology on matrices is the inherited finite product topology of the
canonical field topology. General linear groups have the published matrix-unit
topology, and the triangular group has its subgroup subtype topology. The
compactness and openness of `Ω₂` are in that triangular group. They do not
assert that `Ω₂` is open in the full general linear group. No topology is
chosen independently of these inherited constructions.

The diagonal evaluation is literal `diag(g,I_(d+c))` in consecutive
coordinates. Indeed, specialize the chart's proved
`lowerBlockLocalization_11` through `lowerBlockLocalization_33` at `x=0`
and `h=1`: the diagonal blocks are `g,I_d,I_c`, and all six off-diagonal
blocks are zero. The published embeddings `lowerBlockFirst d c`,
`lowerBlockMiddle a c`, and `lowerBlockLast a d` have natural coordinate
values `i`, `a+i`, and `(a+d)+i`. Thus `I_d` followed by `I_c` is exactly
the final `I_(d+c)` with no coordinate permutation. The statement uses
this chart specialization directly, so no `appendIdentity` cast is needed.

## Coefficient image and scope

Both functions belong to the same actual `whittakerSet` of `π`. This set
is the union of the actual coefficient-model images as the standard
functional varies. Its elements have the form
`g ↦ ℓ(π(g)v)` for a standard Whittaker functional `ℓ` and a vector `v`.
This agrees with JPSS section 2.1, formula (3), printed 386. When the
functional space is one-dimensional, this union is the usual image for
any fixed nonzero functional. No injective realization of `π` in that
space is assumed: the source explicitly allows the coefficient
representation to be a quotient.

The source is over nonarchimedean local fields. Restricting to canonical
p-adic fields, using a successor index for the positive final block,
spelling out the neighborhood quantifiers, and using the published
unchosen coefficient image are formulation choices. The reducible
Whittaker-type scope is already present in the original lemma, rather
than an extension from an irreducible-only statement.

There is no assumed localization operator or measure premise. A proof
successor must construct the coefficients and subgroups by the actual
averaging/Fourier argument or another complete proof, preserving their
arbitrary smallness and the global pointwise formula. Character-coinvariant
heredity does not supply this assertion. This unit supplies no tail-factor
or Laurent-span comparison and does not change the restricted section 5.5
to section 7 to section 9.3 dependency direction retained by Worker 53.
