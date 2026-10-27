# Nonzero compact standard maps into actual mirabolic subrepresentations

Author: Worker 237. Worker 658 supplied the precise target specification
and source route.

`Langlands.Whittaker.MirabolicNonzeroCompactMapStatement.{uF}` is a
proposition target for the existential compact-copy input in the proof of
Bernstein–Zelevinsky (1976), Proposition 5.15(c), printed pp.49–50,
specialized to p-adic fields. This module states the assertion; it does not
prove it or assume it as an axiom. It is a derived specialization extracted
from the source's construction and proof, not a verbatim additional
numbered proposition of the source.

## Exact statement

The proposition quantifies over every prime through
`(p : ℕ) (_hp : Fact p.Prime)`, every `F : PadicField.{uF} p`, and then
installs `F.canonicalTopologicalData.topology`. It quantifies over every
`n : ℕ`, every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`,
and every
`W : Subrepresentation (Whittaker.mirabolicSmoothInduced ψ n)`.
Its conclusion is

```lean
W ≠ ⊥ →
  ∃ A : (Whittaker.mirabolicCompactInduced ψ n).IntertwiningMap
    W.toRepresentation, A ≠ 0
```

All these quantifiers are inside the proposition definition. The field
universe `uF` is arbitrary. `Subrepresentation`, its restriction
`W.toRepresentation` to the actual subtype carrier of `W`, and
`Representation.IntertwiningMap` are Mathlib's: an intertwining map is a
complex-linear map commuting with the two actions of the mirabolic group,
and `0` is the zero map. The conclusion is therefore that some
equivariant linear map from the published compact induction into the
actual subrepresentation `W` is not identically zero. Coefficients are ℂ
and both function carriers are those already constructed by
`MirabolicModels`; no independent representation carrier or additional
universe is introduced. The bundled additive character already includes
continuity, nontriviality and values in the unit circle.

There are no hypotheses on finite length, admissibility, irreducibility,
finite generation, derivatives, scalar uniqueness or minimality, and no
supplied embedding. The conclusion does not assert injectivity of `A`, and
it does not assert that `W` contains the canonical compact image
`Whittaker.mirabolicCompactSubrepresentation ψ n`; that containment is the
separate parent target described below.

An internal `letI` supplies `IsTopologicalRing F.Carrier` from the
published canonical valuative relation and local-field certificate by
typeclass inference. This is a derived certificate for the selected
canonical topology, needed to instantiate the models, not another
quantified instance or mathematical hypothesis. The whole telescope is
copied from the parent `MirabolicCompactMinimalityStatement`.

## Conventions: groups, character, models, support and topology

BZ76 §5.1, printed p.44, defines the last-row mirabolic group `P_r`
(matrices whose last row is `(0, …, 0, 1)`) and its full upper
unitriangular subgroup `U_r`. In this module `r = n + 1`; these are the
published `GeneralLinear.mirabolic n F.Carrier` and
`GeneralLinear.Mirabolic.upperUnipotent n F.Carrier`.
Sections 5.5–5.6, printed p.45, choose the nondegenerate character
`Θ(u) = ψ₀(∑ uᵢ,ᵢ₊₁)` of `U`. The published `mirabolicCharacter ψ n` is
this positive adjacent-entry character: the additive-character law turns
the sum into the product of the adjacent-entry values, as certified by
`mirabolicCharacter_eq_product`. No sign or conjugated character is used.

Section 5.7, printed p.45, defines the smooth standard representation
`τ_P = Ind(P, U, Θ)` and the compact standard representation
`τ_P⁰ = ind(P, U, Θ)`. They are respectively
`Whittaker.mirabolicSmoothInduced ψ n` and
`Whittaker.mirabolicCompactInduced ψ n`. Both use the unnormalized
covariance `f(u * g) = Θ(u) * f(g)` for `u ∈ U` and right translation
`(s • f)(g) = f(g * s)`, as in §§2.21–2.22, printed pp.21–22. The
alternative normalization by a modular character mentioned on p.22 is not
used, and no normalization bridge to BZ76's derivative functors appears in
the statement.

Smoothness: §2.21 asks each function to be right-invariant under a compact
open subgroup, while the implementation asks for an open right stabilizer
for each function. In the p-adic setting every open subgroup contains a
compact open subgroup, so the two conditions give the same functions.
Support: §2.22 (with §1.20) asks the support to be compact modulo `U`.
The published compact model consists of smooth covariant functions whose
projected nonzero support in the actual quotient `U \ P`
(`Induction.quotientSupport`) is compact; viewed inside the smooth model
this is the membership condition `mem_mirabolicCompactSubrepresentation`.

Topology: `F.Carrier` carries the published canonical topology of
`Langlands.LocalField.Canonical`. The matrix groups carry the topologies
that the published group constructions induce from it, and `U \ P` carries
the quotient topology, in which the compactness of supports is measured.
The character `ψ` is continuous for the canonical topology.

## Source correspondence

BZ76 writes `n` for the matrix rank; this section writes `r` to avoid a
clash with the Lean variable `n = r - 1`. BZ76 §5.15, printed pp.48–49,
attaches to each smooth representation `π` of `P_r` a filtration by
`P`-submodules `π_i = (Φ⁺)^i (Φ⁻)^i (π)`, embedded as
`π_{r-1} ⊆ π_{r-2} ⊆ … ⊆ π_0 = π`, built from the functors `Φ⁻`, `Φ⁺` of
§§5.11–5.12. (On p.48 the formula is printed `(Φ⁺)^i (Φ⁻)(π)`, without an
exponent on `Φ⁻`; the filtration and the text on p.49, which identifies
`(Φ⁻)^{r-1}(π)`, require `(Φ⁻)^i`. This apparent misprint does not affect
the present target.) The last term `π^{nd} = π_{r-1}` is called the
completely nondegenerate part of `π`. Page 49 then records that
`(Φ⁻)^{r-1}(π)` is realized in the twisted coinvariants `E_{U,Θ}` (via
§2.32), so that `π` is nondegenerate if and only if `π^{nd} ≠ 0`, and that
`π^{nd}` is isomorphic to the direct sum of `dim E_{U,Θ}` copies of the
irreducible representation `τ_P⁰ = (Φ⁺)^{r-1}(1)`.

The proof of Proposition 5.15(c), printed p.50, begins: if `π ⊆ τ_P` and
`π ≠ 0`, then `π` is nondegenerate by definition. Indeed, by §5.7(b) a
representation of `P` is nondegenerate when it admits a nonzero
`P`-homomorphism to `τ_P` (equivalently, by Frobenius reciprocity §2.28,
when `E_{U,Θ} ≠ 0`), and the inclusion `π ⊆ τ_P` is such a homomorphism.
Hence `π^{nd} ≠ 0`. Since `π^{nd}` is a nonzero direct sum of copies of
`τ_P⁰`, the inclusion of one summand, followed by `π^{nd} ⊆ π`, is a nonzero
`P`-homomorphism `τ_P⁰ → π`. This existential consequence is exactly the
present target, with `π` the actual subrepresentation `W`. The source's
summand inclusion is even injective; the target deliberately asks only for
a nonzero map.

The source proof then uses Proposition 5.15(b) — every `P`-homomorphism
`τ_P⁰ → τ_P` is proportional to the standard embedding — to conclude
`π^{nd} = τ_P⁰`. That scalar-uniqueness step, and the identification of the
canonical compact image, are not part of this target.

This paragraph and the previous one explain the source's argument. No Lean
proof of the target is implemented or claimed here; a future proof may
follow a different route, and must prove any normalization bridge it uses
between the unnormalized induction here and BZ76's functors `Φ±`.

## Relation to the parent target

The parent `Langlands.Whittaker.MirabolicCompactMinimalityStatement`, in
`Langlands.Representation.Whittaker.MirabolicMinimalityStatement`, states
that every nonzero `W` contains the canonical compact image
`Whittaker.mirabolicCompactSubrepresentation ψ n`. Its intended assembly
composes a nonzero map given by the present target with the inclusion of
`W` into `mirabolicSmoothInduced ψ n`; scalar uniqueness (BZ76 5.15(b))
identifies the nonzero composite with a nonzero multiple of
`mirabolicCompactInclusion ψ n`, whose image is the canonical compact
image, and this image then lies in `W`. The present module separates only
the existence input; it neither states nor uses scalar uniqueness or the
final containment.

## Why the arbitrary subrepresentation scope is essential

The parent quantifies over every nonzero smooth subrepresentation `W` of
the actual smooth model, with no finiteness assumption, and its assembly
applies the present input to that same `W`. A finite-length or
irreducible-only version would not cover these `W`.

- The standard representation itself has infinite length. For `n = 1`,
  identify `U \ P₂` with `F^×` through the upper-left entry `a`; a function
  `f` in the smooth model is determined by `φ(a) = f(diag(a, 1))`, which is
  invariant under multiplication by some open subgroup of `O^×` and
  vanishes for large `|a|`, while compact support means that `φ` also
  vanishes near `0`. For a character `χ` of `F^×` trivial on an open
  subgroup of `O^×`, the function with `φ(a) = χ(a) 1_{|a| ≤ 1}` lies in the
  smooth model but not in the compact one. On germs at `a = 0`, `U` acts
  trivially and `diag(t, 1)` multiplies this germ by `χ(t)`. So these germs
  span `P`-stable lines in the quotient of the smooth model by the compact
  one, on which `P` acts through pairwise distinct characters; their sum is
  therefore direct. Infinitely many such `χ` exist, so this quotient, and
  hence the standard representation, has infinite length. A finite-length version therefore does not even apply to
  `W = τ_P` or to the many infinite-length subrepresentations between
  `τ_P⁰` and `τ_P`.
- Reducing an arbitrary nonzero `W` to a nonzero finite-length or
  irreducible subrepresentation would require knowing in advance that `W`
  has one. Smooth representations need not have irreducible
  subrepresentations in general; here their existence (the irreducible
  `τ_P⁰` of §5.13(a) sitting inside `W`) is precisely what the
  compact-copy input and the parent provide. Such a substitute would make
  the parent's argument circular.

Since a nonzero map into a subrepresentation of `W` is also a nonzero map
into `W`, the target for all `W` follows from its restriction to cyclic
`W`. That reduction does not make finite length available, because cyclic
subrepresentations of the smooth model need not have finite length. For
`n = 1`, take `φ(a) = g(v(a))` for `|a| ≤ 1` and `0` otherwise, with
`g(k) = 1/k!`. On germs at `0`, `U` and `diag(O^×, 1)` act trivially and
`diag(ϖ, 1)` acts by the shift of `g`. Since `g` satisfies no linear
recurrence with constant coefficients, even eventually, the germs of the
cyclic subrepresentation generated by this function form a free rank-one
module over the Laurent polynomial ring in that shift, which has infinite
length.
The statement simply keeps the arbitrary scope required by the parent.

## Rank-one boundary

The source's matrix rank `r` is `n + 1`, so every positive matrix rank is
retained. In particular `n = 0` gives `P₁ = U₁ = {1}`
(`GeneralLinear.Mirabolic.rankOne_eq_one`). The adjacent-entry product is
empty, so the induced subgroup character is trivial
(`mirabolicCharacter_rankOne`) even though `ψ` itself remains
nontrivial. The quotient is a point and both standard models are
one-dimensional complex spaces with trivial action. A nonzero `W` is then
the whole smooth model, and the target says that some nonzero linear map
from the one-dimensional compact model to it exists. No positive lower
bound on `n` is needed or imposed.

## Scope and other work

The imported mirabolic groups, character transport, evaluation, support
and inclusion laws are elementary implementation definitions and proofs;
they do not establish this assertion. This module constructs no
derivative, Fourier, sheaf or Frobenius-reciprocity machinery and makes no
claim that those prerequisites or this proposition have been proved. The
normalized derivative constructions coordinated in task `8364e73f`, the
finite-length restriction and mirabolic functional/pairing rigidity work
coordinated in task `2644a4fd`, and the coefficient-image, adapter and
Kirillov work in task `22a72323` remain separate. The existing
`MirabolicFunctionalMultiplicityStatement` has irreducibility hypotheses
and a different conclusion. All existing Library Lean/Markdown pairs are
preserved.

## Source and imports

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1–68, English translation. Registered source
  `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
  Printed and one-based PDF page numbers agree. Read §1.20, §§2.21–2.22
  (pp.21–22), §§2.28–2.32 (pp.23–24), §5.1 and §§5.5–5.7 (pp.44–45),
  §§5.11–5.14 (pp.46–48) and §5.15 with its proposition and proof
  (pp.48–50). Printed pp.48, 49
  and 50 were checked visually. The retained source hash was verified.
  No registered erratum for this source was found in the current
  project/Library notes or literature index.

The two imports are
`Langlands.Representation.Whittaker.MirabolicModels`, supplying the actual
groups, character and both induction models through its published
dependencies, and `Langlands.LocalField.Canonical`, supplying the canonical
p-adic topological data. No change to `MirabolicModels` or to the parent
statement is required.
