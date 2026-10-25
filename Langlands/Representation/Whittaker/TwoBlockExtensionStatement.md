# JPSS two-block Whittaker extension

Author: Worker 357.

`Langlands.Whittaker.TwoBlockWhittakerExtensionStatement` is a closed
Prop-valued definition of the p-adic specialization of JPSS Proposition 9.1.
This contribution states the extension; it does not prove it.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Section 9.1 begins on printed 452, states the proposition on printed 453,
and finishes its proof on printed 454 (one-based PDF pages 87–89).
These scanned pages were read visually. The opening fixes Whittaker-type
representations of ranks `r₁`, `r₂` and the **upper** parabolic of type
`(r₁,r₂)`. The displayed proposition puts the matrix of rank `r₂` in
the leading coordinates and has the determinant exponent `+r₁/2`.
Section 2.1, printed 385–386 (PDF 20–21), supplies the Whittaker-type
definition and explicitly describes the Whittaker coefficient representation
as a quotient. Those pages were also read visually. A bounded local check
found no source-specific erratum in the retained literature or public notes;
this is not a claim that no erratum exists elsewhere.

## Complete proposition

For every prime `p`, every `F : PadicField.{uF} p` with its canonical
topology, every nontrivial continuous unitary additive character `ψ` of
`F.Carrier`, and every `a b : ℕ`, put `A = a+1` and `B = b+1`.
For arbitrary complex modules `V₁ : Type uV₁` and `V₂ : Type uV₂`, take
representations `π₁` of `GL_A(F)` and `π₂` of `GL_B(F)`.
The two representation hypotheses are precisely
`IsOfWhittakerType a (standardCharacter ψ a) π₁` and
`IsOfWhittakerType b (standardCharacter ψ b) π₂`.

Lift the two carriers and conjugate their actions exactly as in
`Langlands.RankinSelberg.InducedTailLFactorStatement`:

```text
π₁' acts on ULift.{uV₂} V₁
π₂' acts on ULift.{uV₁} V₂
πᵢ' = (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp πᵢ
ξ = F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks A B … …) (Shahidi.pairFamily π₁' π₂')
```

Then, for every `W₂ ∈ RankinSelberg.whittakerSet ψ b π₂` and every
`Φ : HarmonicAnalysis.SchwartzBruhat (Fin B → F.Carrier)`, there exists
`W ∈ RankinSelberg.whittakerSet ψ (a+1+b) ξ` such that, for every
`g ∈ GL_B(F)`,

```text
W(diag(g,I_A)) = W₂(g) * Φ(lastRow(g)) * |det(g)|^(A/2).
```

The absolute value is `F.canonicalTopologicalData.normalizedAbs`,
normalized by the canonical residue cardinality. The final factor is
`Real.rpow` with real exponent `((a+1 : ℕ) : ℝ)/2`, then included in `ℂ`.
It is a positive real power, with no complex branch choice or integer
division. `SchwartzBruhat` is the published space of compactly supported
locally constant complex functions, with the product topology on the row
space. `RankinSelberg.lastRow g` is `j ↦ g (Fin.last b) j`.
There is no measure argument or self-dual measure premise.

## Coordinates, induction and universes

The induction is the literal canonical normalized induction from the upper
parabolic with ordered blocks `(π₁,π₂)`. The tail is the second inducing
block `π₂`. In the formula, however, its matrix `g` occupies the **first**
`B` coordinates, with `A` final identity coordinates.

The published `appendIdentity b (a+1)` maps `GL_(b+1)` into
`GL_(b+(a+1)+1)`. The local `e` in the proposition is explicitly
`GeneralLinear.reindex (finCongr (by omega))` from that rank to
`(a+1)+(b+1)`, the literal induction rank. `finCongr` preserves each
index's natural-number value. Reindexing simultaneously in both coordinates
therefore leaves every matrix entry in the same numerical position.
This is an arithmetic rank transport, not the block-swap permutation:
it does not turn the leading `B` coordinates into the last `B`.
The published `appendIdentity_entry` verifies the diagonal block formula.
The Whittaker predecessor rank `a+1+b` has successor definitionally equal
to the induction rank.

The canonical positive half modulus on the Levi `(g₁,g₂)` is
`|det(g₁)|^(B/2) * |det(g₂)|^(-A/2)`. This follows from the actual
upper modulus `|det(g₁)|^B / |det(g₂)|^A`, with its positive square root,
as exposed by the published two-block induction constructions. It is
consistent with the source's **positive** `A/2` in the extension formula:
printed 453 first has the covariance factor `|det(g)|^(-A/2)`;
the substitution on the `B × A` matrix integration variable contributes
`|det(g)|^A`, leaving `|det(g)|^(A/2)`.
The source's block-swap and Fourier construction explains why the second
inducing block appears in the leading coordinates. No inducing blocks are
swapped in the definition of `ξ`.

The three universe parameters `uF`, `uV₁`, `uV₂` are independent.
The lifts place the two block carriers in `max uV₁ uV₂`; the induced
carrier has universe `max uF uV₁ uV₂`. The lifted action sends
`ULift.up v` to `ULift.up (πᵢ g v)` and is conjugated through the
explicit inverse linear equivalences. These are constructed carrier
changes, with no hypothesis equating universes. `W₂` remains a coefficient
of the original representation `π₂`.

## Coefficient images and remaining proof obligations

The published Whittaker-type predicate means admissibility, finite
generation over the group algebra, and a Whittaker functional space
linearly equivalent to `ℂ`. It includes reducible representations.
The published `whittakerSet` consists of functions in the actual images
of the coefficient maps `v ↦ (g ↦ ℓ(π(g)v))`, as `ℓ` ranges over all
standard Whittaker functionals. For a one-dimensional functional space
these images agree with the usual space from any nonzero functional.
This uses coefficient images rather than an assumed faithful realization;
the coefficient map may have a kernel.

In particular, the conclusion supplies a coefficient of the actual
induction `ξ`. It does not merely supply a left-equivariant function on
the full group. No chosen extension of a functional, full Whittaker type
of `ξ`, model equivalence, injective coefficient map, irreducibility, or
extension property is an input.

The original proposition is stated over nonarchimedean local fields.
Its restriction here to canonical p-adic fields, the explicit universe
lifts, the arithmetic rank transport, the use of unchosen coefficient
images, and the real-power implementation are internal formulation
choices. They do not represent additional source theorems.

The proof successor must construct the open-cell vector, justify its
covariance and smoothness, implement the block-swap and Fourier
calculation with the stated sign and measure change, and prove that the
result lies in the actual Whittaker coefficient image of `ξ`.
In particular, the source's reduction to Whittaker models must be justified
through the actual quotient maps for reducible inputs, including the
needed passage under induction. Source terminology and Whittaker
heredity alone do not prove these steps or this pointwise extension.
This statement contribution supplies none of those proofs.
