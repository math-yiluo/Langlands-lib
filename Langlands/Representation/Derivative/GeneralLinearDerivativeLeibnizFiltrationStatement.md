# The actual derivative Leibniz filtration in all ranks

This module states, but does not prove,
`Langlands.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`.
It concerns the actual published smooth complex representations over a supplied
`p`-adic field and its supplied topology. The carrier universe is independent of
the field universe. There are no positivity, admissibility, irreducibility,
finite-dimensionality or finite-length assumptions.

The source is Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I*, Annales scientifiques de l'École Normale Supérieure (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The positive-rank
assertion is Corollary 4.14(c), printed p.458 (one-based PDF p.19), also stated as
Lemma 4.5, printed p.455. Sections 1.8–1.11, 3.1–3.5, 4.3 and 4.12–4.14 supply
the conventions described below. Rank-zero factors use the Library's internal
tensor extension, rather than a positive partition with a zero block.

The registered PDF has SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The source audit read printed pp.444–445, 450–452 and 454–458, including the
normalization formulas and the page images for case (III) and 4.13–4.14.
A bounded search in project notes, supplied Library notes and literature
Markdown found no BZ77-specific errata entry. This records the search's extent,
not a claim that no errata exist.

## Concrete indices and functors

`leibnizIndices a b d` is the finite antidiagonal of `d`, filtered by the two
rank bounds. `mem_leibnizIndices` characterizes membership as
`i ≤ a ∧ j ≤ b ∧ i + j = d`. The named lemmas
`leibnizIndices_left_le`, `leibnizIndices_right_le`, `leibnizIndices_sum`
and `leibnizIndices_rank` provide the two bounds, sum equation and equality
`(a-i)+(b-j)=(a+b)-d`. `LeibnizIndex` is the corresponding finite subtype.
The membership equivalence follows by unfolding the filter and antidiagonal;
the rank equation and singleton boundary lemmas use natural-number arithmetic.
These are internal indexing helpers, not additional results attributed to BZ77.

`leibnizSource T ψ a b d hd` is definitionally

```lean
T.binaryNormalizedProductFunctor a b ⋙
  generalLinearDerivative T ψ (a+b) d hd ⋙ SmoothRep.toRep
```

Its object lemma `leibnizSource_obj` is proved by reflexivity and evaluates at
`(A,B)` to the actual derivative of the published binary product in `Rep`.
There is no comparison representation between this value and the literal
derivative.

For a feasible index `x=(i,j)`, `leibnizPiece T ψ a b d x` is definitionally
the product of `generalLinearDerivative T ψ a i hi` and
`generalLinearDerivative T ψ b j hj`, followed by
`T.binaryNormalizedProductFunctor (a-i) (b-j)`, the published smooth
`generalLinearRankCast T hrank`, and `SmoothRep.toRep`. Its
`leibnizPiece_obj` lemma is proved by reflexivity. The rank cast occurs in
`SmoothRep` before forgetting smoothness. Its existing reflexivity, object,
composition and heterogeneous morphism lemmas remain applicable; no new
transport construction is introduced.

Both functors have source
`SmoothRep ℂ GL_a × SmoothRep ℂ GL_b` at carrier universe `uV` and target
`Rep ℂ GL_((a+b)-d)` at carrier universe `max uF uV`. The product accounts for
the increase of the carrier universe; differentiation preserves that universe.
The helpers use the supplied `T.topology` and the bundled continuous nontrivial
additive character `ψ`.

## The filtration assertion

For every `ψ`, all `a,b,d : ℕ` and every proof `hd : d ≤ a+b`, the proposition
asserts an equivalence from `LeibnizIndex a b d` to `Fin` of its cardinality,
and `IsGluedFrom` for the source and the pieces enumerated by its inverse.
Every feasible index appears exactly once. Equal or zero representations at
distinct indices are retained as separate entries. The gluing relation permits
any permutation and imposes no canonical order.

Here `IsGluedFrom` unfolds to `HasOrderedFiltration` after a permutation, and
then to an actual `RepFunctorFiltration`. Its increasing chain consists of
actual invariant submodules at every object, preserved by every functor map,
beginning at zero and ending at the whole source. Each successive quotient is
the actual quotient of one step by the preceding step, with its descended
maps. The graded identifications are natural isomorphisms of functors.
This states more than an objectwise list or an equality of classes.

The helper theorem
`GeneralLinearDerivativeLeibnizFiltrationStatement.filtration` takes the
assertion as a hypothesis and extracts an actual filtration and an enumeration
whose individual grades have the required natural isomorphisms. Its proof
unpacks the definitions and absorbs the gluing permutation into the enumeration.
It supplies no evidence for the assertion itself. A consumer may evaluate the
filtration using its own object-filtration adapter, without any consumer import
in this module.

## Source correspondence and boundaries

BZ77 1.10 treats subfunctors and natural exact sequences, and 1.11 defines
gluing by a finite filtration with graded quotients up to permutation. The
positive-rank statement therefore uses that actual filtration, not merely the
representation-ring consequence stated after Lemma 4.5.

BZ77 3.5 defines positive mirabolic derivatives as `Ψ⁻ ∘ (Φ⁻)^(d-1)`, and
4.3 first restricts a general-linear representation to the mirabolic subgroup;
its order-zero derivative is the identity. Source `P_m`, for `m>0`, is
`GeneralLinear.mirabolic (m-1) F.Carrier`. There is no `P_0` in this module.
The published `generalLinearDerivative` implements exactly these operations
and the necessary proved rank transports. The range `j=0,…,d` in 4.14(c)
is understood with derivatives of order beyond their source rank set to zero.
The feasible index set removes
precisely those zero-beyond-rank entries; it never removes a feasible piece
that happens to be zero.

The positive-rank product is source case (I) of 4.12, with upper block
unipotent, normalized positive-half induction covariance and right
translation. The minus functors retain the inverse-half determinant
normalization of 1.8(b). The future proof route must also preserve the
case (III) epsilon `ν(m₂)^(-1/2)` in the right mixed product. No residual
character twist is inserted into a grade.

When `a=0` or `b=0`, the product is the Library's lifted ordinary tensor
product with the positive-rank group acting through its corresponding factor.
For two zero ranks it retains both carrier spaces in their tensor product.
This all-rank assertion extends the positive-partition source assertion by
tensor and localization quotient algebra. It does not identify a GL_0
representation with the tensor unit and does not assume a finite-dimensional
or one-dimensional carrier.

`leibnizIndices_zero` proves that order zero has exactly `(0,0)`;
`leibnizIndices_top` proves that order `a+b` has exactly `(a,b)`.
At top order the target rank is zero and the unique piece still contains
the binary product of the two actual top-derivative carriers. Neither is
assumed one-dimensional. For `a=b=0` the two boundary descriptions coincide.
The statement also includes all intermediate orders for either zero factor.

## Imports, proof boundary and provenance

The direct project imports are `Induction.BinaryProduct`, `Derivative.Iteration`
and `Filtration.Definitions`; the direct Mathlib import provides finite
natural-number antidiagonals. The new helpers merely compose these existing
constructions, enumerate feasible indices and unpack the filtration definition.
No existing statement pair is changed.

The general Leibniz assertion remains unproved. BZ77 printed p.458 derives
4.14(a) from 4.13(b), 4.14(b) from (a) and 4.13(c), and 4.14(c) from (a),
(b) and 4.13(a). An eventual proof must establish and audit these general
restriction, minus, exactness, tensor and filtration-composition inputs
independently. A statement definition, source citation or pending proof task
does not establish any of them. In particular, no supercuspidal derivative
formula, top finrank-one result, segment formula, segment existence,
irreducibility criterion, classification or Whittaker-finiteness conclusion
is assumed here.

## Transitive project import audit

At authoring, the actual import closure comprises this entry and the following
68 project modules; names below are relative to `Langlands`. Mathlib and Lean
imports provide the underlying algebra, topology, categories and tactics.

```text
Group.GL.Basic
Group.GL.BlockModulus
Group.GL.Blocks
Group.GL.Mirabolic
Group.GL.MirabolicOppositeIntersection
Group.GL.MirabolicRadical
Group.GL.Nonarchimedean
Group.GL.NonarchimedeanStatement
Group.GL.NormalizedCharacter
Group.GL.OppositeBlocks
Group.GL.Padic
Group.GL.PadicBlocks
Group.GL.RankMaps
Group.GL.RankReindex
Group.GL.UpperUnipotent
HarmonicAnalysis.Basic
LocalField.Canonical
LocalField.Definitions
LocalField.Normalization.Definitions
LocalField.Normalization.Proof
LocalField.Normalization.Statement
LocalField.Topology
Representation.Category.Basic
Representation.Category.Twist
Representation.Derivative.Iteration
Representation.Derivative.MirabolicCharacter
Representation.Derivative.MirabolicMinus
Representation.Dual.Definitions
Representation.Filtration.Definitions
Representation.Induction.BinaryProduct
Representation.Induction.BlockFactors
Representation.Induction.Definitions
Representation.Induction.Parabolic
Representation.Jacquet.Coinvariants
Representation.Jacquet.Localization
Representation.Jacquet.PositiveCharacter
Representation.Jacquet.SmoothTwist
Representation.MatrixCoefficient.Definitions
Representation.MatrixCoefficient.LawsProof
Representation.MatrixCoefficient.LawsStatement
Representation.Smooth.Admissibility.CofinalProof
Representation.Smooth.Admissibility.CofinalStatement
Representation.Smooth.Definitions
Representation.Smooth.SmoothPart.BasicProof
Representation.Smooth.SmoothPart.BasicStatement
Representation.Smooth.SmoothPart.Definitions
Representation.Smooth.Transfer.PullbackProof
Representation.Smooth.Transfer.PullbackStatement
Representation.Smooth.Transfer.SubquotientProof
Representation.Smooth.Transfer.SubquotientStatement
Representation.Tensor.Finite
Representation.Tensor.OneFactor
Representation.Twist.AdmissibilityProof
Representation.Twist.AdmissibilityStatement
Representation.Twist.AlgebraProof
Representation.Twist.AlgebraStatement
Representation.Twist.ContinuousCharacterProof
Representation.Twist.ContinuousCharacterStatement
Representation.Twist.Definitions
Representation.Twist.RealPower
Representation.Twist.SmoothProof
Representation.Twist.SmoothStatement
Representation.Twist.SubquotientDefinitions
Representation.Twist.SubquotientProof
Representation.Twist.SubquotientStatement
Representation.Whittaker.Algebraic
Representation.Whittaker.GeneralLinear
Topology.Nonarchimedean.Subgroup
```

This closure follows the actual Lean imports, including `Tensor.Finite` through
`Induction.BlockFactors`. In particular it includes
`Whittaker.GeneralLinear` and `Whittaker.Algebraic` through
`Derivative.MirabolicCharacter`. Those two modules were read in full: they
construct the additive/Whittaker characters, functionals and models and prove
elementary properties; they supply no Whittaker-finiteness conclusion. The
closure has no segment, classification or cuspidal-support consumer module.
A bounded scan of these project sources found no references to the explicitly
excluded consumer conclusions in the task's inherited restrictions.

The mathematical dependencies of the new proofs are limited to finite-set
membership and natural-number arithmetic for indexing, reflexivity for the two
object lemmas, and unfolding the published gluing definition for the conditional
filtration extractor. None proves the general Leibniz assertion or uses a
supercuspidal derivative, segment, classification, product-irreducibility or
Whittaker-finiteness conclusion. The eventual proof of the assertion must audit
its own complete direct and transitive proof dependencies against every
inherited exclusion; this construction/import audit does not replace that
future proof audit.
