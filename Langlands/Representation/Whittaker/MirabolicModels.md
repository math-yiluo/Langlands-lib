# Standard Whittaker induction on the actual mirabolic group

Author: Worker 353.

This module specializes the published smooth and compact induction constructions
to the actual mirabolic subgroup and its actual full upper unipotent subgroup.
It constructs the standard representations of P from Bernstein–Zelevinsky
(1976), §5.7, printed p.45. The unnormalized covariance convention is
`f(u * g) = θ(u) * f(g)`, and the action is right translation
`(s • f)(g) = f(g * s)`. The definitions of induction are those of §§2.21–2.22,
printed pp.21–22, rather than the normalized variant mentioned on p.22.

The coefficients are complex numbers. The matrix coefficient ring
`F : Type uF` is arbitrary with `CommRing F` and `TopologicalSpace F`;
the models and translation representations additionally assume
`IsTopologicalRing F`. In particular all topological fields in any universe
are covered. The carriers have their natural universe `Type uF`, because
they are complex-valued functions on a group in `Type uF`; no universe equation
restricts F and no general representation carrier is an input. All natural
numbers `n`, including zero, are allowed, and the matrix rank is `n + 1`.
No admissibility, finite length, irreducibility or uniqueness hypothesis is used.

## Character and scalar action

`mirabolicCharacter ψ n` composes the published `standardCharacter ψ n`
with `GeneralLinear.Mirabolic.upperUnipotentEquiv`. Here
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F` is the existing continuous,
nontrivial unitary additive character. The equivalence retains the same matrix.
`mirabolicCharacter_apply` exposes the composition, and
`mirabolicCharacter_eq_product` proves that its complex value on `g` is

`∏ i : Fin n, ψ.complex (g.val.val.val i.castSucc i.succ)`.

The three subtype projections forget unipotent membership, mirabolic membership,
and matrix invertibility. This is exactly the adjacent-entry product in the
unchanged `WhittakerTypeKirillovStatement`. The proof reuses
`standardCharacter_eq_product`, whose additive-character law identifies the
product with the character of the superdiagonal sum. The sum is the convention
of BZ76 §§5.5–5.6, p.45. `mirabolicCharacter_rankOne` gives the trivial character
when the product is empty. `mirabolicCharacterContinuous` transports the
published continuity certificate along the continuous subgroup equivalence.

`mirabolicCharacterRepresentation` is literally the existing
`Langlands.characterRepresentation` of this unit-valued character on ℂ.
Its `_apply` lemma gives multiplication by the complex character value.

## The actual function spaces

`MirabolicSmoothFunctions ψ n` abbreviates `Induction.SmoothFunctions` for the
unipotent subgroup inside `mirabolic n F` and the scalar representation just
constructed. Its vectors are actual covariant functions with a single open
right stabilizer for each entire function. `mirabolicSmoothInduced` abbreviates
the existing right-translation representation on this space.
`mirabolicEval` evaluates the actual function; `mirabolicEval_def` explicitly
reduces it to `f.val.val g`. The `_translate`, `_covariance`, and
`_covariance_product` laws give the action and both character conventions directly.

`mirabolicCompactSubrepresentation ψ n` is exactly the existing
`Induction.compactSubrepresentation` within this same smooth representation.
Its membership lemma `mem_mirabolicCompactSubrepresentation` is the equivalence
with compactness of `Induction.quotientSupport` of `mirabolicEval ψ n f`.
That support is the image of the nonzero support in the actual quotient U\P,
whose classes are `U * g`. No arbitrary support predicate or isomorphic copy of
the compact subrepresentation is substituted.

`MirabolicCompactFunctions` and `mirabolicCompactInduced` are the corresponding
published compact-induced carrier and action.
`mirabolicCompactInclusion` is the canonical intertwining inclusion into the
smooth model. Its `_apply` lemma identifies it with the subtype projection,
and `_injective` proves injectivity. `mirabolicCompactEval_def` reduces compact
evaluation to `f.val.val.val g`, `_translate` gives right translation, and
`_covariance` gives the same left covariance. `mirabolicCompactInclusion_eval`
identifies evaluation before and after inclusion. The two `_smooth` theorems
reuse the published smoothness certificates of the induction constructions.
These evaluation, inclusion and transport proofs are elementary implementation
laws derived from the imported definitions.

In BZ76's locally profinite setting, a uniform open stabilizer can be replaced by
an open compact subgroup contained in it, as in §2.21. The generic Library
induction uses the uniform-open-stabilizer formulation and compact projected
support. This module does not prove a compact-support lifting theorem or the
adapter from the ambient compact-set and ambient open-subgroup clauses of the
inline Kirillov statement. Those adapters belong to the parent task.

JPSS (1983), §2.1, pp.385–386, gives the functional covariance and
right-translation Whittaker functions. Its §2.2, p.386, defines K₀(ψ) as smooth
covariant functions on P with compact support modulo N. Those are the consumer
conventions followed here. The JPSS inclusion K₀(ψ) ⊆ K(π;ψ), BZ minimality,
nonvanishing of these models, and all derivative theorems are outside this
construction unit and are neither assumed nor proved.

## Sources and dependencies

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Math. Surveys 31:3
  (1976), 1–68; `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Read §§2.21–2.22, pp.21–22 (PDF indices 20–21), and §§5.1–5.7,
  pp.44–45 (indices 43–44).
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  Convolutions*, Amer. J. Math. 105 (1983), 367–464;
  `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Visually read §§2.1–2.2, pp.385–386 (PDF indices 19–20).

Both retained Central-Library source hashes were checked. No relevant erratum
was found in the available literature or public notes.
The imports reuse the companion actual group construction,
`Whittaker.PrerequisiteInterfaces` (and hence the published standard character
and its product formula), and `Induction.Definitions` (including the published
scalar twist construction). All existing Lean/Markdown pairs remain unchanged.
