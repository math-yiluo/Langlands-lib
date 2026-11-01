# Aubert duality from the segment socle to its special head

Author: Worker 320.

`Langlands.Aubert.SegmentSocleHeadStatement F T` states the segment case of
Aubert's Theorem 2.3 for the existing unadjusted alternating operator. It is
a proposition definition. The module supplies no proof of the duality
identity and no existence theorem for either constituent.

## Objects and conventions

Fix an arbitrary prime `p`, a finite p-adic extension
`F : PadicField.{uF} p`, and its supplied `T : F.TopologicalData`. The field
and representation universes `uF` and `uV` remain independent. Put
`v = max uF uV`. A segment `Δ : T.Segment.{v, uF}` has positive cuspidal
rank `r`, positive length `m`, and degree `n = m*r`. Its entries are the
actual supercuspidal classes `ρ, νρ, …, ν^(m-1)ρ`, where
`ν = |det|_F` with residue normalization `|ϖ|_F = q^(-1)`.

The two objects `πZ` and `πS` are actual smooth complex representations of
`GL_n(F)` with carriers in `Type v`. The hypothesis
`T.IsSegmentSocle Δ πZ` says that `πZ` is an irreducible subrepresentation
of the increasing segment induction and that every irreducible embedding
has the same image. The hypothesis `T.IsSegmentHead Δ πS` says that `πS`
is an irreducible quotient of that induction and that every irreducible
quotient map has the same kernel. These are the published strong relations;
neither is replaced by a selected constituent or by equality of labels.
Their supercuspidal representatives may differ: both must represent the
same actual class `Δ.base`, as required by the existing definitions.

The increasing induction uses the upper block parabolic, positive
half-modulus covariance, and right translation. In this convention the
socle is Zelevinsky's `⟨Δ⟩` from §3.1, and the special head is `⟨Δ⟩ᵗ`
from §9.1, also denoted `⟨Δ⟩ᵗ` by Aubert.

## Exact assertion and sign

For every segment and every pair satisfying the two strong relations, set
`x = [πZ]` and `y = [πS]` in
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier`. The
assertion is

    alternatingOperator F T n x = (-1 : ℤ)^(n - m) • y.

These are classes in the existing exact Grothendieck group of actual
finite-length smooth representations, whose relations include every actual
short exact sequence. They are not classes in a finite-dimensional
representation group. The finite-length proof for each object comes from
the irreducibility clause of its strong relation and the published
`SmoothRep.hasFiniteLength_of_isIrreducible`. No finiteness or admissibility
hypothesis is added. The natural subtraction in `n - m` is appropriate
because `r ≥ 1` and `n = m*r ≥ m`. Segment positivity already excludes rank
zero.

`alternatingOperator` is the unadjusted endomorphism

    D_GL_n = ∑ B, (-1 : ℤ)^(n - B.length) • i_B r_B.

Aubert's Definition 2.1 instead adjusts this operator on each cuspidal
support component. Remark 2.2 states that on the segment socle
`D = (-1)^(n - m) D_GL_n`. Theorem 2.3 identifies the adjusted `D` with
the involution that sends `⟨Δ⟩` to `⟨Δ⟩ᵗ`. Multiplying by the same sign
therefore gives exactly the displayed unadjusted identity. No support sign
is suppressed or replaced by `(-1)^(m - 1)`.

## Source correspondence and proof boundary

| Lean content | Original passage |
| --- | --- |
| Increasing-product socle convention and its strong uniqueness | Zelevinsky 1980 §3.1, printed pp.180–181 (PDF pp.17–18), using Proposition 2.10. |
| Special head as the unique irreducible quotient of the same increasing product, or socle of the decreasing product | Zelevinsky 1980 §9.1, printed p.197 (PDF p.34); Aubert 1995, beginning of printed p.2185 (PDF p.7). |
| Adjusted versus unadjusted sign | Aubert 1995 Definition 2.1 and Remark 2.2, printed p.2184 (PDF p.6). |
| Segment exchange identity | Aubert 1995 Theorem 2.3 and its final displayed conclusion, printed p.2185 (PDF p.7). |

The cited pages were read in the retained originals; Aubert pp.2184–2185
and Zelevinsky pp.181 and 197 were also checked visually. The retained
Aubert audit and citation guide was read for the applicable corrections.
The incorrect tensor-product identification on p.2184 is not used: product
Levi classes and ambient GL classes remain distinct. The operator uses the
published normalized induction and Jacquet maps.

Aubert's printed proof of Theorem 2.3 uses the polynomial-ring structure of
Zelevinsky Corollary 7.5 and the multisegment expansion of Proposition 9.13.
The present statement does not import these conclusions. Its later proof
in the upstream analytic classification route must respect that route's
independence restrictions and supply independent lower-level inputs.
Reading this source identity does not establish such a proof.

In particular this module proves no irreducible-image theorem, signed
effectivity result, Jacquet compatibility, segment existence, or analytic
square-integrability classification. The reverse identity for the special
head is not a second assertion here; after this identity is proved, it can
be derived using the separately published involutivity theorem and integer
linearity.

## Retained sources and dependencies

- Aubert 1995, *Dualité dans le groupe de Grothendieck des représentations
  lisses de longueur finie*, Trans. Amer. Math. Soc. 347, pp.2179–2189.
  Registered ID `aubert-1995-duality`; SHA-256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
  [Retained original](</home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf>).
- Zelevinsky 1980, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13,
  pp.165–210. Registered ID `zelevinsky-1980-induced-ii`; SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  [Retained original](</home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf>).

The source correction map and the upstream independence boundary are
recorded in [the published Aubert route note](../../../notes/henniart/aubert-duality-route.md)
and its linked retained audit. The direct Lean imports are the published
`Aubert.AlternatingOperator`, `Smooth.IrreducibleRealization`, and
`Classification.Segments`. The exact-class packaging and explicit universe
telescope are formal translations of these existing constructions.
