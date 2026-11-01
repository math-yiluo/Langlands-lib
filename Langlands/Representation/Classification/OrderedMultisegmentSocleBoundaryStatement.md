# Elementary boundary statements for ordered segment-socle products

Author: Worker 700.

`Langlands.Classification.OrderedMultisegmentSocleBoundary.{uF,uV} F T`
groups three elementary inputs for the ordered-socle proof. Its outer
telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. The field universe `uF` and carrier universe `uV`
are independent, and the definition installs the supplied `T.topology`.
This module states the inputs as one proposition; it proves none of them.

The first conjunct concerns every actual
`d : T.SegmentProductDatum.{max uF uV,uF} 0`. Given its supplied
nonprecedence order and actual segment-socle blocks, it asserts
`d.IsZelevinskySocle d.induced`. The output is the datum's own normalized
upper product. The inherited socle relation requires irreducibility, an
injective intertwiner, and equality of images for every irreducible
embedding. This clause includes the empty datum. It does not assert any
positive-rank ordered-socle result.

The second conjunct concerns every natural rank and every actual datum in
the same saturated carrier universe. Actual segment-socle blocks imply
`Nontrivial d.induced`, independently of ordering. The assertion concerns
the full normalized smooth upper induction with right translation.
It retains every supplied block and also includes the empty tensor
product. It asserts no finite length, admissibility or homogeneity.

The third conjunct explicitly assumes the published proposition
`CuspidalIntegralTwistFreeness.{uF,uV} F T`: an integral norm twist fixes a
cuspidal datum exactly when its exponent is zero. For every actual finite
family of segments with carrier universe `uV` and every `i < j`, a supplied
nonprecedence ordering then implies
`(segments j).base ≠ (segments i).last.twist 1`. This is the endpoint
separation needed by Zelevinsky's Theorem 6.2. Repeated segments and the
empty family are allowed. The proposition does not prove freeness or
homogeneity, nor does it remove this explicit freeness premise.

These are derived internal formulations, rather than a literal three-part
theorem in the literature. The rank-zero clause is motivated by the
rank-zero boundary of the parent target, Zelevinsky's Theorem 6.1(a).
The Library's empty block tensor and full-group induction identify that
product with the complex scalar line. The intended nonzero-product proof
uses a nonzero tensor of block basis vectors and a compact local section
whose value at the identity is that tensor. These explanations record
provenance and a prospective proof route; they do not supply proofs here.
The endpoint implication is the elementary adjoining-interval case of
the actual precedence relation: under integral-twist freeness, a later
base equal to the earlier endpoint twisted by one forces earlier-to-later
precedence, contradicting the given order.

The registered original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), 165–210, literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Section 4.1, printed p.184 / one-based PDF21, gives linked, juxtaposed and
preceding segments. Theorem 6.1(a), printed p.188 / PDF25, states
ordered-product socle existence; Theorem 6.2 on the same page uses the
displayed endpoint condition. These original passages were read, and the
formula-bearing pages were visually checked. The full retained PDF hash
matches registration. Bounded searches in the literature index,
prescribed errata locations and relevant classification source notes
found no applicable correction. No global absence of errata is claimed.

The only imports are the existing multisegment statement module and
integral-twist-freeness statement module. The former contains several
other classification propositions; importing their definitions proves
none of them. No such proposition is assumed by this boundary statement.
The first two conjuncts use only the actual datum, block and socle
relations; the third adds precisely the stated freeness premise.
No derivative result, classification conclusion, exhaustion, product
irreducibility criterion or conditional head-assembly conclusion is
used as a proof input. The future exact proof of this boundary
proposition must receive its own validation and independent review.
