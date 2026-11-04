# Actual compact-picture intertwining families

Worker 200. Derived constructions supporting Waldspurger IV.1.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082. The registered source
`waldspurger-2003-plancherel` has SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
IV.1, printed pp.276–278 (PDF pp.42–44), gives the fixed compact picture,
conjugation of the operator by restriction, the representative square, and the
smooth-dual integral. The positive induction convention is I.3, printed p.243
(PDF p.9).

## Actual compact identifications

The setting is the existing canonical `SmoothRep` framework over a locally
compact nonarchimedean group. The two actual semidirect decompositions have the
same Levi `M`. The same chosen compact open subgroup `K` satisfies Iwasawa
factorization for each parabolic. Closedness of each parabolic and radical,
continuity of each actual Levi projection and of the supplied positive
characters, and unimodularity of each actual radical's conjugation modulus
are explicit. The latter inputs identify full-parabolic and positive
Levi-inflated normalization; their actual standard rational-point discharge
belongs to the existing rational-unipotent constructions.

`UnramifiedLeviInduction` is the actual positive Levi-normalized induced
representation of an actual unramified twist. It introduces no new carrier.
`unramifiedLeviInductionCompactEquiv` first uses the inverse of the existing
normalization comparison, then the existing unramified normalized restriction
equivalence. Its target is the single fixed `CompactInductionPicture h K A`
of the untwisted inducing representation. The evaluation theorem is literal
restriction to `K`. The inverse-extension theorem uses the actual positive
normalized twisted action on the actual parabolic factor.

Naturality compares an actual inducing equivalence, twisted at the current
parameter and then induced, with the fixed pointwise compact-picture map
`compactInductionPictureEquiv`. Its proof is function extensionality. The inverse
square follows by injectivity of the actual compact equivalence and its two
inverse identities. The carrier universes of the two inducing representations
are independent, also independently of the group and character-index universes.

## Operators and original integrals

`compactIntertwiningOperator` is precisely the linear composite

`res_target ∘ J ∘ res_source⁻¹`

for an actual ambient intertwiner `J`. Its value at a compact point is the
value of `J` on the actual extended source at that point. Its representative
square follows from the actual ambient square, the inverse source square and
the target restriction square. It is not a newly chosen operator satisfying a
desired analytic conclusion.

The standard-integral constructions additionally assume the existing Borel
structures, fixed regular two-sided Haar measures on the target radical and
intersection, an actual compatible measure on the nonnormal intersection
quotient, closed Levi, Hausdorff ambient group, and the explicit actual
`SquaredModulusCompatibility` premise. Its general geometric proof remains
open here.

`standardCompactOperator` uses the existing `fullSourceIntertwiner` inside
this composite. At each parameter it requires an equality of the actual
smooth-dual integral domain with the whole induced source. This equality
includes both absolute scalar convergence and representability by a vector of
the original inducing carrier for every source vector and ambient argument.
It is an analytic prerequisite needing proof, not an authorized structural
assumption for program completion.

The evaluation theorem identifies this map at every compact point with the
original selected standard integral. The specification extends its output
back to `G` by the actual target compact equivalence and retains the original
`HasIntegral` relation at every point of `G`. Its proof cancels the target
compact equivalence with its inverse and applies the original full-source
specification. The standard representative square uses the proved naturality
of the actual full-source integral; the two full-domain equalities are displayed
separately.

## Rationality condition and limits

`StandardCompactRationalOn` is a proposition-valued definition applying
`UnramifiedOperatorFamily.IsRationalOperatorOn` to these actual maps on a
specified parameter subset. The full-domain equalities are arguments, so the
definition does not conceal convergence inside an arbitrary operator choice.
One denominator serves all inputs, and the target vectors of each finite
numerator expression are fixed elements of the actual target compact picture.

This is an algebraic restriction predicate. An application to Waldspurger's
open orbit domain must separately supply openness and orbit descent, and the
identification of the evaluation-generated scalar algebra with the actual
algebraic-torus coordinate algebra. No finite-length convergence cone or proof
of rationality, continuation, composition scalar or Plancherel conclusion is
asserted. There is no verified same-`K` reductive Iwasawa realization in this
module; the actual decompositions and both factorizations remain explicit.
