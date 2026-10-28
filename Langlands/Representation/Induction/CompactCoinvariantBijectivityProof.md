# Bijectivity of the actual compact-induction quotient integral

This module proves
`Langlands.Induction.compactCoinvariantIntegralBijective.{uG,uV}` with type
exactly
[`Langlands.Induction.CompactCoinvariantIntegralBijective.{uG,uV}`](CompactCoinvariantBijectivityStatement.md).
For the supplied compatible quotient measure, the actual linear map
`compactCoinvariantDesc H σ ν hν.right_invariant` is bijective:

\[
 \overline I_\nu:
   (\operatorname{cInd}_H^G\sigma)_G \longrightarrow V_H,
 \qquad
 \overline I_\nu([f])=\int_{H\backslash G}[f(g)]\,d\nu(Hg).
\]

The group universe `uG` and coefficient universe `uV` remain independent.
The source is the actual ambient coinvariant quotient of
`CompactFunctions H σ`, in `Type (max uG uV)`, and the target is
`Representation.Coinvariants σ`, in `Type uV`.

The theorem retains the full published telescope: a Hausdorff locally compact
topological group with the literal compact-open neighborhood basis, a closed
subgroup, the supplied Borel structures and regular two-sided Haar measures,
and every supplied quotient measure finite on compact sets satisfying the
actual `QuotientIntegration.IsCompatible`. The inducing representation is
smooth on an arbitrary algebraic complex module. No coefficient topology,
norm, completeness, dimension restriction, admissibility or finite length
enters the proof. Every imported pair, including the statement and integral
construction, is unchanged.

## Published ingredients

The proof imports two elementary results.

- [`CompactCoinvariantLocalInverseProof`](CompactCoinvariantLocalInverseProof.md)
  proves `compactCoinvariantLocalInverseExists`. It supplies a complex linear
  map \(T:V_H\to(\operatorname{cInd}_H^G\sigma)_G\) whose value on \([v]\)
  is the normalized class of an identity-centered local section, for every
  compact open subgroup whose intersection with \(H\) fixes \(v\).
  Refinement, common-refinement and conjugation arguments establish this
  map and its descent.
- [`CompactLocalSectionSpanningProof`](CompactLocalSectionSpanningProof.md)
  proves `compactLocalSectionSpanning`: the actual compact functions are
  spanned by right translates of those identity-centered sections.
  Its proof uses a compact open subgroup in each function's uniform right
  stabilizer, a finite cover of its compact projected support, and subtraction
  of one local section at a time.

Neither result assumes bijectivity of the integral. The current proof uses
their proved theorems to discharge both explicit arguments of its private
interface-assembly helper. The public theorem has no additional premise.

## The local integral formula

Write
\[
 C_K=\operatorname{compactOpenQuotientOrbit}(H,K),\qquad
 c_K=\operatorname{ofReal}\bigl(\nu(C_K).\operatorname{toReal}\bigr),
 \qquad
 s_{K,v}=\operatorname{compactDoubleCosetSection}(H,\sigma,K,h_K,1,v,h_v).
\]
Here \(K\) is compact open and \(v\) is fixed by \(H\cap K\), encoded by
`fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup`.

The private `quotientCoinvariantSimple_section_one` identifies the actual
projected simple function of \(s_{K,v}\) with the constant \([v]\)
restricted to \(C_K\). On \(C_K\), choose a representative in \(K\) and use
`compactDoubleCosetSection_apply` with the identity element of \(H\).
Outside \(C_K\), the published support inclusion forces the projected value
to vanish. The orbit is open, hence measurable for the supplied Borel
structure.

`compactCoinvariantIntegral_section_one` then applies the existing
`AlgebraicIntegral.integral_indicator_const` to obtain
\[
 I_\nu(s_{K,v})=c_K\,[v].
\]
This computes the existing finite-fiber algebraic integral; no integral
or quotient map is replaced.

The published
`QuotientIntegration.IsCompatible.compactOpenQuotientOrbit_mass` gives
\(0<\nu(C_K)<\infty\) for this supplied measure. Thus its real value is
strictly positive, and \(c_K\ne0\). Positivity and finiteness are consequences
of compatibility, not extra premises or a choice of normalization.

## Surjectivity

The private `exists_section_subgroup` finds a suitable \(K\) for each vector
\(v\). Smoothness gives an open subgroup of \(H\) fixing \(v\). The subtype
topology realizes it as the inverse image of an open set in \(G\) containing
the identity. The literal neighborhood-basis hypothesis supplies a compact
open \(K\) inside that set, so \(H\cap K\) fixes \(v\).

To prove `compactCoinvariantDesc_surjective`, represent an arbitrary inducing
coinvariant by \(v\), using `Representation.Coinvariants.mk_surjective`.
Choose \(K\) as above. The ambient coinvariant
\(c_K^{-1}[s_{K,v}]\) maps to \([v]\), by
`compactCoinvariantDesc_mk`, the local integral formula and cancellation of
the nonzero scalar \(c_K\).

## Injectivity and the closing theorem

The private `compactCoinvariantDesc_bijective_of_local_data` proves that the
map \(T\) supplied by the local-map theorem is a left inverse of
\(\overline I_\nu\). Its characterization is
\[
 T([v])=c_K^{-1}[s_{K,v}].
\]
For a spanning generator \(\rho(g)s_{K,v}\), ambient coinvariants remove
the right translate by
`Representation.Coinvariants.mk_self_apply`. Applying the actual integral,
then \(T\), gives
\[
 T\bigl(\overline I_\nu([\rho(g)s_{K,v}])\bigr)
 =T(c_K[v])
 =c_Kc_K^{-1}[s_{K,v}]
 =[\rho(g)s_{K,v}].
\]

`Submodule.span_induction` extends this equality through zero, addition
and complex scalar multiplication to every compact function.
Surjectivity of the ambient coinvariant projection then extends it to
every ambient coinvariant. A left inverse implies injectivity; the preceding
surjectivity argument gives bijectivity.

Finally, `compactCoinvariantIntegralBijective_of_prerequisites` introduces
the unchanged target's full telescope and applies this algebraic assembly.
The public theorem `compactCoinvariantIntegralBijective` supplies
`compactCoinvariantLocalInverseExists` and `compactLocalSectionSpanning`
at the two independent universes. All six auxiliary theorems are private.

## Original source and provenance

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) **10** (1977), 441–472, §5.17,
printed pp.466–467 (PDF pages 27–28), is the motivating source. It is
registered as `bernstein-zelevinsky-1977-induced-i`, with SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Both cited original pages were read and visually checked.

The source constructs the quotient integral and reduces its isomorphism
argument to the untwisted case with the normal subgroup equal to the identity.
After the renaming of its ambient group, subgroup and coefficient space,
that integral has the formula displayed above. On p.467 the source proves
the isomorphism for regular representations, passes to direct sums, and
uses free resolutions and exactness.

The implemented proof follows a different, internal elementary route:
normalized local-section classes, spanning by their right translates, and
the local integral calculation. The explicitly supplied-measure formulation
and independent-universe topological-group telescope belong to the published
internal statement; they are not attributed verbatim to BZ77. This proof
establishes the ordinary supplied-measure bijectivity assertion. It makes no
normalizer-equivariance, character-twisted comparison, complement-restriction
or normalized parabolic-orbit assertion.
