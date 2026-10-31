# Rational canonical-dual base change and involution transport

This internal construction transports an actual rational homomorphism
to the constructed dual by actual abelian-scheme pullback followed by
the prescribed canonical dual comparison. It also derives the rational
duality square and preservation of the involution equation from the
explicit integral naturality obligation.

`rationalDualBaseChangeHom` is a rational-linear map on the existing
rational Hom groups. It sends `lam` to
`comp0 (rationalBaseChangeHom b lam) (homToHom0 E_A.hom)`, where
`E_A` is the existing `dualAbelianBaseChangeIso` with all displayed
construction parameters. Thus the target is the constructed dual of
the actual pulled-back abelian scheme. No arbitrary target
identification or new rational Hom convention is used.

Its application formula is definitional. On `homToHom0 lam` it is
the rational inclusion of the existing integral
`dualAbelianBaseChangeMap lam`. The proof uses the actual pure-tensor
pullback formula and compatibility of integral inclusion with
composition. Rational-unit multiples are preserved by linearity.

`dualHom0_baseChange_of_naturality` assumes precisely
`DualAbelianBaseChangeNaturalityStatement`, as well as the pointwise
dual-map additivity proofs for the original and pulled-back pair.
It states

`comp0 (rationalBaseChangeHom b (dualHom0 f)) (homToHom0 E_A.hom) =
  comp0 (homToHom0 E_B.hom) (dualHom0 (rationalBaseChangeHom b f))`.

The rational dual maps use the actual integral dualization at their
displayed endpoints. The proof is tensor-product induction. For a
pure tensor it applies the defining formulas of actual rational
pullback, rational dualization and rational composition, then uses
the assumed integral naturality square. The addition case uses
linearity and bilinearity. This does not prove the integral square.

`IsInvolutionCompatible.baseChange_of_naturality` applies this square
at an endomorphism. For an actual ring with involution `R`, the new
action is the original ring action composed with the actual unital
endomorphism pullback `rationalBaseChangeEnd b A`. The new dual-valued
map is exactly `rationalDualBaseChangeHom lam`. The proof pulls back
the original compatibility equation, reassociates actual rational
compositions, uses the rational duality square for the starred action
element, and reassociates again. The original and changed endomorphism
additivity proofs are explicit.

The base schemes are arbitrary in one universe; the involution
algebra may have a separate universe. All seven dual-construction
inputs, universal-family base-change, comparison group compatibility,
and existence, geometry, inverse line bundles and evaluation data
at the required endpoints remain explicit. These are the same
actual constructions used by the integral target.

Worker 57 implemented the rational extension following Worker 144's
integral-square and involution-transport analysis. This is internal
algebraic compatibility of existing constructions, with no additional
literature theorem asserted. The integral naturality theorem remains
a named hypothesis. No polarization, faithfulness after pullback,
pointed level structure, successive-base coherence, unconditional
dual existence or representability is established here.
