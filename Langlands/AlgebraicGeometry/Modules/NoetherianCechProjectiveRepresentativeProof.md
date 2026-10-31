# Finite projective Čech representatives: proof

`Langlands.AlgebraicGeometry.Modules.noetherianCechProjectiveRepresentative.{u}`
proves `NoetherianCechProjectiveRepresentativeStatement.{u}` over a
commutative noetherian R, for a proper flat morphism π : X → Spec R and a
module M locally isomorphic to the unit. It uses the supplied ordered
affine cover and its cardinality bound n.

The flat-cochain and finite-cohomology theorems for the actual module
`OModulePresheaf.ofModules π M` supply the hypotheses of the published
`boundedFlatComplexProjective`. Above n, there are no increasing cover
indices; the Čech cochain modules are therefore subsingletons. The algebra
theorem chooses one bounded family K of finite projective R-modules and
a chain map φ to the original Čech complex. Its four original-base cycle
and boundary tests are retained in the conclusion of this proof.

For each commutative R-algebra A, the published
`boundedFlatQuasiIsoBaseChange` gives the four tests for the base change of
φ. The geometric cochain base-change theorem supplies degreewise linear
equivalences E from A tensor the original Čech cochains to those of the
actual pulled-back module. The proof defines Θ as E composed with the
base change of φ. The internal `CechProjectiveTransport` lemmas transport
differential commutation and the four tests through E and its inverse.
The pure-tensor formula for E gives the required restriction of the
pullback–pushforward adjunction unit applied to φ. All choices of A use
the same previously chosen K.

## Provenance and adaptation

This proof adapts registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
file
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial.lean`.
The source retains Copyright 2026 Anthropic under Apache License 2.0;
see `licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
Worker 137 made the following changes:

- The source solution is a proof of the host Prop-valued statement, and
  the four φ tests are included before the universal A clause.
- Imports use host modules. The two algebra calls use their published
  `boundedFlatComplexProjective` and `boundedFlatQuasiIsoBaseChange`
  adapters.
- The source's `S32F2` helpers are placed in the host
  `CechProjectiveTransport` namespace; their arguments and proofs are
  retained.
- The `P2M.Util` import and source attribute resets are removed. The file
  uses `autoImplicit false`, finite heartbeat limits of 4,000,000 and
  400,000 for synthesis, and
  `backward.isDefEq.respectTransparency.types false`.
- The two proposition-instance declarations in the source's cochain
  bound and flatness steps use ordinary `let` declarations.

No identity-base geometric identification is needed to recover the φ
tests. The theorem remains a noetherian Čech representative result; it
does not itself prove the universal-perfect-sections theorem.
