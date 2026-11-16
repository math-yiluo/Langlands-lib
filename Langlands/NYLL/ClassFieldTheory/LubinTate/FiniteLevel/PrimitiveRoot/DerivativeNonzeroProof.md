# Nonzero derivative of the primitive polynomial (M341.009)

`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_derivative_ne_zero`
proves the fully applied published target
`standardLubinTatePrimitivePolynomialOverField_derivative_ne_zeroStatement hπ n`.
It asserts that the formal derivative of
`standardLubinTatePrimitivePolynomialOverField F π n` is nonzero.

The theorem preserves the source telescope: independent universes `u v`;
implicit `{K : Type u} [Field K]`;
implicit `{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}`
and `{π : F.valuationSubring}`; explicit
`(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))`; and explicit
`(n : ℕ)`. The hypothesis `hπ` is supplied positionally to the target's
`_hπ` binder. This applies in every characteristic allowed by the local
field package, including positive characteristic.

## Implemented proof

Put `q = Nat.card F.residueField` and let `A` be the image of the
`n`th standard Lubin–Tate polynomial iterate under the coefficient map
`algebraMap F.valuationSubring K`. The private formula helper unfolds
the published primitive-polynomial definitions and maps their powers,
addition and constant coefficient, giving
`standardLubinTatePrimitivePolynomialOverField F π n = A ^ (q - 1) + C π`.

The published theorem
`standardLubinTatePolynomialIterate_derivative_eval_zero F π n`
gives the valuation-ring identity for the iterate derivative at zero.
Commuting differentiation and evaluation at zero with the coefficient
map gives `A.derivative.eval 0 = (π : K) ^ n`. The uniformizer hypothesis
implies `(π : K) ≠ 0`, so this evaluation is nonzero and hence
`A.derivative ≠ 0`. If `A` were zero, its derivative would be zero;
therefore `A ≠ 0` as well.

Differentiating the formula leaves the product
`C ((q - 1 : ℕ) : K) * A ^ ((q - 1) - 1) * A.derivative`.
The published theorem `residueFieldNatCard_sub_one_cast_ne_zero F`
makes the first factor nonzero. The other two factors are nonzero by
the preceding argument and nonvanishing of powers in the polynomial
ring over a field. Thus the product is nonzero. All subtraction in
these exponents is natural-number subtraction.

The private assembly helper accepts the two published conclusions,
and the public theorem supplies them from
`IterateDerivativeEvalZeroProof` (M341.002) and
`ResidueCardSubOneNonzeroProof` (M341.008). Both prerequisites are
imported from their published Library modules. The two helpers are
private; the only new public declaration is the requested exact theorem.

## Source and adaptations

Original source: Naganori Yamaguchi, NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
M341.009, lines 147–188, supplies the theorem and derivative argument;
M341.004, lines 79–87, supplies the formula calculation. The shared
section telescope is at lines 32–42. Registered sources are
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

Worker 569 made these adaptations:

- extracted the requested proof, qualified the namespace with
  `Langlands.NYLL`, and stated its type using the unchanged published
  Prop-valued target;
- replaced the original broad imports with the target, the two published
  prerequisite proofs and the polynomial derivative API;
- kept the M341.004 formula calculation as a private helper named
  `primitivePolynomialOverField_formula`;
- moved the derivative calculation to the private helper
  `derivative_ne_zero_of_inputs`, supplied by the two imported theorems;
- derived `A ≠ 0` from `A.derivative ≠ 0`, replacing the original
  iterate-monicity argument and removing that dependency;
- added an explicit `change` to unfold the target for the calculation,
  retained the remaining coefficient-map and differentiation argument,
  and replaced the module documentation.

The target and all imported Lean/Markdown pairs are preserved. The
original copyright, author and Apache-2.0 header are retained.
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are unchanged.
