# Zariski local lifting of geometric normalizer points

`Langlands.GroupScheme.splitNormalizerGeometricLocalLifting.{u}` proves the
unchanged published proposition
`Langlands.GroupScheme.SplitNormalizerGeometricLocalLiftingStatement.{u}`.
For every commutative ring `R` and all the split reductive data specified in
that proposition, a full normalizer point `n` over an algebraically closed
field point `x : Spec k → Spec R` has a normalizer representative `nV` on a
Zariski neighbourhood `V` of the image of `x`. The proof constructs the
factorization `a : Spec k → V` and proves
`(a ≫ nV) * n⁻¹ ∈ range t` using actual torus points. Normalizer and
centralizer assertions are subgroup-functor assertions on all test schemes.
The theorem is universe-polymorphic and imposes no additional hypothesis on
`R`, including no reducedness, connectedness, localness or finiteness condition.

This is an internal derivation from the published split-torus automorphism,
transporter, self-centralization and cocycle results. The source provenance
of the target, including Conrad's Proposition 5.1.6, Corollary 5.1.11 and
Corollary 5.2.13(2), is recorded in the unchanged statement companion. The
implemented proof uses smooth affine transporters and Zariski local
triviality of split-torus cocycles. Worker 799's
`Torus.LocalTransporterDescent` supplies the local descent helper; its paired
Markdown explains that construction. All other mathematical inputs are
imported by their published Lean names.

## Local transporter lemmas

`PointwiseSchemeAction.exists_local_transporter_of_smooth` starts with a
split commutative torus `T`, two maps `j₁,j₂ : T → G`, a monomorphic `j₂`, and
an all-test transporter `x` over a smooth affine morphism `U → S`. It assumes
that the full centralizer of `j₂` equals its actual range. For any point `s`
in the image of `U`, it produces a transporter on an open neighbourhood of
`s`. Smoothness makes the image `W` open. Restricting `U → S` over `W` gives
an affine, flat, surjective morphism. The proof base-changes the two maps,
the transporter, the split torus and the centralizer equality to `W`.
`exists_local_transporter_of_cover` then descends the transporter Zariski
locally. Finally the canonical pullback point equivalence and the open
immersion `W → S` express this section over an open of `S`. Surjectivity is
only used over the open image, so no nonemptiness of unrelated fibres is
asserted.

`PointwiseSchemeAction.exists_local_transporter_of_fieldPoint` works over
an arbitrary affine base `Spec R`, with `G` smooth and affine, and the same
monomorphic self-centralizing split torus. It assumes an actual field-valued
all-test transporter. A chosen splitting identifies its source with the
diagonalizable group of the free lattice `I → ℤ`. The proof applies
`relativeTransporterScheme`, `relativeTransporterHom_isTransporter` and
`smooth_relativeTransporterScheme` from `Torus.RelativeTransporterSmooth`.
The given field point factors through this affine transporter by
`exists_relativeTransporter_factor_iff`; the algebra structure on the field
is obtained from `Spec.preimage`. Thus the base point lies in the smooth
transporter's image, and the previous lemma supplies the required local
transporter. This helper works for any field, without an algebraic-closure
assumption.

`PointwiseSchemeAction.IsTransporter.mem_torusNormalizer` says that a
transporter from `σ ≫ t` to `t`, for an actual automorphism `σ` of the
commutative torus, belongs to the full normalizer on its test scheme. On
every refinement the two normalizer conditions are witnessed by applying
`σ` and `σ⁻¹` to the torus point. The proof uses the transporter equation,
the inverse-automorphism identity and group cancellation. This lemma
requires no smoothness or maximality assumption.

## Proof of the exact target

For the coordinate torus of the target, reductivity gives smoothness and
affineness of `G`. Closedness makes the inclusion monomorphic. The published
`splitTorusCentralizer_eq_range_of_fibrewiseMaximal` identifies its full
centralizer with its actual range over the original base.

The canonical pullback point equivalence transports the given normalizer
point to the identity test scheme over `Spec k`.
`mem_torusNormalizer_baseChange_iff` and
`torusNormalizer_carrier_base` identify it with an actual normalizing
automorphism `σ₀` of the pulled-back torus. The published
`IsSplitTorus.automorphism_fieldBaseChange_surjective` extends `σ₀` to an
automorphism `σ` over the original base; that theorem applies to an arbitrary
base and field morphism. The normalizing equation becomes an all-test
transporter equation from `σ ≫ t` to `t`, first over the field and then over
the original base via the point equivalence.

The field-point helper produces an open `V` and a transporter `nV` for the
same pair of maps. The normalizer lemma proves that `nV` is a full
normalizer section. Since `Spec k` has one point, its image is contained in
`V`; the open-immersion lift constructs `a` explicitly. The transporter
difference identity `IsTransporter.inv_mul_mem_torusCentralizer` gives
`n⁻¹ * (a ≫ nV)` in the centralizer, hence in `range t` by
self-centralization. Conjugating by the given normalizer point preserves
that range and yields exactly `(a ≫ nV) * n⁻¹`, the orientation required by
the unchanged target.

The supplied fibrewise root datum and rank-one free root-space hypotheses
remain quantified exactly as in the published proposition. The implemented
argument does not need them. All scheme refinements and actual range
witnesses are retained throughout, including over nonreduced test schemes.
