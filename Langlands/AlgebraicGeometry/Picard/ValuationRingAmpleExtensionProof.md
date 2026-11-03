# Ample extension from the generic fibre over a valuation ring

`Langlands.AbelianScheme.valuationRingAmpleExtension` proves exactly the
published proposition
`Langlands.AbelianScheme.ValuationRingAmpleExtensionStatement.{u}`.
Its entire type is that proposition, with arbitrary universe `u` and no
additional outer hypotheses. The published statement is imported unchanged.

The result covers every valuation domain `R`, including fields and
valuation domains of arbitrary rank, every supplied fraction field `K`
with its supplied algebra structure, and every Library abelian scheme
`A / Spec R`. Its sole geometric premise is the existence of an ample
line bundle on the actual generic fibre. The conclusion provides an
actual line bundle on `A.X.left` whose actual pullback along
`pullback.fst` is ample in the Library sense.

## Implemented proof

The helper `valuationRingAmpleExtension_of_twoAxis` takes the published
`ValuationRingTwoAxisExtensionStatement.{u}` and
`FieldAmpleDiagonalCorrespondenceStatement.{u}` as explicit hypotheses.
Write `b : Spec K → Spec R` for the map induced by the supplied algebra
structure, `B = A × Spec K` for the actual base change,
`π : B → A` for its first projection, and `q : B × B → A × A` for the
canonical product base-change map over the corresponding bases.

The field input supplies an actual line bundle `D` on the self-product
of `B`, with trivial pullbacks to both unit axes and ample diagonal
pullback. The extension input supplies an actual line bundle `E` on the
self-product of `A`, together with an actual module-sheaf isomorphism
`q* E ≅ D`. The constructed total bundle is `M = diagonal_A* E`.

Pullback extensionality and the two projection identities prove the
morphism equality

`π ≫ diagonal_A = diagonal_B ≫ q`.

The module-sheaf pullback-composition and pullback-congruence
isomorphisms, followed by the pullback of `q* E ≅ D`, give an actual
isomorphism

`π* (diagonal_A* E) ≅ diagonal_B* D`.

The proof transports the supplied diagonal ampleness along the inverse
of this isomorphism with `LineBundle.IsAmple.of_iso`. This preserves the
whole Library predicate, including `CompactSpace` and the affineness of
the whole generation open. The conclusion uses the actual
`LineBundle.pullback π` of the constructed `M`.

The final theorem applies this helper to the published unconditional
proofs `valuationRingTwoAxisExtension.{u}` and
`fieldAmpleDiagonalCorrespondence.{u}`. Thus neither helper hypothesis
remains in its type. Both inputs use the same universe and the supplied
fraction field directly.

## Provenance and scope

Worker 477 implemented this internal categorical assembly. Its inputs
are the published actual-bundle results in
`ValuationRingTwoAxisExtensionProof` and
`FieldAmpleDiagonalCorrespondenceProof`, and ampleness transport from
`AmpleIsoProof`. Their companions describe their proofs. The field proof
constructs a difference correspondence with ample diagonal pullback;
the extension proof constructs a total bundle using the published
integral-fibre projectivity theorem. The present module composes those
results through the actual diagonal square.

This is a derived proof of the published weakening of Raynaud's
Theoreme XI 1.4 described in the target's companion. It does not claim
symmetry, algebraic equivalence to the original bundle, relative
ampleness of the total bundle, or projectivity of the abelian scheme.
The constructed total bundle need not extend the original ample bundle.
The proof adds no rank, noetherian, completeness, henselian,
projectivity, polarization or symmetry premise, and uses no downstream
Picard-zero or relative-dual valuative extension theorem.
