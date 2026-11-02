# Actual point fibres of multiplication

For a field `K`, an abelian scheme `A` over `Spec K`, and a natural number `n`,
`TorsionPointFibre A n` is the subset of the underlying space of `A` consisting of
points sent by the actual multiplication morphism `[n]` to the image of the
identity section. The definition uses `GroupScheme.multiplication A.toGrp (n : ℤ)`
and `η[A.X]`.

`torsionPointFibre_finite` proves that this set is finite under `(n : K) ≠ 0`.
The proof applies the existing
`Langlands.AbelianScheme.multiplication_isFinite_of_ne_zero` and Mathlib's
`Scheme.Hom.finite_preimage_singleton`. The nonzero condition is an explicit
hypothesis; no algebraic-closure assumption is used.

`isClosed_identityPoint` proves that the identity point is closed. Mathlib's
`isClosedImmersion_of_comp_eq_id` applies to a section over the singleton space
`Spec K`; its image is the singleton in question.
`torsionPointFibre_isClosed` then follows by continuity of multiplication, for
every `n`. With `(n : K) ≠ 0`, local quasi-finiteness makes the fibre discrete
by `Scheme.Hom.isDiscrete_preimage_singleton`. A singleton in this closed
discrete subset is closed in the ambient space, giving
`torsionPointFibre_isClosed_singleton`.

The general helper `section_eq_of_point_eq` concerns any scheme morphism
`p : X ⟶ Spec K`. Two morphisms `f g : Spec K ⟶ X` satisfying
`f ≫ p = 𝟙 _` and `g ≫ p = 𝟙 _` are equal when they send the unique point
to the same point `q`. The proof uses Mathlib's `Scheme.SpecToEquivOfField`,
which describes a field-valued point by `q` and an embedding `κ(q) ⟶ K`.
Write this embedding as `a` and the structural map `K ⟶ κ(q)` as `b`.
The section identity gives `b ≫ a = 𝟙 _`, so `a` is surjective as well as
injective. Thus `a` is an isomorphism, `b` is its inverse, and cancellation
by `b` identifies the embeddings associated to `f` and `g`.
`sectionPoint_injective` packages this result for morphisms in `Over (Spec K)`.
These two results require only that `K` is a field.

`levelToTorsionPointFibre` evaluates an actual element of
`GroupScheme.Tate.Level A.toGrp (Over.mk (𝟙 (Spec K))) n` at the unique
point of `Spec K`. Membership in `levelGroup` says that its section composed
with `[n]` is the identity section, proving membership in `TorsionPointFibre`.
The theorem `levelToTorsionPointFibre_injective` follows from
`sectionPoint_injective` and `GroupScheme.Tate.toSection_injective`.
This map and its injectivity hold for every `n`.

This is an internal supporting construction for the actual cubic
torsion-hyperplane bound. Its provenance is the existing finite-multiplication
theorem, actual torsion-section kernel, and Mathlib's residue-field,
quasi-finite-fibre, and closed-immersion APIs cited above. Worker 1124 supplied
the point-side reduction plan; Worker 310 implemented the construction and
proofs, including the arbitrary-field section-evaluation argument.
The unrestricted geometric cardinality bound remains a separate obligation.
