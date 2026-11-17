# Fibre centrality in actual Hopf algebra coordinates

This is an internal derived construction in
`Langlands.GroupScheme.HopfFiberCentrality`. Fix a commutative ring `R` and
commutative Hopf algebras `A` and `C` over `R`, all in an arbitrary common
universe, and a Hopf algebra map `π : A ⟶ C`. The associated group
homomorphism is the actual contravariant Hopf-spectrum map
`Spec C → Spec A`. The construction preserves centrality on every full
residue-field fibre when enlarging a supplied noetherian coefficient ring.
It does not assume reducedness of any algebra.

## Coactions and actual scalar extension

`leftCoaction π` and `rightCoaction π` are algebra maps
`A → C ⊗[R] A`. The first is `(π ⊗ id) ∘ Δ`; the second is
`swap ∘ (id ⊗ π) ∘ Δ`. Their application formulas identify these
algebra maps with the published linear tensor coactions.
`isCentral_iff_coaction_eq` uses `HopfSpecCentrality` and algebra-map
extensionality to identify their equality with `IsCentral` of the actual
Hopf-spectrum map. That predicate tests centrality after every test-scheme
restriction; it is not a condition only on field-valued points.

For any commutative `R`-algebra `S` in the same universe,
`scalarExtensionMap S π` is the actual tensor-product Hopf map
`S ⊗[R] A → S ⊗[R] C`. The standard Hopf structure on the scalar
extension is used. `coactionTensorIso` is the canonical algebra isomorphism

`S ⊗[R] (C ⊗[R] A) ≃ (S ⊗[R] C) ⊗[S] (S ⊗[R] A)`.

Its pure-tensor formula is
`s ⊗ (c ⊗ a) ↦ (s ⊗ c) ⊗ (1 ⊗ a)`.
The two `Coaction_scalarExtension` lemmas compare the actual coactions
with the scalar extensions of the original algebra maps followed by this
isomorphism. The proofs use tensor algebra-map extensionality, the
scalar-extension comultiplication formula, and induction on the original
comultiplication tensor. Injectivity of the target isomorphism then gives
`isCentral_scalarExtension_iff`.

`baseChange_hopfSpec` is a naturality equality for the actual group-scheme
pullback and the standard Hopf-spectrum scalar-extension isomorphisms.
It follows by forgetting to the underlying affine morphism and applying
`HopfMorphismBaseChange.tensorSpecIso_naturality`.
`isCentral_baseChange_iff` transports centrality across these actual group
isomorphisms. Thus it equates centrality of the actual scheme pullback
with equality of the two scalar-extended algebra maps, without assuming
flatness or finite type.

## The residue-fibre locus

`fiberCentralityLocus π` is the set of primes `p` of `R` for which the
pullback of the Hopf-spectrum homomorphism along the canonical algebra
map `Spec κ(p) → Spec R` is central, with
`κ(p) = p.asIdeal.ResidueField`. These are full scheme pullbacks, retaining
nilpotents in the fibre algebras.
`fiberCentralityLocus_eq` identifies this set with the full fibre-map
equality locus of `leftCoaction π` and `rightCoaction π`.

`fiberCentralityLocus_scalarExtension` proves that for every `R`-algebra
`S`, the centrality locus of `scalarExtensionMap S π` is exactly the
inverse image of the original locus under contraction of primes.
Postcomposition by an algebra isomorphism preserves and reflects full
residue-fibre equality: its tensor extension is still an isomorphism.
Applying this observation to `coactionTensorIso`, the coaction comparison
formulas and the published arbitrary-base-change identity for fibre-map
equality proves the claim.

`isConstructible_fiberCentralityLocus` assumes that `R` is noetherian and
both `A` and `C` are finite type `R`-algebras. The target `C ⊗[R] A` is
finite type by base change and transitivity. The full fibre-map equality
constructibility theorem therefore applies to the two coactions.

## Finite coefficient enlargement

Under these same noetherian and finite-type assumptions, suppose the
centrality locus after scalar extension to a commutative `R`-algebra `S`
is all of `Spec S`. For any finite set `t` of elements of `S`,
`exists_fg_subalgebra_fiberCentrality` returns an actual finitely generated
`R`-subalgebra `T` of `S` containing `t`, for which the centrality locus
after scalar extension to `T` is also all of `Spec T`.
The proof rewrites the hypothesis using the inverse-image identity, applies
`FiberMapEqualityDescent.exists_fg_subalgebra_preimage_eq_univ` to the
constructible locus and the actual coefficient spectrum limit, then
rewrites its conclusion by the same inverse-image identity.

`FiberCentralityCoefficientModel` retains this subalgebra, its finite
generation, containment of `t`, and centrality on every full ideal-residue
fibre of the actual scalar-extension map.
`fiberCentralityCoefficientModel` chooses that data from the proved
existence theorem. No noetherian hypothesis is imposed on `S`.

This construction starts from supplied Hopf algebras and a Hopf map. It
does not construct reductive group models, prove centrality over the whole
base from fibrewise centrality, or prove the host central-isogeny
criterion. Comparison with Mathlib's scheme-stalk presentation of a
residue field is a further transport step. The provenance is derived:
the proofs compose the published Hopf centrality criterion, actual tensor
and scheme base-change comparisons, and constructible affine-limit
detection; they invoke no new external structural theorem.
