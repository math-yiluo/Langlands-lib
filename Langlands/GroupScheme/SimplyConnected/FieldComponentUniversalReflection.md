# Reflection of the central-cover universal property from a finite tensor decomposition

Authors: Workers 1347, 416 and 1366. Worker 1347 supplied the proof
prototype. Worker 416 suggested the descent of module finiteness and
supplied the tensor-component and component-Hom interfaces. Worker 1366
prepared the exact-target proof and explanation for review.

The closing theorem
`Langlands.GroupScheme.centralCoverUniversalPropertyTensorReflection.{u}`
has exactly the published type
`Langlands.GroupScheme.CentralCoverUniversalPropertyTensorReflectionStatement.{u}`.
It imports that statement and proves reflection for arbitrary fields
`k K : Type u` with `Algebra k K`, actual group schemes `C` and `G` over
`Spec k`, and an actual homomorphism `π : C → G`.

The hypotheses are a finite type `I : Type`, a supplied algebra equivalence
`e : K ⊗[k] K ≃ₐ[K] (I → K)`, a family `s : I → (K ≃ₐ[k] K)` with
`e (a ⊗ₜ b) i = a * s i b`, and the central-cover universal property of
the actual pullback of `π` along `p : Spec K → Spec k`. The conclusion
is `HasCentralCoverUniversalProperty π`. In this predicate, every actual
central isogeny `q : H → G` from a semisimple group scheme `H` has exactly
one actual factorization `a₀ : C → H` with `a₀ ≫ q = π`.

## Field-component reflection

`HasCentralCoverUniversalProperty.of_fieldComponents` first proves the
implication for an algebraic extension `K/k` and a supplied finite
field-component decomposition of `Overlap p`. Its component fields may
vary with the index. The coproduct of the component maps must be an
isomorphism, and both structural maps from each field component to
`Spec K` must be isomorphisms. The proof uses `fieldExtension_fpqc` to
install flatness, surjectivity and quasi-compactness of `p`.

Fix a semisimple `H` and a central isogeny `q : H → G`. The separate
algebraic-extension ascent theorem makes `H_K` semisimple. Central-isogeny
base change makes `q_K` a central isogeny. The given universal property
therefore gives a unique homomorphism `a : C_K → H_K` satisfying
`a ≫ q_K = π_K`.

Both `π_K` and `q_K` are compatible with their canonical descent data.
`Compatible.of_factorization_onFieldComponents` proves the same
compatibility for `a`. It restricts the two descent expressions to each
field component, transports the universal property along the first
structural isomorphism and the target overlap isomorphism, and observes
that both expressions factor the same map through the same semisimple
central isogeny. Uniqueness identifies them on that component, and
finite-component equality detection identifies them on the full overlap.
The universal property is used only on the field components.

`Descent.FpqcHomDescent.hom` then supplies an actual descended
homomorphism `a₀ : C → H`. Its recovery theorem gives `p*a₀ = a`.
Faithfulness of actual pullback along the fpqc map `p` reflects the
equation `a₀ ≫ q = π`. A competing factorization pulls back to `a` by
uniqueness over `K`, and the same faithfulness proves that it equals
`a₀`. This is existence and uniqueness over `k`.

## Tensor-decomposition specialization

`HasCentralCoverUniversalProperty.of_tensorDecomposition` derives the
algebraicity and component hypotheses from the supplied tensor data.
The `K`-algebra structure on the tensor product is through its first
factor. Since `I` is finite, the `K`-module `I → K` is finite. Transport
through `e.toLinearEquiv` makes `K ⊗[k] K` finite as a `K`-module.
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K` descends this
to `Module.Finite k K`; the field extension is consequently algebraic.
No algebraicity or finiteness assumption on the extension is added to
the target.

The published maps `Descent.tensorComponent e i` give the finite
coproduct decomposition of the actual double overlap. Their composites
with `fst p` are identities. The pure-tensor formula identifies their
composites with `snd p` with the spectra of the supplied automorphisms
`s i`; hence those composites are isomorphisms as well. Applying the
preceding field-component theorem proves the implication. The closing
theorem introduces the data in the published target and applies this
specialization directly.

## Provenance and scope

This is an internal deduction from the published actual group-scheme
predicates, tensor-component interfaces, field-isomorphism transport,
algebraic-extension semisimplicity ascent and fpqc descent of actual
homomorphisms. It does not use an external literature assertion as a
premise. The algebraic-extension ascent proof is supplied by the separate
module `Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent`.

All fields and the universe `u` are arbitrary, including imperfect fields
and positive characteristic. The proof keeps the full scheme-theoretic
centres and kernels on all test schemes, including nonreduced tests.
It assumes no semisimplicity or simple connectedness of `C` or `G`, and
no isogeny property of `π`. The universal property after base change is
its only group-theoretic premise.

The theorem supplies reflection through a given decomposition. Cover
existence, simple-connectedness reflection and existence of the tensor
decomposition remain separate results. The published target pair,
`SimplyConnected.CoverExistenceStatement` and every pair they import are
left unchanged.
