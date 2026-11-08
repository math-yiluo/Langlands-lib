# Reciprocity and conjugation by absolute Galois elements on a finite Galois kernel

Author: Worker 1839, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. All
declarations are in `Langlands.Weil.Local`. This module extends the equivariance
of `Langlands.Weil.Local.FiniteGaloisEquivariance` from conjugation by elements of
the local Weil group `W_F` to conjugation by arbitrary elements `κ` of the
absolute Galois group `G_F`. The extension is needed because the direct and
composite Weil maps of a tower of fields differ by such a conjugation (see
`Langlands.Weil.Local.FiniteGaloisTower`).

## Setting

`F E : PadicField p`, `f : F.Carrier →ₐ[Padic p] E.Carrier`, and
`hGal : IsGalois F.Carrier E.Carrier` for `extensionAlgebra F E f`, as in
`FiniteGaloisQuotient`. Conjugation of the Weil pullback by `κ` is the published
`galoisConjugationWeil F κ`, which maps `(σ, n)` to `(κ σ κ⁻¹, n)`.

## Conjugation of the kernel

- `finiteGaloisQuotient_galoisConjugationWeil`: the finite Galois quotient of
  `galoisConjugationWeil F κ x` is the conjugate of the quotient of `x` by the
  restriction `finiteGaloisRestriction F E f hGal κ`. This holds because the
  quotient is restriction after `localProjection`.
- `galoisConjugationWeil_mem_ker`: hence the conjugation preserves the kernel of
  the finite Galois quotient.
- `kernelGaloisConjugation` is the induced continuous automorphism of that
  kernel.
- `finiteGaloisAbsoluteConjugation F E f hGal κ` is its transport to `W_E`
  through `finiteGaloisQuotientKernelEquiv`.
- `extensionWeilMap_finiteGaloisAbsoluteConjugation`: it agrees with
  `galoisConjugationWeil F κ` after `extensionWeilMap F E f`.
- `localDegree_finiteGaloisAbsoluteConjugation`: it preserves the integer degree.
  `galoisConjugationWeil` preserves degree, and the positive residue degree of
  `extensionWeilMap` cancels in `ℤ`.

## Closure and base automorphisms

`absoluteClosureConjugation F E f κ = ε ∘ κ ∘ ε⁻¹`, where
`ε = extensionClosureEquiv F E f`.

- `absoluteClosureConjugation_apply` and `absoluteClosureConjugation_symm_apply`
  evaluate it, and its inverse, through `ε`.
- `absoluteClosureConjugation_algebraMap` shows that on `E` it is the restriction
  `finiteGaloisRestriction F E f hGal κ`, using `finiteGaloisRestriction_apply`.
- `localProjection_finiteGaloisAbsoluteConjugation_closure` proves
  `projection(c_κ w)(θ x) = θ(projection(w)(x))`, with `θ` the closure
  automorphism and `c_κ` the transported conjugation. The proof has the same
  structure as for Weil elements in `FiniteGaloisEquivariance`: it uses
  `extensionClosureLift_galoisMap` and the identity
  `extensionWeilMap (c_κ w) = galoisConjugationWeil F κ (extensionWeilMap w)`.

`absoluteBaseConjugation F E f hGal κ` is the restriction of `κ` as a ring
automorphism of `E`, and `absolutePadicGaloisEquiv` is the same map over
`Padic p`. The following lemmas discharge the remaining hypotheses of the
generic theorem.

- `absoluteBaseConjugation_compatible` is the compatible square.
- `continuous_absoluteBaseConjugation` and
  `continuous_absoluteBaseConjugation_symm` give continuity, through the
  published `extension_isometry`.
- `orderHom_absoluteBaseConjugation` is order preservation, from
  `PadicField.CanonicalTransport.ord_map`.

## Main theorem

`reciprocityUnits_finiteGaloisAbsoluteConjugation`: for every reciprocity
candidate `e` of `E` with `GeometricWeilReciprocityRelation`, every `κ` in `G_F`,
and every `w` in `W_E`,

`reciprocityUnits E e (finiteGaloisAbsoluteConjugation F E f hGal κ w) =
  Units.mapEquiv (absoluteBaseConjugation F E f hGal κ) (reciprocityUnits E e w)`.

It is an application of Worker 1556's
`LocalClassField.WeilReciprocityTransport.reciprocity_conjugation`. The data are
the base automorphism, the closure automorphism and `c_κ`, together with the
lemmas above. The local candidate relation is `⟨he.1, he.2.1⟩`.

## Provenance

Derived. It is the same uniqueness–transport argument as in
`FiniteGaloisEquivariance`, applied to the published `galoisConjugationWeil`.
Classically this is the Galois compatibility of local reciprocity with
conjugation (Tate 1979, *Number theoretic background*, condition (W2) in (1.1),
printed pp.3–4). Nothing here relies on that source.
