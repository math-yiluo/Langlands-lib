# Adic effectivity for diagonalizable sources

This module constructs an actual global homomorphism from a compatible
formal system and proves the adic Hom comparison for every diagonalizable
source and affine target. It implements the diagonalizable case of SGA 3,
Exposé IX, Theorem 7.1, recomposed pp.56–58 (original margins pp.68–72),
registered source `sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The coordinate adapters and the transport of formal systems are internal
constructions using the published Library Hopf-spectrum and Hom coordinates.

Let `A` be a commutative noetherian ring, `I` an ideal for which `A` is
`I`-adically complete and separated, `M` any commutative additive group,
and `C` any commutative Hopf algebra over `A`. Initially the source and
target groups are the Hopf spectra of `A[M]` and `C`. An input
`HomScheme.Adic.System I H G` consists of actual group-scheme homomorphisms
over `Spec(A/I^(n+1))`, compatible with the actual successive pullbacks.

`nativePoint` uses `FiniteSource.pointEquiv` to express each of these
homomorphisms as a Hopf point `C →ₐ[A] (A/I^(n+1)) ⊗[A] A[M]`.
The coordinate part of that published equivalence imposes no finite-source
or finite-presentation hypotheses. `groupPoint` uses `HopfPointBridge`
to identify these with Hopf points in `(A/I^(n+1))[M]`.
`point_evaluate_specMap` and `toGroupAlgebra_pushPoint` show that actual
pullback changes exactly the coefficients, proving `groupPoint_compatible`.
`algebraSystem` extends over the zero quotient and feeds these points to
`AdicHopfPoint`, which provides a genuine bialgebra map `C →ₐc[A] A[M]`.

`lift` applies the actual Hopf-spectrum functor to that map, producing a
homomorphism of the original Hopf spectra. `relativeHomEquiv_baseChange`
uses the published tensor-spectrum naturality theorem to identify the
coordinates of an actual base-changed homomorphism. The resulting
`groupPoint_baseChange` says these coordinates are coefficientwise change
of ring. Since the algebraized map has the prescribed coefficients,
`lift_reduction` proves equality with every original scheme homomorphism.
This gives `restrict_surjective`.

For injectivity, `coordinateMap` recovers the actual bialgebra map of an
arbitrary homomorphism of Hopf spectra by full faithfulness. Equality of
all scheme reductions gives equality of the corresponding coefficients
modulo every positive power of `I`. Adic separatedness identifies the
original coefficients. Full faithfulness then recovers equality of the
homomorphisms, proving `restrict_injective` and `restrict_bijective`.
The injectivity argument uses separatedness and does not use noetherianity.

`Adic.System.transport` carries formal systems along source and target
isomorphisms. Published evaluation naturality proves its compatibility;
`restrict_bijective_of_iso` proves that bijectivity of the restriction map
is invariant under these isomorphisms. Finally,
`restrict_bijective_of_isDiagonalizable` replaces a relatively diagonalizable
source by its standard group-algebra Hopf spectrum and an affine target by
its actual coordinate Hopf spectrum. It concludes

```text
Function.Bijective (HomScheme.Adic.System.restrict I H G)
```

for every `H`, `G` over `Spec A` with `IsDiagonalizable H` and
`IsAffineHom G.X.hom`. The character group chosen by `IsDiagonalizable`
is finitely generated as in the Library definition; the standard Hopf-spectrum
construction itself does not use that condition. All types lie in the
arbitrary universe `u`.

There is no smoothness, finite-type, or flatness hypothesis on the target.
This is the complete split-source case of the adic Hom comparison; it does
not perform finite étale descent or infinitesimal lifting/conjugacy, so it
does not by itself prove the full isotrivial lifting statement
`MultiplicativeTypeAdicLiftStatement`.

The imported `AdicAffinePoints` and `AdicSystem` helper pairs are used
unchanged. The coefficient and scheme adapters are defined in this module.
