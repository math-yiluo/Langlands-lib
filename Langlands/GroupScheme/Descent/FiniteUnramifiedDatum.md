# Actual Čech data over finite unramified integer extensions

This internal construction combines `FiniteUnramifiedComponents` with the
published `SemilinearDatum` API. For a finite Galois intermediate extension
`E/F` in the separable closure, assumed arithmetically unramified, it uses the
actual map `Spec O_E → Spec O_F` and its actual integer automorphisms.
It applies at arbitrary universe `u`, using the small indexing type
`Fin (Module.finrank F E)`.

`integerBaseAut` is the spectrum map of the restriction of a field
automorphism to `O_E`. `integerIndexMul` transports Galois multiplication to
the small index type. The proof of `integerBaseAut_comp` uses the
contravariance of spectrum and verifies equality of the ring maps on their
underlying elements.

For a group scheme `G` over `Spec O_E`, `integerDatum` takes actual
semilinear isomorphisms `e i : (integerBaseAut i)^* G ≅ G`, together with
their pullback tower law. It constructs the actual overlap isomorphism and
its triple-overlap cocycle by `SemilinearComponents.datumOfSemilinear`.
The component decomposition used in that construction is the one proved
in `FiniteUnramifiedComponents`. `pullIso_integerDatum` proves that the
resulting overlap isomorphism restricts to
`baseChangeIdIso G ≪≫ (e i).symm` on each component.

The coherent semilinear isomorphisms are inputs. This construction does
not assert their existence from Galois-stable integral points, nor does it
assert effective descent or the full integral-model descent theorem.
