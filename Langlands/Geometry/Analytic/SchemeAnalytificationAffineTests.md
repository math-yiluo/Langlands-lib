# Affine tests for localized scheme analytification

Over a complete nonarchimedean field with nontrivial norm, a finite polynomial presentation of a commutative algebra supplies a separated affine scheme locally of finite type. `affineTestObject` is its spectrum, with the algebra's structural map to the spectrum of the base field.

`affineTestIso` identifies the localized analytification obtained by gluing affine opens of this spectrum with the polynomial-locus model of the specified presentation. The full affine chart is the analytic domain of all points. Its inclusion is an isomorphism by the factorization property of analytic domains. The ring of sections of the full chart is canonically the test algebra, using the restriction to the full open and the affine spectrum's global-section isomorphism. The induced algebra equivalence gives inverse isomorphisms of the polynomial-locus models by affine functoriality.

`affineTestIso_naturality` compares the actual localized map of spectra arising from an algebra homomorphism with the polynomial-locus map. Restrict the scheme arrow to the full affine charts and use the naturality of pullback of sections there to identify the two algebra maps.

This is the affine case of scheme analytification in Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields* (1990), Theorem 3.4.1, pp. 63–64. The domain factorization used here is the defining property in §3.1, p. 48.
