# Integral models of the actual tame Harris tower

Worker 951, Task 7903. The definitions are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

`CMIntegralTraitRing v` is the localization of the ring of integers of `F`
at the height-one prime `v`, realized by Mathlib's
`v.valuationSubringAtPrime F`. `cmIntegralTraitGenericMap` uses the
inclusion in `F`, and `cmIntegralTraitClosedMap` uses the quotient to its
actual residue field. These maps have common target the spectrum of the
valuation subring, not the spectrum of its completion.

`cmHarrisTameOverTower` restricts the arithmetic Harris tower determined by
`q` to fixed local level `K₀` at `p`. It uses `awayFunctor` and
`representedCMOverTower`; after forgetting the map to `Spec F`, its objects
and arrows are the corresponding objects and arrows of `cmSchemeTower`.
The domain is the Library's `cmPrimeToProperty` full subcategory of the
opposite prime-to-`p` transporter category. In particular it retains the
right translations, not just the poset of inclusions.

`CMHarrisTameIntegralTower` packages a **supplied** tower over the trait at
a place `v` above `p`, a natural isomorphism of its actual generic fibre
with `cmHarrisTameOverTower`, relative smooth dimension `n − 1` and
H-projectivity at every level, and finite étaleness of the tame arrows.
For a Hecke span whose legs are in the tame category, naturality identifies
both legs with their Harris counterparts after taking generic fibres.
`genericIso_naturality` writes this square on the underlying schemes;
its proof applies the forgetful map to the naturality equation in `Over`.
`specialTower` takes the actual pullback to the residue field.

## Provenance and limitations

This is a scheme-level interface for the beginning of Kottwitz's §5
(*On the λ-adic representations associated to some simple Shimura
varieties*, printed p. 661, PDF p. 9; `kottwitz-1992-lambda-adic-simple-shimura`,
SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`).
The smooth projective PEL models and tame transitions come from *Points on
some Shimura varieties over finite fields*, §§5–6, pp. 389–393 (PDF
pp. 17–21; `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`).
Harris–Taylor III.1, pp. 90–92 (PDF pp. 98–100;
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`),
gives the characteristic-zero moduli problem, Hecke maps and complex
uniformization. Its real symmetric domain has one factor of signature
`(1,n−1)` and definite remaining factors, giving the dimension used here.

No integral PEL functor, representability, chart-to-self-dual lattice
construction or coefficient extension is asserted. The type is defined
for arbitrary `K₀` and contains no theorem that it is inhabited, even at a
hyperspecial `K₀`. Model existence must check the source's smallness of the
tame levels and the hyperspecial lattice data, transport from the reflex
field, and compare the actual moduli problems. The source's rational
skew-Hermitian type decomposition (§8, pp. 398–400) is not a decomposition
into individual geometric connected components. Harris–Taylor III.1,
p. 92, describes the full moduli space as a union of copies. A proof
using this interface must establish which moduli space its generic fibre
is, rather than assume it is one copy. In Kottwitz's §19, p. 442,
(19.5) is for the whole moduli scheme and (19.6) is for one canonical copy
for `(G, [h⁻¹])` in the notation of that paper. Relating the copy factor,
coefficient correspondences, specialization and traces is separate work.
