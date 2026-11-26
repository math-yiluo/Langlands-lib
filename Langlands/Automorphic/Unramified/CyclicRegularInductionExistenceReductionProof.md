# Proof of the cyclic regular-induction existence reduction

Module `Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceReductionProof`.

## Result

`Langlands.Automorphic.Unramified.cyclicRegularInductionExistenceReduction :
CyclicRegularInductionExistenceReductionStatement.{uF, uE, uV, uW}`, the exact
target of module `CyclicRegularInductionExistenceReductionStatement`, for arbitrary
universes `uF`, `uE`, `uV`, `uW`. No hypothesis is added, and no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` is used. Each of the eleven premises
is used, at its stated universe levels.

The lemmas of the argument are in the namespace
`Langlands.Automorphic.Unramified.CyclicRegularInductionExistence`. The common
argument `cyclicRegularInductionExistenceOver_of_inputs` is shared with the totally
complex reduction, proved in `CyclicRegularInductionExistenceReductionTCProof`.

## The common argument

`cyclicRegularInductionExistenceOver_of_inputs` fixes the lower field `F` and
proves `CyclicRegularInductionExistenceOver F E` for every Galois `E : Type uE`
over `F`. Its hypotheses are the bodies of the premises: the prime realization,
the pair comparison and Euler constituent recovery over `F` or over fields
carrying an algebra over `F`, together with the remaining premises as stated.
It proceeds by strong induction on `[E : F]`.

Let `σ` generate `Gal(E/F)` and let `T` be a unitary cusp over `E` fixed by no
power `σ^i` with `0 < i < [E : F]`. Since the order of `σ` is `[E : F]`, every
automorphism is `σ^i` for some `0 ≤ i < [E : F]`; the exponent `0` gives the
identity, and every nonidentity automorphism is a power `σ^i` with
`0 < i < [E : F]`. So the identity is the only automorphism fixing the class of
`T` (`eq_one_of_isGaloisStable`); in degree one the range of positive exponents is
empty and the identity is the only automorphism. Conversely a class fixed only by
the identity is fixed by no power `σ^i` of a generator with `0 < i` below its order
(`not_isGaloisStable_pow`). The argument works with this second form of regularity.

**Degree one** (`exists_weakInduction_of_finrank_eq_one`). The algebra map is a
ring isomorphism `e : F ≃+* E` (`Algebra.finrank_eq_one_iff_bijective_algebraMap`).
The lower cusp is `T.arithmeticComap e`, of the same rank. Its central character
is unitary by `arithmeticComapUnitaryCentralCharacter`. The attachment premise in
`uV` gives a spectral system attached to `T`, and `cuspidalArithmeticSpectralTransport`
gives one attached to the pullback with the Euler polynomial of the former at the
place `(finitePlaceEquiv e).symm v`. The attachment premise in `uW` gives the upper
system. At every place where both upper systems are defined their spectra agree
(`IsoClass.HasSpectralSystem.eigenvalues_eq`). For each finite place `v` of `F`,
the only place of `E` above `v` is `(finitePlaceEquiv e).symm v`, because the place
of `F` corresponding to a place of `E` is the place below it
(`finitePlaceEquiv_eq_under`). Its ramification index is one by the fundamental
identity `finitePlacesAbove_sum_ramification_inertia`
(`ramificationIdx_eq_one_of_finrank_eq_one`), and its inertia degree is one by
`inertiaDeg_eq_one_of_finrank_eq_one`. So the induced Euler polynomial at `v` is
the upper Euler polynomial at that place. Outside the finitely many places where a
system is undefined this is the weak induction identity.

**Prime degree** (`exists_weakInduction_of_prime`, at independent universes). The
generator is not the identity, so the class of `T` is not `σ`-stable, and the prime
realization gives an actual lower cusp `S` of the multiplied rank, with unitary
central character, whose singleton has the Galois orbit of `T` as weak base change.
`HeckeCharacter.cyclicNormKernelCharacter` supplies a character `η` with kernel
exactly the norm image. The orbit has distinct constituents (`galoisOrbit_nodup`)
and is unitary (`isUnitary_galoisOrbit`, by arithmetic transport of the unitary
central character), so it has exactly `[E : F]` equal pairs with itself. The
singleton of `S` is unitary by `isUnitarizable_of_hasUnitaryCentralCharacter`.
The pair comparison, applied to the singleton and the orbit twice, writes `[E : F]`
as a sum of `[E : F]` multiplicities of the twists of `S` by `η^i` in the singleton,
each at most one. So each is one; for `i = 1` the twist by `η` is `S` itself, and
`IsoClass.isFiniteOrderDeterminantTwist_iff_eq` gives the self-twist. The reverse
orbit comparison `CyclicOrbitBaseChangeWeakInductionStatement` then gives weak
induction. The lemma also returns the weak base change of the singleton.

**Composite degree.** Let `n = [E : F]`, neither one nor prime, and `p` its least
prime factor, so `p < n`. The power `g = σ^(n/p)` has order `p`
(`orderOf_pow_orderOf_div`). Any two automorphisms are powers of `σ` and commute,
so `H = ⟨g⟩` is normal. Let `K` be its fixed field. Then `K/F` is Galois
(`IsGalois.of_fixedField_normal_subgroup`), `[E : K] = p`
(`IntermediateField.finrank_fixedField_eq_card`), and `[K : F] < n` by the tower
law. The adèle quotient of `K` is compact by `compactSpace_adeleQuotient`.

`Gal(E/K)` has prime order, hence a generator. The class of `T` remains regular for
`E/K`: a `K`-automorphism fixing it, viewed over `F`, fixes it
(`isGaloisStable_restrictScalars`), so it is the identity. The prime step over
`E/K`, with the premises at `.{uE, uE, uW, uW}`, gives a unitary cusp `U` over `K`,
the weak base change from its singleton to the `Gal(E/K)`-orbit of `T`, and the weak
induction from `T` to `U`.

The class of `U` is regular for `K/F`. Let `ρ` fix it. It is the restriction of
some `τ` in `Gal(E/F)` (`AlgEquiv.restrictNormalHom_surjective`), and `τ` and `ρ`
are compatible with `K → E` (`AlgEquiv.restrictNormal_commutes`). The equivariance
premise makes the `τ`-translate of the orbit a weak base change of the singleton of
the `ρ`-translate of `U`, which is `U`. Two weak base changes of one isobaric datum
coincide, by Euler constituent recovery over `E` (`isWeakBaseChangeOf_unique`: the
two upper systems are arithmetic weak base changes of lower systems with the same
Euler polynomials, so their Euler polynomials agree at every place above a cofinite
set of places of `K`, and recovery compares two enumerations of constituents). So
the translated orbit is the orbit, and contains the class of `T`. Hence some `ρ'`
in `Gal(E/K)` gives `T ≅ (T^{ρ'})^{τ}`, that is, `τ ρ'` fixes the class of `T`. By
regularity over `F`, `τ ρ' = 1`. Since `ρ'` fixes `K` pointwise, so does `τ`, and
then `ρ` is the identity. A generator of `Gal(K/F)` exists because it is a quotient
of the cyclic group `Gal(E/F)`.

The induction hypothesis for `K/F` gives a unitary cusp `S` over `F` weakly induced
from `U`, of rank given by `[K : F]`. `WeakInductionTransitivityStatement` at
`.{uF, uE, uE, uV, uW, uW}` composes the two weak inductions, and the rank equation
follows from `[K : F][E : K] = [E : F]`.

## Assembly

`cyclicRegularInductionExistenceReduction` introduces the eleven premises and the
fields, and applies the common argument with the premises themselves: the prime
realization and pair comparison at `.{uF, uE, uV, uW}` over `F`, and at
`.{uE, uE, uW, uW}` over the intermediate field, the two reverse orbit comparisons,
equivariance at `.{uE, uE, uW, uW}`, Euler constituent recovery at `.{uE, uW}` over
the upper field, transitivity, and the two attachment premises.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. The argument is
the proof of Lemma III.6.4, printed pp. 217–218 (PDF pp. 231–232), which takes a
prime top layer `[E : E₁]`, obtains the cusp over `E₁` from Theorem III.4.2,
excludes its stability under a nontrivial automorphism of `E₁/F` by
Proposition III.4.4(iii), printed pp. 210–211 (PDF pp. 224–225), and applies the
lemma inductively to `E₁/F`. The Lean proof takes the least prime factor for the
top layer. The prime realization is Theorem III.4.2(e), printed pp. 202 and 207–210
(PDF pp. 216 and 221–224). The norm-twist pair comparison and the constituent
recovery are III.(2.2)–(2.4), printed p. 200 (PDF p. 214). The weak-induction
formulas and their composition in a tower are Definition III.6.1 and Theorem III.6.2,
printed pp. 214–217 (PDF pp. 228–231).
