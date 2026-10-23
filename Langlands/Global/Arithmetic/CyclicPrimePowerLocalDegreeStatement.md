# Full local degree in cyclic prime-power extensions

`Langlands.Global.CyclicPrimePowerLocalDegreeStatement` states that a cyclic Galois
extension `E/F` of number fields of degree `ℓ^r`, with `ℓ` prime and `r > 0`, has a
finite place of full local degree outside any prescribed finite set. More
precisely, for each finite set `S` of nonzero prime ideals of `𝓞 F`, it asserts the
existence of `v ∉ S` and a nonzero prime ideal `w` of `𝓞 E` above `v` such that

`[E_w : F_v] = [E : F]`.

The completions are the actual `adicCompletion` fields. The local algebra
structure is the published one induced by `w.asIdeal.LiesOver v.asIdeal` in
`AdelicFunctoriality.FiniteExtension`; the witness `h` installs precisely that
instance before the local degree is formed. The number fields occupy independent
universes `u` and `v`. Finiteness of the extension follows from their number-field
structures. Cyclicity is imposed on the actual group `E ≃ₐ[F] E`.

This is a proposition definition, not an existence proof. It assumes no
Chebotarev theorem, class-field theorem, or prime-existence hypothesis. It does
not assert unramifiedness of the chosen prime. The assertion about every finite
set expresses the infinitude needed from the source; taking `S = ∅` gives the
single prime used in the later cyclic invariant construction.

## Source and correspondence

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea, 2009,
Chapter V §4, Theorem 3, printed page 17 (PDF page 26), registered as
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The theorem states infinitude of primes that remain prime in a cyclic extension
of prime-power degree. Its proof uses the unique intermediate field of prime
degree and Theorem 2 on primes that do not split completely. The Lean proposition
records the number-field specialization in terms of full completed-field degree.
This is the local-degree consequence used explicitly in Chapter VII §3, Lemma 5,
printed page 49 (PDF page 58), to obtain an idele cohomology class with invariant
`1/ℓ^r`.

The formulation leaves ramification unrestricted, so it does not claim the
stronger conclusion that the residue degree itself is the full global degree.
The published local-degree identity `AdelicFunctoriality.localDegree_eq`
identifies the displayed degree with the product of ramification index and
inertia degree. No global invariant existence or cohomological cardinality bound
is asserted here.
