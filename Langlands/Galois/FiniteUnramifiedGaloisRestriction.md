# Inertia and Frobenius under actual finite Galois restriction

`finiteGaloisRestriction E` restricts the absolute Galois group to a Galois
subfield `E` of the actual algebraic closure, with the Krull topology on
both sides. `localToGlobalGalois` abbreviates the map used by
`LambdaAdicCharacter.atFinitePlace` for the actual completion at `v`.

`FiniteUnramifiedGaloisRestrictionStatement` uses an actual finite abelian
subfield and a prime `w` above `v` at which the extension is unramified.
The composite from the actual local absolute Galois group to `Gal(E/K)`
sends local inertia to one. It sends the inverse of each geometric lift
to an arithmetic Frobenius, in the Mathlib `IsArithFrobAt` sense on the ring
of integers at `w`. Its abelian hypothesis makes the Frobenius independent
of the prime above `v` selected by the closure embedding.

## Source and proof route

This is the unramified decomposition-group and residue-field comparison
used in Milne, *Class Field Theory*, v4.03, Chapter V §5, Lemma 5.1, pp. 177–178,
and in Serre, *Abelian l-Adic Representations and Elliptic Curves*, Chapter
II §2.3, p. II-12. The specific statement is derived for the Library's
residue action and completion-to-global map. It is a Galois and residue
comparison independent of class field existence.

The statement is proved by `finiteUnramifiedGaloisRestriction` in
`Langlands.Galois.FiniteUnramifiedGaloisRestrictionProof`. At the prime
`inducedPrime v E` induced by the completion embedding, the inverse of the
image of a geometric Frobenius lift restricts to an arithmetic Frobenius
(`arithmeticFrobeniusAt_inducedPrime`, module
`Langlands.Galois.FrobeniusDensity`). The primes of `E` above `v` are
conjugate under `E ≃ₐ[K] E`, and conjugation moves an arithmetic Frobenius
at a prime to one at the conjugate prime; in the abelian group it does not
change the element. So the restriction is an arithmetic Frobenius at every
prime above `v`, without the unramifiedness hypothesis
(`finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt`). A
geometric Frobenius lift times an element of local inertia is again one
(`isGeometricFrobeniusLift_mul_of_mem_localInertia`), and an arithmetic
Frobenius at an unramified prime is unique
(`Langlands.ClassFieldTheory.Global.Artin.eq_of_isArithFrobAt_mapAlgHom`);
so local inertia restricts to one
(`finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia`).

Milne source ID `milne-2020-class-field-theory` (SHA-256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`).
Serre source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
