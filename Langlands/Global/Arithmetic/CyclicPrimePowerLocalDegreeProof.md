# Full local degree outside finite sets in cyclic prime-power extensions

The theorem `Langlands.Global.cyclicPrimePowerLocalDegreeStatement.{u,v}`
proves the unchanged proposition
`Langlands.Global.CyclicPrimePowerLocalDegreeStatement.{u,v}`. For a cyclic
Galois extension `E/F` of number fields of degree `ℓ^r`, where `ℓ` is prime
and `r > 0`, and every finite set `S` of finite primes of `F`, it gives a
prime `p` outside `S` and a prime `w` of `E` above `p` such that
`[E_w : F_p] = [E : F]`. The completions and their algebra structure are
the actual adic completions with the canonical algebra installed by the
`LiesOver` witness. The field universes `u` and `v` are independent.

The argument applies the published
`Langlands.Global.cyclicPrimePowerLocalDegreeReductionStatement` to choose an
actual intermediate field `K` of degree `ℓ`. The returned Galois and cyclic
properties are installed as instances. Since `ℓ` is prime, the degree of
`K/F` exceeds one. The published
`Langlands.Global.cyclicNonsplitPrimeStatement` therefore applies to `K/F`
and the original finite set `S`. This gives a prime `p` outside `S` and a
prime `q` of `K` above `p` with
nontrivial completed degree. The reduction's local test produces a prime `w`
of `E` above both `q` and `p` with full completed degree. The final conclusion
retains `p`, its exclusion from `S`, `w`, and the supplied witness above `p`.

The intermediate field is a subtype of `E`, so its universe is `v`; the
independent universes `u` and `v` match the nonsplit-prime theorem without a
universe identification. Both applications retain the precise `LiesOver`
witnesses used to install the canonical completion algebras.

This is an internal composition of the published proofs imported from
`Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeReductionProof` and
`Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof`. Its mathematical
provenance is Artin and Tate, *Class Field Theory* (2009), Chapter V §4,
Theorem 3, printed page 17 (PDF page 26): use the degree-prime intermediate
field and Theorem 2 on nonsplit primes. The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The implemented reduction is described in the published proof's paired
Markdown. The conclusion here is full completed-field degree, as used in
Chapter VII §3, Lemma 5, printed page 49 (PDF page 58); it makes no claim
of unramifiedness or full residue degree.

Worker 65 authored this assembly. All arithmetic inputs are imported from
their published proofs. The final theorem has no additional hypotheses,
and the target statement and its full import closure are unchanged.
