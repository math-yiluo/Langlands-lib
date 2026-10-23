# Proof of the residue-limit / p-adic product comparison

`Langlands.Global.profiniteIntegerPadicProductComparison` proves the Library
proposition `Langlands.Global.ProfiniteIntegerPadicProductComparison` from
module `Langlands.Global.ProfiniteIntegerPadicProductComparison`, which is
imported unchanged. The theorem has no parameters or hypotheses. It
constructs a unital ring equivalence

\[
e:\mathrm{ProfiniteIntegerRing}\;\simeq\;\prod_{p\ \mathrm{prime}}\mathbb Z_p
\]

from the existing residue-limit ring to the actual dependent product
`(p : Nat.Primes) → PadicInt (p : ℕ)`, proves that \(e\) and \(e^{-1}\) are
continuous for the existing topologies, and proves the normalization
\(e(\mathrm{intCastHom}(z))_p=(z:\mathbb Z_p)\).

As in the statement file, the proof module declares the local instance
`Fact p.val.Prime := ⟨p.property⟩` for `p : Nat.Primes`. Since `Fact` is a
proposition, its instance terms are definitionally equal by proof
irrelevance, so the rings and topologies are the ones of the statement.

## The map

The map is `RingHom.pi` of the existing canonical projections
`ProfiniteIntegerRing.toPadic p` from
`Langlands.Global.ProfiniteIntegerPadicProjection`; its \(p\)-th coordinate
is `toPadic p x`. These projections are characterized by
`toZModPow_toPadic`: the reduction of `toPadic p x` modulo \(p^k\) is the
residue of \(x\) at the positive modulus \(p^k\).

## Two arithmetic lemmas

**Uniqueness (private `intCast_eq_of_primePow`).** For a natural number \(n\)
and integers \(z,z'\), if \(z\equiv z'\pmod{p^k}\) for every prime \(p\) and
every \(k\) with \(p^k\mid n\), then \(z\equiv z'\pmod n\). This is
`ZMod.intCast_eq_intCast_iff_dvd_sub` and `Int.natCast_dvd`, reduced to
Mathlib's `Nat.dvd_iff_prime_pow_dvd_dvd` applied to
\(|z'-z|\).

**Existence (private `exists_intCast_eq_toZModPow`).** For every family
\(y=(y_p)_p\) of \(p\)-adic integers and every positive \(n\), there is an
integer \(z\) with \((z \bmod p^k)=\mathrm{toZModPow}_k(y_p)\) whenever
\(p^k\mid n\). Let \(v_p\) be the exponent of \(p\) in \(n\). Mathlib's
`Nat.chineseRemainderOfFinset`, applied over the primes dividing \(n\)
(the preimage of `n.primeFactors` in `Nat.Primes`) to the pairwise coprime
moduli \(p^{v_p}\) and the residues `(toZModPow v_p (y p)).val`, gives a
natural number \(c\) congruent to each of them; for primes not dividing
\(n\) the modulus is \(p^0=1\), so the congruence holds trivially. Then
\((c \bmod p^{v_p}) = \mathrm{toZModPow}_{v_p}(y_p)\), and for
\(p^k\mid n\) (so \(k\le v_p\) by
`Nat.Prime.pow_dvd_iff_le_factorization`) the reduction modulo \(p^k\)
follows from `PadicInt.zmod_cast_comp_toZModPow`.

A third private lemma, `toZModPow_toPadic_eq_intCast`, records that if an
integer \(z\) represents the residue of \(x\) modulo \(n\) and \(p^k\mid n\),
then `toZModPow k (toPadic p x)` is \(z \bmod p^k\). It combines
`toZModPow_toPadic`, the compatibility of the residue family at
\(p^k\mid n\), and `ResidueLimit.transition_intCast`.

## Bijectivity

*Injective.* If two residue families have the same p-adic coordinates, fix a
positive modulus \(n\) and integer representatives \(z,z'\) of their
residues modulo \(n\). By the third lemma, \(z\) and \(z'\) agree modulo every
prime power dividing \(n\), so by uniqueness they agree modulo \(n\). The
families agree at every modulus and hence are equal (`ResidueLimit.ext`).

*Surjective.* Given \(y\), choose for every positive \(n\) an integer
\(z_n\) from the existence lemma and take the family
\(n\mapsto (z_n \bmod n)\). It lies in the compatible subring: for
\(i\mid j\), the reduction of \(z_j\) modulo \(i\) and \(z_i\) agree modulo
every prime power dividing \(i\) (both equal the coordinate of \(y\)), so
they agree modulo \(i\) by uniqueness. Its image is \(y\): for each prime
\(p\) and each \(k\), the reduction of its \(p\)-th coordinate modulo \(p^k\)
is \(z_{p^k} \bmod p^k=\mathrm{toZModPow}_k(y_p)\), and p-adic integers with
the same reductions are equal (`PadicInt.ext_of_toZModPow`).

The witness is `RingEquiv.ofBijective` of this ring homomorphism, so it is a
unital ring equivalence whose underlying function is the product of the
canonical projections.

## Continuity and normalization

The map is continuous because each coordinate is continuous
(`ProfiniteIntegerRing.continuous_toPadic`) and the target carries the
product topology (`continuous_pi`). The inverse is continuous by
`Continuous.continuous_symm_of_equiv_compact_to_t2`: the residue-limit ring
is compact (its existing `CompactSpace` instance) and the product of p-adic
integer rings is Hausdorff. No topology is transported.

The normalization is the existing `ProfiniteIntegerRing.toPadic_intCast`,
since the \(p\)-th coordinate of \(e(\mathrm{intCastHom}(z))\) is by
definition `toPadic p (intCastHom z)`.

The proof uses no hypotheses, comparison assumptions, replacement rings or
transported topologies, and adds no axioms. The private helper declarations
are not part of the public interface; only the theorem is exported.
