# One-sided inverses of polynomial substitutions are two-sided

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only. Everything is in namespace
`Langlands.GroupScheme.TorusLinearization`.

- `injective_of_surjective_of_isNoetherianRing f hf`: a surjective ring endomorphism
  `f` of a Noetherian commutative ring is injective.
- `aeval_eq_X_of_aeval_eq_X Φ Q h`: let `k` be a field and
  `Φ Q : Fin n → MvPolynomial (Fin n) k`. If `aeval Φ (Q j) = X j` for every `j`,
  then `aeval Q (Φ i) = X i` for every `i`. So a one-sided inverse under
  substitution is two-sided.

## Proofs

For the first lemma, the kernels of the iterates `f ^ m` form an increasing chain
of ideals. By `monotone_stabilizes_iff_noetherian` the chain is constant from some
`N` on. Let `f x = 0`. Since `f ^ N` is surjective, `x = f ^ N y` for some `y`.
Then `f ^ (N + 1) y = f x = 0`, so `y` lies in the kernel of `f ^ (N + 1)`, which
equals the kernel of `f ^ N`. Hence `x = 0`.

For the second lemma, let `ψ := aeval Φ`, an endomorphism of `k[X₁, …, Xₙ]`. The
hypothesis says `ψ ∘ aeval Q` fixes every variable, so `ψ ∘ aeval Q` is the
identity (`AlgHom` extensionality on `MvPolynomial`). In particular `ψ` is
surjective. The ring `k[X₁, …, Xₙ]` is Noetherian by Hilbert's basis theorem
(Mathlib's instance `MvPolynomial.isNoetherianRing`), so `ψ` is injective by the
first lemma. Finally `ψ (aeval Q (Φ i)) = Φ i = ψ (X i)`, so
`aeval Q (Φ i) = X i`.

## Provenance

Both lemmas are standard commutative algebra. The first is the usual
ascending-chain argument showing that a surjective endomorphism of a Noetherian
object is injective, here applied to ring endomorphisms (which are not module
endomorphisms, so Mathlib's `IsNoetherian.injective_of_surjective_endomorphism`
does not apply directly). They are stated here only for use in the
characteristic-`p` linearization argument.
