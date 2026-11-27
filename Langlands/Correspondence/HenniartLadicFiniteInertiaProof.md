# Finite inertia image of irreducible ℓ-adic Galois representations

`Langlands.Henniart.ladicFiniteInertia` proves `Langlands.Henniart.LadicFiniteInertiaStatement`
of `Langlands.Correspondence.HenniartLadicStatement`, at its universe parameters
`uK, uΩ, uW`. The statement concerns:

- a nonarchimedean local field `K` of either characteristic, with separable closure `Ω`;
- a prime `ℓ` with `((ℓ : ℕ) : 𝓀[K]) ≠ 0`;
- a finite-dimensional representation `A` of `Ω ≃ₐ[K] Ω` over `PadicAlgCl ℓ` that is
  continuous (`IsLadicContinuous`), defined over a finite extension of `ℚ_[ℓ]`
  (`IsLadicDefinedOverFiniteExtension`) and irreducible.

Its conclusion is that the image of `absoluteInertia K Ω` is finite.

## Proof

The proof applies `Langlands.LadicMonodromy.finite_image_of_tameFrobenius`, from
`Langlands.Representation.LadicMonodromy`, with the following data:

- `G = Ω ≃ₐ[K] Ω` with its Krull topology, `I = absoluteInertia K Ω`, and
  `ρ = A.representation`;
- `φ`, `p = ringChar 𝓀[K]` and `q = Nat.card 𝓀[K]`, with `φ` and the tame Frobenius
  hypothesis supplied by `Langlands.LocalGalois.SepClosed.exists_tameFrobenius`;
- the neighbourhood hypothesis, supplied by
  `Langlands.LocalGalois.SepClosed.exists_normal_finiteIndex_subset`.

Both of these come from `Langlands.Galois.Local.TameFrobenius`. The remaining hypotheses are
checked as follows.

- `p` is prime, being the characteristic of the finite field `𝓀[K]`. It differs from `ℓ`,
  because `ℓ = p` would make `(ℓ : 𝓀[K]) = 0`. So `ℓ` and `p` are coprime
  (`Nat.coprime_primes`).
- `q ≥ 2`, since `𝓀[K]` is a finite nontrivial type (`Finite.one_lt_card`).
- In `E = PadicAlgCl ℓ`, `(ℓ : E) ≠ 0` because `E` has characteristic zero. Also
  `‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ < 1` by `PadicAlgCl.norm_extends` and `Padic.norm_p_lt_one`.
  The field `E` is algebraically closed, and its norm is ultrametric.
- Continuity is `IsLadicContinuous ℓ A` itself, the continuity of `A.representation` for the
  module topology on `Module.End E A`.
- Irreducibility, `IsSimpleOrder (Subrepresentation A.representation)`, gives the required
  form. A `ρ(G)`-stable submodule `W` defines a subrepresentation, which is `⊥` or `⊤`, so
  `W` is `⊥` or `⊤`.

The hypothesis `IsLadicDefinedOverFiniteExtension ℓ A` is not used. The argument works with
entrywise congruences in the ultrametric norm of `E` directly and needs no stable lattice or
finite coefficient field.

## Sources

Henniart deduces finiteness of the inertia image for ℓ-adic representations whose restriction
to inertia is irreducible from the structure of ℓ-adic representations, citing Deligne and
Tate (Henniart 1988, §4.1, pp. 509–510). The statement proved here assumes irreducibility
under the whole Galois group. The argument is Grothendieck's monodromy argument as in Tate's
account: an open subgroup of inertia acts through its tame quotient, Frobenius acts on it by
the `q`-th power, and the kernel of the monodromy is stable, so irreducibility makes the
monodromy trivial (Tate 1979, (4.1.5), p. 20, and (4.2)–(4.2.1), p. 21). The implemented
route is described in `Langlands/Representation/LadicMonodromy.md` and
`Langlands/Galois/Local/TameFrobenius.md`.

- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988),
  `henniart-1988-numerical`, §4.1, pp. 509–510. Retained PDF SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
- J. Tate, *Number theoretic background* (1979), `tate-1979-number-theoretic-background`,
  (4.1.5), p. 20, and (4.2)–(4.2.1), p. 21. Retained Corvallis Part II PDF SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- J.-P. Serre, *Local Fields* (1979), `serre-1979-local-fields`, IV §2, Proposition 7 and
  Corollaries 1 and 3, pp. 67–68. Retained PDF SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
