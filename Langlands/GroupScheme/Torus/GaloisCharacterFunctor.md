# The contravariant Galois character functor

Worker 3483. This is a derived construction from the published actual character
groups, canonical descent transport and its naturality. Its field specialization
packages the character functor used in Milne's classification of groups of
multiplicative type. The implementation also applies to commutative ring
extensions, because its construction laws use only scheme pullback and
naturality.

## Objects and morphisms

Let `k` and `K` be commutative rings in the same arbitrary universe and let `K`
be a `k`-algebra. Write `b : Spec K → Spec k` for the structure morphism.
For every actual commutative `k`-group scheme `T`, the underlying module of
`characterLattice.galoisRep k K T` is

```text
X*(T_K) = Hom_CommGroupScheme(Spec K)(T_K, Gm_K).
```

Addition is pointwise multiplication of characters, and integer scalar
multiplication is the corresponding integer power. The action is exactly the
published `characterLattice.galoisRepresentation k K T` of `Aut_k(K)`.
The object is bundled in Mathlib's category `Rep ℤ (K ≃ₐ[k] K)`.
No new character group, group scheme or action is introduced.

For an actual morphism `f : H → G` over `k`,
`characterLattice.galoisPullback k K f` is the representation morphism

```text
X*(G_K) → X*(H_K),     χ ↦ f_K ≫ χ.
```

Here `≫` denotes diagrammatic composition: first `f_K`, then `χ`.
The equality `galoisPullback_apply` identifies the underlying map with this
actual composition. The auxiliary `characterLattice.pullback` constructs the
integral linear map for a morphism over any base scheme. Linearity follows from
bilinearity of composition in the published preadditive category of
commutative group schemes.

## Canonical equivariance and functoriality

Let `b : S → B`, let `a : S → S` satisfy `a ≫ b = b`, and let `f : H → G`
be an actual group homomorphism over `B`. The intrinsic helper
`transportCharacter_naturality` proves that transporting
`f_S ≫ χ` equals `f_S` followed by the transported character of `G_S`.
It applies even when `a` is not invertible and `H` and `G` are not commutative.

The helper is reused from
[CharacterGaloisAction](../Rational/CharacterGaloisAction.md). Its all-test
pointwise naturality identifies the same canonical transport morphisms.
`characterLattice.transport_naturality` rewrites this as an equality in the
actual additive character groups when the groups are commutative.

Specializing to `a = Spec σ` gives
`characterLattice.galoisRepresentation_naturality`:

```text
σ · (f_K ≫ χ) = f_K ≫ (σ · χ).
```

This equation supplies the intertwining law of `galoisPullback`; it is proved
without assuming equivariance as a premise.

The entry definition `characterLattice.galoisFunctor k K` has type

```text
(CommGroupScheme (Spec k))ᵒᵖ ⥤ Rep ℤ (Aut_k(K)).
```

It sends `op T` to `galoisRep k K T` and an opposite morphism to pullback along
its underlying group morphism. The identity law follows from preservation of
identities by base change. The composition law follows from preservation of
composition and associativity. In particular, for `H → G → J`, character
pullback goes from `X*(J_K)` to `X*(G_K)` and then to `X*(H_K)`.
`galoisFunctor_map_apply` gives the same actual precomposition formula for
the bundled functor.

## Source and scope

The registered original is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g, printed p.239 (PDF p.255), describes characters over a separable
closure, their canonical Galois action and their contravariant functoriality.
Theorem 12.23, printed p.240 (PDF p.256), uses that functor in the
multiplicative-type equivalence. The proof of Corollary 12.25 on the same page
uses a common finite Galois splitting extension. The original pages were read.
The complete retained official 2017 errata were checked; its Chapter 12
corrections do not affect these passages.

This unit constructs the functor on actual commutative group schemes with a
specified ring extension and its automorphism group. Its ring-level scope is
derived from the published scheme-level transport laws, rather than asserted
as a ring-level version of Milne's classification theorem. For a finite Galois
field extension it provides the actual integral Galois representation functor
used by the finite-level classification statements. It imposes no affineness,
finite type, splitting, smoothness, connectedness or freeness hypothesis.
Consequently its target is the entire representation category; no finite
generation of its objects is claimed. It constructs neither a restricted
multiplicative-type category nor an anti-equivalence, and proves no full
faithfulness, essential surjectivity, exactness or absolute-Galois continuity
theorem. Those assertions require their separate hypotheses and comparisons.
