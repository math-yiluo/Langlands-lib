# Invariant-algebra obligations for finite étale quotients

This module defines three propositions in
`Langlands.AlgebraicGeometry.FiniteEtale`. It states algebraic prerequisites for
finite-group quotients of finite étale covers; it proves none of them and adds
no axioms or instances asserting their conclusions. All type parameters lie in
one arbitrary universe `u`.

## Parameters and invariant algebra

The first two definitions have explicit type arguments `R A G : Type u` and
exactly these common hypotheses:

```lean
[CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
[Module.Finite R A] [Algebra.Etale R A]
[Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
```

Thus `A` is finite as an `R`-module and étale as an `R`-algebra over a
noetherian commutative ring. The group acts on `A` by semiring automorphisms;
scalar compatibility makes these `R`-algebra automorphisms. The actual Mathlib
subalgebra `FixedPoints.subalgebra R A G`, denoted here by `C`, consists of
those `a : A` satisfying `g • a = a` for every `g : G`. Its inclusion is the
`R`-algebra homomorphism `C.val`. No replacement invariant algebra is defined.

There is no connectedness, field, or nontriviality assumption on `R`, no
invertibility assumption on the group order, and no freeness or faithfulness
assumption on the action. Both declarations retain every displayed hypothesis,
even when it is unnecessary merely to elaborate the proposition body.

## Finite étale closure

`InvariantAlgebraFiniteEtale R A G` is the conjunction, in this order,

```lean
Module.Finite R (FixedPoints.subalgebra R A G) ∧
  Algebra.Etale R (FixedPoints.subalgebra R A G)
```

The base is noetherian to match affine opens of the locally noetherian base in
the geometric quotient problem. The proposition concerns finiteness and
étaleness over `R`, not the quotient map from `A`.

## Geometric-point orbits

`InvariantAlgebraGeometricPoints R A G Ω` adds the explicit type argument
`Ω : Type u` and hypotheses `[Field Ω] [IsAlgClosed Ω] [Algebra R Ω]`.
It asserts first that restriction

```lean
fun x : A →ₐ[R] Ω => x.comp (FixedPoints.subalgebra R A G).val
```

is surjective onto `C →ₐ[R] Ω`, and second that for all `x y : A →ₐ[R] Ω`,

```lean
x.comp (FixedPoints.subalgebra R A G).val =
    y.comp (FixedPoints.subalgebra R A G).val ↔
  ∃ g : G, y = x.comp (MulSemiringAction.toAlgHom R A g)
```

These are actual algebra homomorphisms into the specified algebraically closed
field. Equality compares the entire restricted homomorphisms, not merely their
kernels. No nonempty geometric fibre is assumed: surjectivity also allows both
Hom sets to be empty.

For a left ring action, write `σ_g(a) = g • a`. Precomposition sends `x` to
`x ∘ σ_g`, and defines a right action on geometric points because
`(x ∘ σ_g) ∘ σ_h = x ∘ σ_(g*h)`. This is the contravariance of affine spectra.
The displayed orbit condition therefore needs no inverse; inserting inverses
would give the same existential orbit relation. It agrees with SGA 1's
convention of right scheme actions and left ring actions.

## Invariant numerators under localization

`InvariantAlgebraLocalization R A B G r _hequiv` has independent hypotheses:

```lean
(R A B G : Type u) [CommRing R] [CommRing A] [CommRing B]
[Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
(r : R) [IsLocalization.Away (algebraMap R A r) B]
[Group G] [Finite G]
[MulSemiringAction G A] [MulSemiringAction G B]
[SMulCommClass G R A] [SMulCommClass G R B]
(_hequiv : ∀ (g : G) (a : A),
  algebraMap A B (g • a) = g • algebraMap A B a)
```

The algebra tower makes the direct and composite maps `R → B` agree. The
explicit argument `_hequiv` requires equivariance of `A → B`; its underscore
only marks that this hypothesis is not used to form the proposition body.
The actions fix the image of `R`, hence the element being inverted. No
noetherian, finite-module, étale, or field hypothesis occurs here.

The conclusion is exactly

```lean
∀ b : B, (∀ g : G, g • b = b) →
  ∃ a : A, (∀ g : G, g • a = a) ∧
    ∃ n : ℕ, algebraMap A B a = algebraMap R B (r ^ n) * b
```

Thus every invariant localized element has an invariant numerator after
clearing one nonnegative power of `r`. This is only the elementwise
surjectivity part of invariants commuting with localization. It does not
construct a localization isomorphism or assert injectivity. It is intended
for use together with the existing localization zero criterion; the algebra
maps are not assumed injective and `r` need not be a non-zero-divisor.

## Original source and derived provenance

The registered original is Grothendieck et al., *SGA 1, Revêtements étales et
groupe fondamental*, recomposed edition, arXiv `math/0206203v2`, source
`sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
The following locations use printed pages and one-based PDF pages:

- Exposé V, Proposition 1.1 and Corollary 1.2, printed p.88 / PDF p.104:
  the affine quotient is the spectrum of the invariant ring; the ring extension
  is integral, prime fibres are group orbits, and residue-field extensions are
  algebraic and normal with the stabilizer surjecting onto their automorphism
  groups. Corollary 1.2 uses invariants commuting with localization at a
  multiplicative subset of the invariant ring.
- Exposé V, Proposition 1.8 and Corollary 1.8, printed p.90 / PDF p.106:
  admissibility is established using invariant affine opens, and the affine
  relative quotient is described by the invariant algebra sheaf. Proposition
  1.9 on that page states compatibility with flat base change.
- Exposé V, Proposition 3.1 and Corollary 3.2, printed p.96 / PDF p.112, and
  Corollary 3.4, printed p.97 / PDF p.113: over a locally noetherian base the
  quotient of a separated étale scheme of finite type is étale, the quotient
  map is étale, and a finite étale scheme has finite étale quotient.

The finite étale closure proposition is the internal affine-algebra translation
of Corollary 3.4, with the quotient identified by Proposition 1.1 and Corollary
1.8. It is not a verbatim algebraic statement in SGA 1.

The geometric-point proposition is a derived translation of Proposition
1.1(i)–(iii). Integrality provides primes above a given invariant-ring prime,
and algebraic residue extensions embed into an algebraically closed field,
extending the specified embedding. For equality of restrictions, the prime
orbit result first aligns the kernels; residual normality and surjectivity
of the stabilizer onto residue-field automorphisms then align the embeddings.
This extra residue-field step is essential: prime-ideal orbits alone do not
state the required Hom-orbit conclusion. The noetherian and finite étale
hypotheses are retained for the intended common interface, although this
source argument applies more generally.

The localization proposition is an internal elementwise consequence of the
localization formula in the proof of Corollary 1.2, restricted to powers of
the invariant element `algebraMap R A r`. It records only the invariant
numerator assertion explained above, rather than the source's full equality
of localized invariant rings.

These source comparisons explain the statement choices; no such derivations
are implemented as proofs in this module. In particular, no Galois-category
conclusion or classification by continuous group actions is imported or
assumed. Proofs of all three propositions and the later geometric assembly
remain separate obligations.
