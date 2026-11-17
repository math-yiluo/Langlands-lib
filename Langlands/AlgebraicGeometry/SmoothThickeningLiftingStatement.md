# Smooth morphisms lift along nilpotent thickenings of affine schemes

The Prop-valued definition
`Langlands.AlgebraicGeometry.SmoothThickeningLiftingStatement.{u}` states:

```lean
∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] {C D : CommRingCat.{u}} (q : C ⟶ D),
  Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
    ∀ (x₀ : Spec D ⟶ X) (s : Spec C ⟶ S), x₀ ≫ f = Spec.map q ≫ s →
      ∃ x : Spec C ⟶ X, Spec.map q ≫ x = x₀ ∧ x ≫ f = s
```

In words: let `f : X ⟶ S` be a smooth morphism of schemes, and let
`q : C ⟶ D` be a surjective homomorphism of commutative rings whose
kernel is a nilpotent ideal. Then for every commutative square

```text
Spec D --x₀--> X
   |           |
Spec.map q     f
   |           |
   v           v
Spec C --s---> S
```

there is a morphism `x : Spec C ⟶ X` making both triangles commute:
`Spec.map q ≫ x = x₀` and `x ≫ f = s`.

Meaning of the hypotheses:

- `X` and `S` are arbitrary schemes in universe `u`. Neither is assumed
  affine, separated, quasi-compact, or noetherian. The point of the
  statement is that `X` need not be affine; for affine `X` and `S` it
  is the lifting property of formally smooth ring maps.
- `Smooth f` is Mathlib's `AlgebraicGeometry.Smooth`: for all affine
  opens `U ⊆ S` and `V ⊆ X` with `V ≤ f ⁻¹ᵁ U`, the ring map
  `Γ(S, U) → Γ(X, V)` is smooth (formally smooth and of finite
  presentation). This is the usual notion of a smooth morphism of
  schemes; no relative dimension is fixed.
- `C` and `D` are arbitrary commutative unital rings in universe `u`,
  including the zero ring. `Function.Surjective q.hom` makes
  `Spec.map q` a closed immersion with the same underlying topological
  space as `Spec C`.
- `IsNilpotent (RingHom.ker q.hom)` is nilpotency in the monoid of
  ideals of `C`: some power `(ker q)^n` is the zero ideal, so every
  product of `n` elements of the kernel vanishes. This includes the
  square-zero case `(ker q)^2 = 0` and the trivial case `q` bijective.
- The conclusion asserts existence only. Lifts are not unique, and no
  uniqueness or torsor structure on the set of lifts is stated.

## Original source and derived formulation

The original source is The Stacks Project Authors, *More on Morphisms*,
[Definition 37.11.1, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
(formally smooth morphisms of schemes) and
[Lemma 37.11.7, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
(infinitesimal lifting criterion), statements and proof, on pages 34–36
of the retained chapter PDF `more-morphisms.pdf`.

Definition 37.11.1 calls `f : X → S` formally smooth if every solid
commutative diagram with a first order thickening `T ⊂ T'` of affine
schemes over `S` and an `S`-morphism `a : T → X` admits a dotted
`S`-morphism `T' → X` extending `a`. Lemma 37.11.7 proves that a
morphism is smooth if and only if it is locally of finite presentation
and formally smooth; the direction used here is "smooth implies
formally smooth", proved there by showing that the sheaf of local
lifts is a torsor under the quasi-coherent sheaf
`Hom(a*Ω_{X/S}, C_{T/T'})` on the affine scheme `T` and using vanishing
of `H¹`. The notation corresponds as follows.

| Stacks notation | This statement |
| --- | --- |
| `T'` | `Spec C` |
| `T` | `Spec D` |
| `T → T'` | `Spec.map q` |
| `a : T → X` | `x₀` |
| `T' → S` | `s` |
| dotted arrow `T' → X` | `x` |

Two features of the present formulation are derived rather than taken
verbatim from the source.

1. **Presentation of the thickening.** In the source, `T ⊂ T'` is a
   closed subscheme of an affine scheme. For `T' = Spec C`, such a
   closed subscheme is `Spec (C/K)` for an ideal `K`, and a surjection
   `q : C ⟶ D` with kernel `K` identifies `D` with `C/K`. The statement
   is phrased with an arbitrary surjection `q`, which covers every such
   presentation up to isomorphism.
2. **Nilpotent instead of square-zero kernel.** The source treats first
   order thickenings, that is `K^2 = 0`. Here `K^n = 0` for some `n`.
   This is the standard consequence of the square-zero case: factor
   `C → C/K^(n-1) → ⋯ → C/K^2 → C/K ≅ D`, where each step
   `C/K^(m+1) → C/K^m` is surjective with kernel `K^m/K^(m+1)` of
   square zero (since `2m ≥ m+1`), and lift successively through the
   `n-1` first order thickenings. This paragraph explains the provenance
   of the formulation; this file supplies no formal proof of the
   reduction or of the lifting assertion.

The retained source is the folder
`literature/Stacks Project - Artin's Axioms, Smoothing Ring Maps, Formal Deformation Theory and More on Morphisms (PDF and tag snapshot 2026-11-06)/`,
registered as `stacks-artin-axioms-approximation-2026-11-06`, with
registered folder SHA-256
`f2f078895a7155a2277c0db49c51f80b73993f0439ffc51c35eb54e9b6e0990b`.
The chapter file `more-morphisms.pdf` in it has SHA-256
`59df05f5d52f453b17677398c72a51fe156367f460f6dcfdf764d9631b7c787c`;
the cited definition and lemma are on its pages 34 (Definition 11.1),
35 (Lemma 11.7, statement and first half of the proof), and 36 (rest of
the proof), numbered 37.11.1 and 37.11.7 in the full Stacks Project.

## Scope

The source remarks after Definition 37.11.1 that, unlike the formally
unramified and formally étale cases, the condition that `T'` be affine
cannot be dropped for formally smooth morphisms. Accordingly the
thickening here is always of the affine scheme `Spec C`; only the
target `X` and the base `S` are general. Lifting along thickenings of
non-affine schemes, uniqueness of lifts, the torsor structure on the
set of lifts, and the converse direction of Lemma 37.11.7 (formally
smooth and locally of finite presentation implies smooth) are outside
this definition.

This module defines the proposition only. An exact proof is a separate
successor. Worker 496 supplied the Lean formulation and this
description, as a prerequisite for lifting homomorphisms of group
schemes through nilpotent thickenings (SGA 3, Exposé IX, Théorème 3.6),
where the smooth group scheme `G` is not assumed affine.
