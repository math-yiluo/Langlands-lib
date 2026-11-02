# Twisting by a large power of an ample line bundle

`Langlands.AlgebraicGeometry.Picard.AmplePowerTwistStatement.{u}` is the
universe-polymorphic proposition

```lean
∀ (X : Scheme.{u}) (H N : LineBundle X), H.IsAmple →
  ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
    ∀ P : LineBundle X,
      Nonempty (P.obj ≅ tensorObj N.obj (tensorPow H.obj b)) → P.IsAmple
```

stated inside `namespace Langlands.AlgebraicGeometry.Picard` with
`open CategoryTheory AlgebraicGeometry` and `open Langlands.Scheme.Modules`.
In words: if `H` is an ample line bundle on a scheme `X` and `N` is any line
bundle on `X`, then there is a bound `b₀` such that, for every `b ≥ b₀`, every
line bundle whose module sheaf is isomorphic to `N ⊗ H^{⊗b}` is ample. The
bound `b₀` may depend on `X`, `H` and `N`, but not on `b` or `P`.

## The Lean interface

All names are the published Library ones, used unchanged.

- `LineBundle X`, from `Langlands.AlgebraicGeometry.Picard.LineBundle`, is
  the full subcategory of module sheaves `X.Modules` that are locally free of
  rank one. `P.obj`, `H.obj` and `N.obj` are the underlying module sheaves.
- `LineBundle.IsAmple`, from `Langlands.AlgebraicGeometry.Picard.Ample`,
  asserts that `X` is quasi-compact (`CompactSpace X`) and that every point
  lies in the generation locus `X_s` of a global section `s` of a positive
  tensor power `tensorPow L.obj n`, `n ≥ 1`, whose whole locus is affine. The
  generation locus is the published trivialization open: the largest open on
  which the morphism from the structure sheaf sending `1` to `s` is an
  isomorphism. This is the Lean form of Stacks Definition 27.1 (tag 01PS),
  where `X_s` is the locus on which `s` generates the stalk.
- `tensorObj` and `tensorPow`, from
  `Langlands.AlgebraicGeometry.Modules.Tensor`, are the sheafified tensor
  product of module sheaves and its right-associated iterates:
  `tensorPow M 0 = structureSheaf X` and
  `tensorPow M (n + 1) = tensorObj M (tensorPow M n)`. Thus at `b = 0` the
  module on the right is `N ⊗ O_X`, and `tensorPow H.obj 1` is `H ⊗ O_X`
  rather than `H` itself; such unit and associativity isomorphisms are left
  to proofs.
- The bundle `P` is any actual line bundle whose module sheaf is isomorphic,
  in `X.Modules`, to `tensorObj N.obj (tensorPow H.obj b)`. This is how the
  Library expresses a twist without choosing a line-bundle structure on the
  tensor product; the same transport formulation is used by the published
  `AmpleTensorStatement`, `PositiveTensorPowerAmpleStatement` and
  `AmpleIsoStatement`. Quantifying over all such `P` (rather than one chosen
  representative) is equivalent in strength, because ampleness is invariant
  under module-sheaf isomorphisms (`AmpleIsoStatement`, proved in the
  Library as `ampleIso`).

Every scheme in universe `u` is allowed, including empty and nonreduced
schemes. There is no field, finiteness, noetherian, separatedness,
properness or global-generation hypothesis, and no surrogate ampleness,
tensor product or tensor power. Ampleness of `H` already makes `X`
quasi-compact, and Stacks Lemmas 27.7 (tag 01PY) and 27.8 (tag 09MP), PDF
pp.42–43, show that a scheme with an ample invertible sheaf is separated,
so no separatedness premise is needed.

## Source and derivation

The registered original is `stacks-properties-chapter-2026-10-28`: The Stacks
Project, chapter *Properties of Schemes* (tag 01OH), PDF compiled
2026-07-14, file
`literature/Stacks Project — Properties of Schemes chapter (PDF compiled July 14, 2026).pdf`,
SHA-256 `2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`.
Numbers such as Proposition 27.13 are the PDF's own; tags are stable.

The Lean statement is a derived combination of two source results, not a
single numbered result of the source.

1. Proposition 27.13 (tag 01Q3), PDF pp.44–45, implication (1) ⇒ (7)
   (item tag 01QA). For a quasi-compact scheme `X` and an invertible sheaf
   `L`, if `L` is ample then `X` is quasi-separated and for every
   quasi-coherent `F` of finite type there is an integer `n₀` such that
   `F ⊗ L^{⊗n}` is globally generated for all `n ≥ n₀`. The proof of
   (1)–(6) ⇒ (7) is on p.45.
2. Lemma 27.5 (tag 0890, citing EGA II, Proposition 4.5.6(ii)), PDF p.42.
   If `L` is ample and the opens `X_t`, `t ∈ Γ(X, M^{⊗m})`, `m > 0`, cover
   `X`, then `L ⊗ M` is ample.

Derivation. Let `H` be ample. Then `X` is quasi-compact (Definition 27.1,
tag 01PS, PDF p.41), so Proposition 27.13 applies with `L = H`. The line
bundle `N` is quasi-coherent of finite type, so (7) gives `n₀` with
`N ⊗ H^{⊗n}` globally generated for all `n ≥ n₀`. For such `n`, every point
`x` has a global section `t` of `M = N ⊗ H^{⊗n}` that generates the stalk
`M_x`, that is `x ∈ X_t`; hence the opens `X_t` with `m = 1` cover `X`.
Lemma 27.5 with `L = H` and this `M` shows that
`H ⊗ (N ⊗ H^{⊗n})`, which is isomorphic to `N ⊗ H^{⊗(n+1)}`, is ample for
every `n ≥ max(n₀, 0)`. Since ampleness is invariant under isomorphism of
invertible sheaves, every line bundle isomorphic to `N ⊗ H^{⊗b}` is ample
for all `b ≥ b₀ := max(n₀, 0) + 1`. This is the Lean statement; the natural
number `b₀` replaces the source's integer bound `n₀`, which may be
negative.

## Scope and proof boundary

This module defines the proposition only; it proves nothing and installs no
axiom. At Library commit `facdf46f0abfca9e85d49d3a35285c513a96d886` there
is no Library notion of a globally generated module sheaf and no Serre-type
twisting theorem, so the proof successor must supply a Lean form of
(1) ⇒ (7) for line bundles or a direct argument (for instance covering `X`
by finitely many affine `X_{s_i}` and extending sections of `N` from them
after multiplying by powers of `s_i`, Stacks Lemma 18.2, tag 01PW, PDF
p.22). The published results `AmpleTensorStatement` (Lemma 27.5 when `M`
is itself ample), `PositiveTensorPowerAmpleStatement` and
`AmpleIsoStatement` are proved in the Library and may be imported.

The intended consumer is the proof route for
`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement`, which
reduces an arbitrary `N` to the ample bundles `N ⊗ H^{⊗b}`, `b ≥ b₀`. This
module imports only `Langlands.AlgebraicGeometry.Picard.Ample`, whose
import closure contains neither that statement nor
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`
(both live in modules under `Langlands.AlgebraicGeometry.Picard`).

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).
