# Reductivity through a semisimple representation with finite kernel

`Langlands.GroupScheme.ReductiveFiniteKernelRepresentationStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field with `[PerfectField k]`, and
let `G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`. Then

```text
IsConnectedReductive G ↔
  ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
    sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤ ∧
      IsFinite (kernel ρ).X.hom
```

In words: a smooth connected affine group over a perfect field is reductive
if and only if it has a semisimple finite-dimensional representation whose
kernel is finite.

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` (from [`Basic`](Basic.md)) says that `G` is
  smooth, affine and connected over `k`, and that the unipotent radical of
  its base change to an algebraic closure of `k` is trivial. `Basic.md`
  relates this structure to Milne's definition 6.46 of a reductive group.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, a representation of `G` on `kⁿ`.
  Every finite-dimensional representation is isomorphic to one of these.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for every commutative `k`-algebra `A`
  and every point `x` of `G` with values in `A` (it is stated through
  `k`-linear maps `A → k`, which detect `W ⊗ A` inside `Aⁿ`). The stable
  subspaces are the subrepresentations, and the set inside `sSup` is the set
  of simple subrepresentations. So the first conjunct says that `ρ` is
  semisimple: the sum of its simple subrepresentations is `kⁿ`. The same
  condition is used in `SemisimpleRepresentationUnipotentStatement` (in
  [`SemisimpleRepresentationUnipotentStatement`](SemisimpleRepresentationUnipotentStatement.md)).
- `kernel ρ` (from [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md))
  is the scheme-theoretic kernel of `ρ`, the fibre product of `ρ` with the
  unit section of `GL_n`, a group scheme over `Spec k`. `IsFinite`
  (Mathlib) says that its structure morphism to `Spec k` is finite: the
  kernel is a finite group scheme.
- `PerfectField k` (Mathlib) says that `k` is perfect.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is the equivalence of (a) and (d) in Proposition 21.60,
printed p. 442: "Let G be a connected group variety over a perfect field k.
The following conditions on G are equivalent: (a) G is reductive; (b) The
radical R(G) of G is a torus; (c) G is an almost-direct product of a torus
and a semisimple group; (d) G admits a semisimple representation with finite
kernel." Its proof of (d) ⇒ (a): "The unipotent radical of G acts trivially
on semisimple representations of G (see 19.16). Hence (d) implies that it
is finite, but, by definition it is connected and smooth, and so it is
trivial (2.17). As k is perfect, this implies that G is reductive (19.11)."
Conditions (b) and (c) are not part of the Lean statement.

Definitions used by the source:

- Group varieties, printed p. 6: "When G is a variety, we call (G, m) a group
  variety". Printed p. 12: "Therefore 'group variety' = 'geometrically
  reduced algebraic group'." Proposition 1.28, printed p. 14: an algebraic
  group is smooth if and only if it is geometrically reduced. Algebraic
  groups are of finite type (printed p. 3: "An algebraic scheme over k (or
  algebraic k-scheme) is a scheme of finite type over k"; printed p. 6: "An
  algebraic group over k is a group object in the category of algebraic
  schemes over k").
- Affineness, printed p. 162 (end of Chapter 8): "We now concentrate on
  affine algebraic groups. By 'algebraic group' we shall mean 'affine
  algebraic group' and by 'group variety' we shall mean 'affine group
  variety'." Later chapters repeat this (for example Chapter 18, printed
  p. 387: "Recall that all algebraic groups are affine over a base field
  k").
- Reductive groups: printed p. 400, "Recall (6.46) that an algebraic group G
  over a field k is said to be reductive if it is smooth and connected and
  the unipotent radical of G_{k^a} is trivial."
- Semisimple representations: Definition 4.15, printed p. 90, "It is
  semisimple if it is a sum of simple subrepresentations."
- Kernels, printed p. 23: "The kernel of a homomorphism φ: G → H of
  algebraic groups is defined to be the following fibred product:
  Ker(φ) = G ×_H e". Finite algebraic groups, 2.14, printed p. 44: "An
  algebraic group G over k is finite if it is finite as a scheme over k."

The provenance is derived for these reasons.

- The group. Milne's connected group variety (affine, by the convention of
  printed p. 162) is a smooth, connected, affine algebraic group, which is
  what the instances `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
  `[ConnectedSpace G.X.left]` say; finite type follows from smoothness.
- Reductive. Milne's "reductive" is `IsConnectedReductive G`, as recorded
  in [`Basic`](Basic.md).
- The representation. A representation of `G` on a finite-dimensional
  vector space is a homomorphism `G → GL_V`; choosing a basis gives
  `ρ : G ⟶ GL_n`, and the existential quantifier ranges over all of these.
  "Semisimple" is the `sSup` condition, and "with finite kernel" is
  `IsFinite (kernel ρ).X.hom`, with Milne's kernel as the fibre product with
  the identity section.
- One universe `u` is used for `k` and the schemes. This is a formalization
  convention.

The hypothesis that `k` is perfect is needed for (d) ⇒ (a). Over an
imperfect field `k` of characteristic `p` with `a ∈ k ∖ k^p`, let
`k′ = k(a^{1/p})` and let `G` be the Weil restriction of `𝔾_m` from `k′` to
`k` (its points over a `k`-algebra `R` are the units of `k′ ⊗_k R`), a
smooth connected commutative group of dimension `p`. Over `k^a`,
`k′ ⊗_k k^a ≅ k^a[t]/(t^p)`, and the units with constant term `1` form a
smooth connected normal unipotent subgroup of `G_{k^a}` of dimension
`p − 1 > 0`, so `G` is not reductive. The representation of `G` on `k′` by
multiplication is faithful, so its kernel is trivial, and it is simple: a
stable subspace is in particular stable under the `k`-points `k′^×` of `G`,
hence is a `k′`-subspace of `k′`, which is `0` or `k′`. (This example is not
used by the Lean statement.)

Relation to the Library. The Library proves this statement as
`reductiveFiniteKernelRepresentation` (in
`ReductiveFiniteKernelRepresentationProof`). Related statements:

- `SemisimpleRepresentationUnipotentStatement` (in
  [`SemisimpleRepresentationUnipotentStatement`](SemisimpleRepresentationUnipotentStatement.md),
  Milne's 19.16 and 19.17) says that normal unipotent subgroups act
  trivially on semisimple representations, and that a smooth connected
  group with a faithful (closed immersion) semisimple representation has
  trivial unipotent radical over `k`.
- `PerfectFieldPseudoReductiveStatement` (in
  [`PerfectFieldStatement`](PerfectFieldStatement.md)) says that over a
  perfect field `IsPseudoReductive G ↔ IsConnectedReductive G`.
- `GeometricallySemisimpleRepresentationReductiveStatement` (in
  [`GeometricSemisimpleRepresentationReductiveStatement`](GeometricSemisimpleRepresentationReductiveStatement.md),
  Milne's 19.18) deduces reductivity from a faithful representation that is
  semisimple and stays semisimple over an algebraic closure, over any field.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Proposition 21.60
on printed p. 442 with the same hypotheses and the same four conditions.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 3, 6, 12, 14, 23, 44, 90, 162, 387, 400 or 442. The
errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed p. 442.

## For the proof (not part of this module)

The Library proves the statement as `reductiveFiniteKernelRepresentation` in
`ReductiveFiniteKernelRepresentationProof`.

- (⇐). Let `ρ` be semisimple with finite kernel. By
  `SemisimpleRepresentationUnipotentStatement` (first conjunct), every
  smooth connected normal unipotent closed subgroup `U` of `G` acts
  trivially through `ρ`, so `U` lies in the finite kernel; being connected
  and smooth, it is trivial. Hence `G` has trivial unipotent radical over
  `k`, that is, `G` is pseudo-reductive, and `PerfectFieldPseudoReductiveStatement`
  gives `IsConnectedReductive G`.
- (⇒). Choose a faithful representation `V` of `G` (Milne 4.9) and a
  composition series `0 = V_0 ⊂ ⋯ ⊂ V_r = V` of subrepresentations with
  simple quotients. The direct sum `⨁ V_i / V_{i−1}`, written in a basis, is
  a semisimple representation `ρ`. Its kernel `N` acts trivially on every
  `V_i / V_{i−1}`, so it is a normal unipotent subgroup of `G`. Over `k^a`,
  the identity component of the reduced subgroup of `N_{k^a}` is a smooth
  connected normal unipotent subgroup of `G_{k^a}`, hence trivial because
  `G` is reductive; so `N` is finite.
