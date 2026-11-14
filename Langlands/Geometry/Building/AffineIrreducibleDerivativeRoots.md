# Irreducibility of an affine root system through its derivative roots

Module `Langlands.Geometry.Building.AffineIrreducibleDerivativeRoots`.

## Contents

The module compares the affine irreducibility predicate `IsIrreducibleRoots Ψ` (KP Definition
1.3.13, module `Langlands.Geometry.Building.AffineIrreducibleSimpleRoots`) with Mathlib's
irreducibility `RootPairing.IsIrreducible` of the finite root pairing of derivative roots. It
also gives a field-independent form of Mathlib's irreducibility, so that irreducibility can be
moved between root systems over different fields (for example a rational relative root system
and the real derivative roots of an apartment).

### Generic root pairings (namespace `RootPairing`)

Throughout, `K` is a field with `NeZero (2 : K)` (characteristic different from `2`), and
`P : RootPairing ι K M N` has `[P.IsRootSystem]` (roots span `M` and coroots span `N`). Mathlib's
`P.IsOrthogonal i j` means `P.pairing i j = 0 ∧ P.pairing j i = 0`.

- `RootPairing.isIrreducible_iff_forall_isOrthogonal P`:
  `P.IsIrreducible ↔ Nonempty ι ∧ ∀ s : Set ι, (∀ i ∈ s, ∀ j ∉ s, P.IsOrthogonal i j) →
  s = ∅ ∨ s = univ`.
  So a root system is irreducible in Mathlib's sense (nontrivial, and no nonzero proper
  submodule of `M` or of `N` invariant under all reflections, resp. coreflections) exactly when
  it has a root and its roots admit no partition into two nonempty mutually orthogonal parts.
- `RootPairing.isIrreducible_iff_of_equiv_pairing_eq_zero P P' e he`: for root systems
  `P : RootPairing ι K M N` and `P' : RootPairing ι' K' M' N'`, possibly over different fields
  `K`, `K'` (both with `NeZero 2`), and a bijection `e : ι ≃ ι'` with
  `he : ∀ i j, P.pairing i j = 0 ↔ P'.pairing (e i) (e j) = 0`, one has
  `P.IsIrreducible ↔ P'.IsIrreducible`.

### Affine root systems (namespace `Langlands.Geometry.Building.AffineRootSystem`)

Here `Ψ : Set (A →ᵃ[ℝ] ℝ)` is a set of affine functionals on a real affine space `A` over `V`
(independent universes `uV`, `uA`) with `hΨ : IsAffineRootSystemWithRankZero Ψ`, the Library form
of KP axioms AR 1–AR 4. The Library (module `SpecialPointExistence`) supplies the finite real root
pairing `hΨ.derivativePairing : RootPairing (derivativeRoots Ψ) ℝ (Module.Dual ℝ V) V` whose
roots are the derivatives `ψ̇` of the affine roots (`derivativeRoots Ψ`, as a subtype of `V*`) and
whose coroots are `hΨ.derivativeCoroot a`, the coroot vector of a chosen lift of `a`; its pairing is
`(a, b) ↦ a(hΨ.derivativeCoroot b)`. It is a root system by the published instance
`IsAffineRootSystemWithRankZero.derivativePairing_isRootSystem` (module
`AffineDerivativeRootPairing`), which the results below use. They are in namespace
`IsAffineRootSystemWithRankZero` and take `hΨ` as their first explicit argument.

- `derivativePairing_pairing_eq hψ hη hv`: for `ψ, η ∈ Ψ` and any `v` with `IsCoroot Ψ η v`,
  the pairing of the derivative roots `ψ̇` and `η̇` equals `ψ̇(v)`. So the pairing does not depend on
  the chosen lifts and coroot vectors.
- `isIrreducibleRoots_iff_forall_isOrthogonal`:
  `IsIrreducibleRoots Ψ ↔ ∀ s : Set (derivativeRoots Ψ),
  (∀ a ∈ s, ∀ b ∉ s, hΨ.derivativePairing.IsOrthogonal a b) → s = ∅ ∨ s = univ`.
- `isIrreducibleRoots_iff_isIrreducible`:
  `IsIrreducibleRoots Ψ ↔ Ψ = ∅ ∨ hΨ.derivativePairing.IsIrreducible`.
  (The empty set satisfies `IsIrreducibleRoots` vacuously, while Mathlib's irreducibility
  requires a root.)
- `isIrreducible_iff_isIrreducibleRoots hne`: for `hne : Ψ.Nonempty`,
  `hΨ.derivativePairing.IsIrreducible ↔ IsIrreducibleRoots Ψ`.
- `isIrreducible_iff_isIrreducibleRoots_of_equiv P e he`: for a root system
  `P : RootPairing ι K M N` over any field `K` with `NeZero (2 : K)` (`[P.IsRootSystem]`), a
  bijection `e : ι ≃ derivativeRoots Ψ` and
  `he : ∀ i j, P.pairing i j = 0 ↔ (e i).val (hΨ.derivativeCoroot (e j)) = 0`,
  `P.IsIrreducible ↔ Ψ.Nonempty ∧ IsIrreducibleRoots Ψ`.

No statement here is about algebraic groups. In particular, the module does not prove that the
relative root system of an absolutely almost-simple group is irreducible, and it does not compare
any group's relative roots with the derivative roots of an apartment; such a comparison is what a
user must provide as `e` and `he`.

## Provenance

- `IsIrreducibleRoots` is the formalization of Kaletha–Prasad, *Bruhat–Tits Theory: A New
  Approach* (2023), Definition 1.3.13 (printed p. 18, PDF p. 49), given in
  `AffineIrreducibleSimpleRoots`. `RootPairing.IsIrreducible`, `RootPairing.IsOrthogonal` and
  `RootPairing.IsRootSystem` are Mathlib's (`Mathlib/LinearAlgebra/RootSystem/Defs.lean`,
  `Irreducible.lean`).
- All results of this module are internal comparison lemmas between these two existing
  definitions; they transcribe no new statement from the literature. The characterization of
  irreducibility by orthogonal partitions is the standard one for finite root systems; here it
  is derived from
  Mathlib's lemmas `RootPairing.span_root_image_eq_top_of_forall_orthogonal`,
  `RootPairing.eq_top_of_mem_invtSubmodule_of_forall_eq_univ` and
  `RootPairing.IsIrreducible.mk'`.

## Proof notes

- **Partition form of irreducibility.** If `P` is irreducible then `M` is nontrivial, so `ι` is
  nonempty (otherwise the roots span `⊥ = ⊤`, making `M` trivial). Given an orthogonal partition
  with `s` nonempty, Mathlib's `span_root_image_eq_top_of_forall_orthogonal` says the roots in `s`
  span `M`. If some `j ∉ s` existed, the coroot form `P.coroot' j` would vanish on all roots in `s`
  (orthogonality), hence on `M`, contradicting `P.pairing j j = 2 ≠ 0`. So `s = univ`.
  Conversely, with a root `i₀` the module `M` is nontrivial (`P.root i₀ ≠ 0`); by
  `IsIrreducible.mk'` it suffices that every nonzero reflection-invariant `q ≤ M` is `⊤`, and
  `eq_top_of_mem_invtSubmodule_of_forall_eq_univ` reduces this to: every nonempty set `Φ` of roots
  lying in `q`, whose complementary roots are killed on `q` by the coroot forms, is everything.
  Such a `Φ` and its complement are orthogonal (`pairing_eq_zero_iff'` gives the second
  vanishing), so the hypothesis gives `Φ = univ`.
- **Transfer.** The partition property only involves the zero pattern of the pairing, which `e`
  preserves. Orthogonal partitions are transported by preimages under `e` and `e.symm`.
- **Affine comparison.** A set `s` of derivative roots corresponds to the partition
  `Ψ₁ = {ψ ∈ Ψ | ψ̇ ∈ s}`, `Ψ₂ = {ψ ∈ Ψ | ψ̇ ∉ s}`; conversely a partition `Ψ = Ψ₁ ∪ Ψ₂` gives
  `s = {ψ̇ | ψ ∈ Ψ₁}`. Through `derivativePairing_pairing_eq`, `RootsOrthogonal Ψ Ψ₁ Ψ₂` is
  orthogonality of the corresponding derivative roots. In the second direction, a `ψ ∈ Ψ₁` and
  `η ∈ Ψ₂` with the same derivative cannot occur in an orthogonal partition, because
  `ψ̇(η̇∨) = η̇(η̇∨) = 2`.
