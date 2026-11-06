# Proof of proper coherent formal existence over complete local rings

`Langlands.AlgebraicGeometry.Modules.properFormalCoherentExistence` proves the
proposition `ProperFormalCoherentExistenceStatement.{u}` for every universe
`u`. Let `R` be a complete local noetherian ring with maximal ideal `m`, let
`f : X ⟶ Spec R` be proper, and let `F` be a `FormalModuleSystem f m` whose
terms are all locally finitely presented. Then there is a locally finitely
presented `M : X.Modules` with `FormalModuleSystem.IsAlgebraization M F`.

## The proof term

The theorem is a single application:

```lean
ProperFormalCoherentExistenceOfFLT.properFormalCoherentExistence_of_flt
  AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
```

- `properFormalCoherentExistence_of_flt` (module
  `Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT`)
  derives `ProperFormalCoherentExistenceStatement.{u}` from a hypothesis
  `hflt`. This hypothesis is an existence theorem for adic systems of
  coherent quasi-coherent module presheaves.
- `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`
  (module
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`)
  is the ported existence theorem of the Anthropic formalization of Fermat's
  Last Theorem. Its statement is the type of `hflt`, so the constant is passed
  unchanged. Lean checks that the two types agree.

The ported theorem is the presheaf form of Grothendieck's existence theorem
(EGA III 5.1.4, Stacks Project Tag 088C). Let `A` be a noetherian ring that is
complete for the `I`-adic topology, let `q : P ⟶ Spec A` be proper, and let
`F k` be coherent quasi-coherent `OModulePresheaf q`s. Let
`φ k : F (k+1) → F k` be maps that are surjective on every affine open, with
kernel `I^(k+1)` times the sections. Then there are a coherent quasi-coherent
`G` and compatible maps `ψ k : G → F k`. Each `ψ k` is surjective on every
affine open, with kernel `I^(k+1)` times the sections of `G`. Its proof
proceeds by Chow's lemma and a dévissage on the support. It uses Serre
vanishing on projective space, and it uses Artin–Rees bounds for Čech
cocycles. The ported modules (see below) and their paired Markdown files
describe this proof.

## The reduction `properFormalCoherentExistence_of_flt`

The modules written for this task prove the conditional theorem as follows.
Their own Markdown files give the details.

1. **Input presheaves** (`FormalModuleSystemPresheaves`). Each term `F_n` on
   the thickening `X_n` gives the presheaf `U ↦ Γ(F_n, p_n⁻¹ U)` on `X`, an
   `OModulePresheaf f`. It is quasi-coherent because `F_n` is locally finitely
   presented. It is coherent because, over an affine open `U`, the sections of
   `F_n` over `p_n⁻¹ U` are finite over `Γ(X_n, p_n⁻¹ U)`, and this ring is
   finite over `Γ(X, U)` since `p_n : X_n ⟶ X` is finite.
   The transition isomorphisms of `F` give maps `φ n` between consecutive
   presheaves. On every affine open, `φ n` is surjective with kernel
   `m^(n+1)` times the sections. This uses the sections of a quasi-coherent
   pullback on affine opens, which are a tensor product.
2. **Existence.** The hypothesis `hflt` with `A = R`, `I = m` and `q = f`
   gives a coherent quasi-coherent presheaf `G` and compatible maps
   `ψ n : G → F'_n`, where `F'_n` is the presheaf of step 1.
3. **Realization** (`CoherentPresheafRealization.exists_modules_sectionsEquiv`).
   `X` is locally noetherian, being of finite type over the noetherian `R`.
   So `G` is realized as a locally finitely presented sheaf `M : X.Modules`. On
   every affine open `U`, the sections `Γ(M, U)` are identified with `G(U)`,
   compatibly with restriction.
4. **Comparison** (`ProperFormalCoherentExistenceOfFLT`). On affine opens,
   the maps `ψ n` glue to morphisms `M ⟶ (p_n)_* F_n`. Their adjoints
   `p_n^* M ⟶ F_n` are bijective on sections over the inverse image of every
   affine open of `X`. These inverse images form a basis, so the adjoints are
   isomorphisms. They commute with the transition maps of `F` and with those
   of the restriction system of `M`, which gives
   `FormalModuleSystem.IsAlgebraization M F`.

## Supporting files and provenance

This candidate includes the port of the 265 FLT modules that the existence
theorem needs and that the Library did not yet contain. There are 5
`Definitions` modules, 130 `Theorems` statement modules and their 130
`P2M.Sol` proof modules, all under `Langlands/AnthropicFLT/`. They come from
the Anthropic Lean formalization of Fermat's Last Theorem, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (literature id
`anthropic-flt-complete-lean-source-6e837e75`). That source is licensed under
the Apache License, Version 2.0, Copyright 2026 Anthropic, PBC; see
`licenses/Anthropic-FLT/`. Each ported file has an attribution header. Its
paired Markdown lists every change against the FLT text and describes its
content. The changes are module renaming, lakefile options, dropping the
`P2M.Util` tactic import, and a small number of compatibility edits for the
project's Mathlib version.

The modules `FormalModuleSystemPresheaves`, `CoherentPresheafRealization`
and `ProperFormalCoherentExistenceOfFLT` were written for this task. Their
Markdown files state which parts are adapted from FLT files. The proof uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
