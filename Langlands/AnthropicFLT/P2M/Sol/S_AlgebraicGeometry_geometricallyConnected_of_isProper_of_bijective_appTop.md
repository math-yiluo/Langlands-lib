# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions, such as scoped notation and instances, of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces (line 28), which activates the same scoped extensions.
- Manual edit for Mathlib drift: in the proof of `P2mKcGeomConnFibres.isLocalRing_adjoinRoot`, FLT
  line 565 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫` is replaced by
  `Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) 𝔫` (lines 576–577 here). In the
  project's Mathlib the old name takes a ring homomorphism argument (Mathlib
  `RingTheory/Ideal/GoingUp.lean`); the new lemma states the same fact for the algebra map
  (the contraction to `R` of a maximal ideal of an integral `R`-algebra is maximal). The proved
  statement `h1` is unchanged.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the namespace header (which locally deactivate instances and simp lemmas declared in
  imported FLT modules) are kept unchanged.

## Content

Proof of Zariski's connectedness statement (namespace `P2mKcGeomConnFibres`). Notation:
`bc πX R γ` is the base change of `πX : X ⟶ Spec A` along `Spec R ⟶ Spec A`; `TrivialIdem R`
says the only idempotents of `R` are `0` and `1`.

- Algebra of `TrivialIdem`: transfer along ring isomorphisms and along maps with nil kernel; a
  nontrivial artinian ring with trivial idempotents is local with nilpotent maximal ideal
  (`isLocalRing_of_isArtinianRing`, `isNilpotent_of_mem_maximalIdeal`, both assuming `Nontrivial R`;
  the zero ring is artinian with trivial idempotents but is not local); for a purely
  inseparable field extension `ℓ/κ`, `k ⊗_κ ℓ` has trivial idempotents; a finite `κ`-algebra `L`
  with trivial idempotents such that every `AdjoinRoot P ⊗_κ L` (`P` monic irreducible) has trivial
  idempotents stays so after any field base change (`trivialIdem_baseChange`). Its proof first
  treats the case where `L` is the zero ring, in which `k ⊗_κ L` is also zero. Otherwise `L` is
  artinian and nontrivial, hence local with nilpotent maximal ideal. Its residue field `ℓ` is
  purely inseparable over `κ`, since separable elements lie in the image of `κ`
  (`mem_range_of_isSeparable_of_trivialIdem`), and `k ⊗_κ L → k ⊗_κ ℓ` has nil kernel, so the
  trivial idempotents of `k ⊗_κ ℓ` transfer to `k ⊗_κ L`.
- Schemes: a scheme is preconnected iff its global sections have trivial idempotents
  (`trivialIdem_of_preconnectedSpace`, `preconnectedSpace_of_trivialIdem`).
- Fibres: flat base change preserves bijectivity of `appTop` (`bijective_appTop_snd_of_flat`, via
  `isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`); for a noetherian local ring `B` over
  which the base change is proper with `Γ = B`, the fibre over the residue field `E` is
  preconnected (`preconnectedSpace_bc_of_surjective`, from
  `isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`); global sections of a
  fibre over an extension field `F` of `κ` are `F ⊗_κ Γ(fibre over κ)` (`nonempty_ringEquiv_bc_tensor`,
  flat base change). `AdjoinRoot P` over a local ring is local when `P` is monic with irreducible
  reduction (`isLocalRing_adjoinRoot`).
- Main (`preconnectedSpace_bc_of_isAlgClosed`): for `φ : A → k`, `k` algebraically closed, with
  kernel `𝔭`, let `R = A_𝔭` with residue field `κ`. `L = Γ(fibre over κ)` is finite over `κ`
  (`finite_appTop_of_isProper_of_isNoetherianRing`) with trivial idempotents (fibre over the closed
  point of `R`); for `P` monic irreducible over `κ`, lift it to a monic `P̃` over `R`, so
  `B = AdjoinRoot P̃` is a finite free local `R`-algebra and the fibre over its residue field
  `AdjoinRoot P` is preconnected, giving trivial idempotents of `AdjoinRoot P ⊗_κ L`. Hence
  `k ⊗_κ L = Γ(fibre over k)` has trivial idempotents and the geometric fibre is preconnected.
- Corollaries: the fibre over any field is preconnected (pass to an algebraic closure) and
  nonempty, hence connected, so `πX` is geometrically connected (`geometricallyConnected`).
  `solution` applies it.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.TrivialIdem`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_of_subsingleton`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_of_surjective_of_ker_nil`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_of_ker_nil`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_of_ringEquiv`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.isNilpotent_or_isUnit_of_isArtinianRing`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.isLocalRing_of_isArtinianRing`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.isNilpotent_of_mem_maximalIdeal`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.ker_lTensor_nil`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_tensor_of_isPurelyInseparable`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.mem_range_of_isSeparable_of_trivialIdem`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_baseChange`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.nontrivial_sections_of_nonempty`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.trivialIdem_of_preconnectedSpace`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.preconnectedSpace_of_trivialIdem`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.preconnectedSpace_of_iso`
- abbrev `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.bc`
- def `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.bcCompIso`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.preconnectedSpace_bc_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.nonempty_ringEquiv_bc_tensor`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.bijective_appTop_snd_of_flat`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.isLocalRing_adjoinRoot`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.preconnectedSpace_bc_of_isAlgClosed`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.exists_factor_residueField`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.surjective_fst_bc_field`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.preconnectedSpace_bc`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.nonempty_bc`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.connectedSpace_bc`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.P2mKcGeomConnFibres.geometricallyConnected`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing` (same contribution).
All modules also import `Mathlib`.
