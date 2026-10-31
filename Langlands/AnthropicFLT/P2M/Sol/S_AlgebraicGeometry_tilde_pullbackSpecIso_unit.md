# The unit of the tilde adjunction is compatible with base change

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit` proves the theorem `P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit.solution`. Its statement is that of `AlgebraicGeometry.tilde.pullbackSpecIso_unit`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit` states under its FLT name.

## Statement

Let `φ : R ⟶ S` be a morphism of commutative rings in universe `u` and `M`
an `R`-module. Write `M~` for the sheaf of modules on `Spec R` associated
with `M`, and `tilde.pullbackSpecIso φ M : (Spec φ)^*(M~) ≅ (S ⊗_R M)~` for
the base-change isomorphism of the port
(`Definitions/Def_AlgebraicGeometry_ModulesTildePullback`). Then two maps
from `M` to the `R`-module of global sections of `(S ⊗_R M)~` agree:

- the unit at `M` of the composite adjunction (the tilde adjunction on
  `Spec R` followed by `pullbackPushforwardAdjunction (Spec.map φ)`),
  followed by global sections of the pushforward of
  `(tilde.pullbackSpecIso φ M).hom`, followed by the identification
  `Scheme.Modules.pushforwardSpecCompΓIso φ` of global sections of a
  pushforward with restriction of scalars;
- the unit `M ⟶ S ⊗_R M` of the extension–restriction of scalars
  adjunction, followed by the restriction of scalars of the unit
  `S ⊗_R M ⟶ Γ((S ⊗_R M)~)` of the tilde adjunction on `Spec S`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_unit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;
- the FLT file ends with the diagnostic command `#print axioms solution`,
  which only prints the axioms used and adds nothing to the environment; the
  port drops it.

## Proof outline

In the port, `tilde.pullbackSpecIso φ M` is the component at `M` of the
isomorphism `Adjunction.leftAdjointUniq` between two left adjoints of the
same functor: the composite adjunction above, and the composite of the
extension–restriction of scalars adjunction with the tilde adjunction on
`Spec S`, transported along `pushforwardSpecCompΓIso φ` by
`Adjunction.ofNatIsoRight`. `Adjunction.unit_leftAdjointUniq_hom_app` says
that the first unit followed by the right adjoint applied to this
isomorphism is the second unit. Unfolding the unit of `ofNatIsoRight` and of
a composite adjunction (`Adjunction.comp_unit_app`) and composing both sides
with the component of `pushforwardSpecCompΓIso φ` cancels the inverse of
that isomorphism and gives the stated equation.
