<!-- MANUAL -->
# Absence of degenerate mirabolic submodules over packaged local fields

Lean module: `Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracy`,
namespace `Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy`.

This module proves Bernstein–Zelevinsky 1977, Theorem 4.9 (literature id
`bernstein-zelevinsky-1977-induced-i`, printed p. 456, PDF p. 17), for a packaged nonarchimedean
local field `F : Langlands.AllFieldBZ.LocalFieldPackage` with local-field structure
`T : F.TopologicalData` (the Library's `Langlands.LocalFieldData F.Carrier`), in any
characteristic. The theorem says: an irreducible nondegenerate representation of `GL_(n+1)(F)`
has no nonzero degenerate `P`-submodules. The formulation is that of the Library statement
`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyStatement`. Degeneracy of a `P`-submodule is
expressed by vanishing of its full upper-unipotent character quotient, and nondegeneracy of `ω` is
the Library's `IsGeneric`. The bridge
`Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyBridge` turns
`mirabolicNondegeneracy`, for all packages and data, into that Library statement.

## Origin

Worker 5677 wrote this argument as the p-adic draft module
`Langlands.Representation.Whittaker.PadicMirabolicNondegeneracy`, for `F : PadicField p`. That
draft is not published. This module is its mechanical all-field port, made by the port script of
Worker 71 with the systematic changes of the other all-field port modules, listed below. Every
declaration of the draft depends on the field, so the module neither imports nor uses the draft.
The module name keeps the draft's name.

## Statement

`mirabolicNondegeneracy T ψ n π`. Let `F : LocalFieldPackage` and `T : F.TopologicalData`, with
the topology `T.topology` on `F`. Let `ψ` be a unitary additive character of `F`, `n : ℕ`, and `π`
a complex representation of `GL_(n+1)(F)` on `V : Type uV`. Suppose `IsGeneric ψ n π`: `π` is
irreducible and admissible and has a nonzero standard Whittaker functional. Let `U` be a
subrepresentation of the restriction of `π` to the mirabolic group `P = mirabolic n F`. If the
coinvariants `Jacquet.Localization.Coinvariants U.toRepresentation (Mirabolic.upperUnipotent n F) θ`
are zero, then `U = ⊥`. Here `θ = (standardCharacter ψ n).comp
Mirabolic.upperUnipotentEquiv.toMonoidHom`. This is the conclusion of
`LocalFieldMirabolicNondegeneracyStatement`, with `F.Carrier` for `F`.

## Auxiliary lemmas

- `nontrivial_coinvariants_rankCast` and `hasNonzeroDerivative_top_iff` are the all-field versions
  of two lemmas of the Library module `Langlands.Representation.RankinSelberg.UnramifiedKirillovInjectivity`,
  which the p-adic draft copied to avoid that module's large import closure. The second says: a
  smooth `P`-representation `B` has a nonzero derivative of order `n + 1` iff its coinvariants for
  `Mirabolic.upperUnipotent n F` and `TopLocalization.mirabolicUpperCharacter ψ.complex n` are
  nonzero. Proof: by `mirabolicDerivativeOfOrder_top`, the top derivative is a rank cast of
  `mirabolicDerivative T ψ 0 n`. That is the coinvariant functor by
  `TopLocalization.mirabolicLocalizationIso`, and rank casts preserve nontriviality.
- `mirabolicUpperCharacter_eq_standardCharacter`: `TopLocalization.mirabolicUpperCharacter
  ψ.complex n` equals `θ` above. It is the definition together with
  `entrywiseCharacter_eq_standardCharacter`.

## Proof of `mirabolicNondegeneracy`

All derivative and Theorem 4.11 results used are the all-field versions in `Langlands.AllFieldBZ`.

1. **Bundling.** Admissibility includes smoothness, so `X0 = SmoothRep.of π` is a smooth
   representation. `X = SmoothRep.universeLift X0` moves it to the carrier `ULift V` in universe
   `max uF uV`, which is the universe of `exists_good_embedding`. `X` is irreducible by
   `SmoothRep.isIrreducible_universeLift_iff`.
2. **Nonzero top derivative.** Composing the given standard Whittaker functional with `ULift.down`
   gives a nonzero standard Whittaker functional on `X`. By
   `hasStandardFunctional_iff_nontrivial_topDerivative` (ported module
   `Langlands.AllFieldBZ.Representation.Whittaker.TopDerivativeDual`), the top derivative of `X` is
   nonzero.
3. **Good embedding.** `exists_good_embedding` gives an injective `j : X ⟶ P'` with `Good T ψ P'`.
   The restriction of `P'` to the mirabolic group is homogeneous of level `n + 1`
   (`level_of_good`).
4. **Contradiction.** Write `U = ⊥` as `U.toSubmodule = ⊥` and suppose `v ∈ U`, `v ≠ 0`. Let `U'`
   be the preimage of `U` under `ULift.moduleEquiv`. It is a subrepresentation of the mirabolic
   restriction `R` of `X`. Let `W` be the smooth subrepresentation of `R` on `U'`. It is nonzero,
   since it contains `ULift.up v`. The composite `W ⟶ R ⟶ P'|_P` is injective. By homogeneity
   (`hasNonzeroDerivative_of_isHomogeneous`), `W` has a nonzero derivative of order `n + 1`. By
   `hasNonzeroDerivative_top_iff`, its coinvariants for `TopLocalization.mirabolicUpperCharacter
   ψ.complex n` are nonzero. The linear equivalence `W ≃ U`, `x ↦ x.down`, is `P`-equivariant. The
   characters agree by `mirabolicUpperCharacter_eq_standardCharacter`. So
   `Jacquet.Localization.transportEquiv` identifies these coinvariants with those of `U`, which are
   zero by hypothesis. Contradiction.

Step 4 is the conclusion of the source's argument: `ω ≅ σ` is a submodule of `ρ_1 × ⋯ × ρ_r`,
which by Theorem 4.11 has no nonzero degenerate `P`-submodules. Here that property follows from
homogeneity of level `n + 1`.

## Systematic changes from the p-adic draft

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders.
- The namespace `Langlands.Whittaker.PadicMirabolicNondegeneracy` becomes
  `Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy`, and references to ported Library
  declarations `Langlands.X` use their all-field versions `Langlands.AllFieldBZ.X`.
- The docstring of `mirabolicNondegeneracy` says "over packaged nonarchimedean local fields"
  instead of "over p-adic fields" (a literal replacement in the port configuration).

## Provenance

Mathematics: Worker 5677 (p-adic draft); generated by the all-field port script of Worker 71.
