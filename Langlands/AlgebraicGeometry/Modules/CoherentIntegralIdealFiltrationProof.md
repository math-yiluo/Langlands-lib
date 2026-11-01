# Coherent filtrations by integral closed ideal sheaves: proof

Author: Worker 716.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationStatement`,
which it imports unchanged (through the helper modules below).

## Main result

```lean
theorem coherentIntegralIdealFiltration : CoherentIntegralIdealFiltrationStatement.{u}
```

in namespace `Langlands.AlgebraicGeometry.Modules`, for an arbitrary universe `u`.
Unfolded: for every `X : Scheme.{u}` with `[IsNoetherian X]` and every `M : X.Modules`
which is quasi-coherent and has finite affine sections, there are `n : ℕ` and
`F : Fin (n + 1) → X.Modules` with `IsZero (F 0)`, an isomorphism `F (Fin.last n) ≅ M`,
every `F j` quasi-coherent with finite affine sections, and for every `j : Fin n` a
closed immersion `i : Z ⟶ X` from an integral scheme, a nonzero quasi-coherent module
`I` on `Z` with finite affine sections and a monomorphism `I ⟶ structureModule Z`, and
a short exact sequence `F j.castSucc ⟶ F j.succ ⟶ (Scheme.Modules.pushforward i).obj I`.

The theorem has no hypothesis beyond the statement's. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof combines two results.

1. `IntegralIdealFiltration.exists_mono_idealPushforward` (this module): every nonzero
   quasi-coherent `Q` on a noetherian scheme receives a monomorphism `φ : C ⟶ Q` from a
   module `C` satisfying `IsIdealPushforward C`. That is, `C` is isomorphic to the pushforward
   of a nonzero quasi-coherent ideal sheaf with finite affine sections on an integral scheme,
   along a closed immersion. The module `C` is moreover quasi-coherent, has finite affine
   sections, and is nonzero. The proof takes a `Witness` of `Q` (`nonempty_witness`, module
   `Witness`). It sets `C` to the pushforward `w.i_* w.I` of the ideal sheaf of admissible
   functions and `φ` to `w.phi` (module `Embedding`). The required properties are
   `w.isQuasicoherent_I`, `w.hasFiniteAffineSections_I`, `w.not_isZero_I`,
   `w.hasFiniteAffineSections_pushforward` and `w.not_isZero_pushforward` (modules
   `Quasicoherent`, `Embedding`). They also use `QuasicoherentLocal.isQuasicoherent_pushforward`
   from the Library, since a closed immersion is affine. The closed immersion instance for
   `w.i` comes from Mathlib, and the integrality instance from module `Witness`.
2. `IntegralIdealFiltration.filtered_of_core` (module `Filtered`) turns this core statement
   into `Filtered M`, and `Filtered.exists_chain` converts `Filtered M` into the statement's
   `Fin (n + 1)`-indexed form.

## Relation to the literature

The statement is Stacks Project Lemma 30.12.3, tag 01YF (`coherent.tex`, lines 3050–3141,
label `lemma-coherent-filter`, in the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`). The implemented proof follows a
different route from the Stacks proof. Stacks uses noetherian induction on the support,
Lemma 30.12.2, the ideal-power filtration, the `i_*` equivalence and an extension of
morphisms over an open subset. The Lean proof instead uses the following steps.

- An ascending chain argument. Among filtered subobjects of `M`, take one whose sections
  on a fixed finite affine cover are maximal. Its cokernel must vanish, since otherwise the
  core lemma produces a strictly larger filtered subobject.
- A minimal associated point. Choose a closed set `Zc`, minimal among those carrying a
  nonzero affine section killed by their vanishing ideal. Then `Zc` is the closure of a
  point, and `Q` has no nonzero section supported on a smaller closed set that is killed by
  the ideal.
- The ideal of admissible functions. On the reduced closed subscheme `Z` of `Zc`, the ideal
  consists of the functions `a` whose product `a · s` with the associated section `s`
  extends to a section of `Q` killed by the ideal. Its pushforward embeds into `Q` by
  sending `a` to this unique extension.

Only the conclusion, not the route, is taken from the source.

## Modules

All modules below are new and lie in `Langlands/AlgebraicGeometry/Modules/IntegralIdealFiltration/`.

| Module | Content |
| --- | --- |
| `Filtered` | `IsIdealPushforward`, inductive `Filtered`, `Filtered.exists_chain`, `filtered_of_core` |
| `Killed` | sections killed by an ideal sheaf; locality of sections |
| `MinimalPoint` | associated primes; `exists_minimal_witness` |
| `Witness` | the witness structure, the reduced closed subscheme, multiplication `mu` of `s` |
| `Extension` | `Agrees`, `InT`, uniqueness and gluing of killed extensions |
| `IdealSheaf` | the ideal sheaf `idealSub` of admissible functions on `Z` |
| `Embedding` | the monomorphism `phi : i_* I ⟶ Q`; nonvanishing |
| `Quasicoherent` | quasi-coherence and finiteness of `I` and `i_* I` |
