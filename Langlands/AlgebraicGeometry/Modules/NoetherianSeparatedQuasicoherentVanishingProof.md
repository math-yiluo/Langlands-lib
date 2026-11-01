# Vanishing of quasi-coherent cohomology above the dimension: proof

Author: Worker 921.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`,
which it imports unchanged.

## Main result

```lean
theorem noetherianSeparatedQuasicoherentVanishing :
    NoetherianSeparatedQuasicoherentVanishingStatement.{u}
```

in namespace `Langlands.AlgebraicGeometry.Modules`, for an arbitrary universe `u`. Unfolded,
it says the following. Let `R : CommRingCat.{u}`, let `X : Scheme.{u}` with
`[IsNoetherian X]` and `[X.IsSeparated]`, let `f : X ⟶ Spec R` and `d : ℕ` with
`topologicalKrullDim X ≤ d`. Then for every `M : X.Modules` with `M.IsQuasicoherent` and every
`n : ℕ` with `d < n`, `IsZero ((DerivedSections.relativeCohomology f n).obj M)`.

The theorem has no hypothesis beyond the statement's. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof applies `NoetherianVanishing.isZero_relativeCohomology_of_height` with `e = d + 1`
and the closed set `Z = ⊤`, the whole space. Its three hypotheses hold:

- `IsAffineLocallyQuasicoherent M` holds because `M` is quasi-coherent
  (`IsAffineLocallyQuasicoherent.of_isQuasicoherent`).
- `M` vanishes off `⊤`. The complement of `⊤` is empty, and every module vanishes on the
  empty open set (`VanishesOn.bot`).
- Every irreducible closed `T` has `height T ≤ d` (`height_le_of_topologicalKrullDim_le`),
  that is, `height T < d + 1`.

So the cohomology vanishes in every degree `n ≥ d + 1`, which is the statement's `d < n`.

## Modules used

The proof uses five new helper modules, each with its own Markdown. Together they make one
argument. Positive-degree vanishing on affine schemes is the Library's
`affineQuasicoherentCohomologyVanishing`
(`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof`).

- `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Basic`: over an affine open `V`,
  quasi-coherence of `M.restrict hV.fromSpec` is equivalent to a localization property of the
  sections of `M` (`IsLocalizingAt`).
- `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Closure`: the property
  `IsAffineLocallyQuasicoherent` (quasi-coherence of the restriction to every affine open) is
  stable under kernels, cokernels, isomorphisms and pushforward along affine morphisms.
- `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Support`: vanishing of a module on an
  open set, and its behaviour under the unit `M ⟶ j_* (M|_V)`.
- `Langlands.AlgebraicGeometry.Modules.NoetherianVanishing.Topology`: a nonempty closed subset
  of a noetherian space contains an irreducible closed piece, cut out by an open set. Height in
  the poset of irreducible closed subsets is the dimension measure.
- `Langlands.AlgebraicGeometry.Modules.NoetherianVanishing.Induction`: the induction on the
  height bound `e` of the support, with a noetherian induction on the support for fixed `e`.

The route, in brief: choose an irreducible piece `T` of the support `Z` and an affine open `V`
meeting `Z` only inside `T`. The unit `M ⟶ j_* (M|_V)` has kernel supported on the smaller
closed set `Z \ V` and cokernel supported on `T \ V`, whose irreducible closed subsets have
smaller height. The cohomology of `j_* (M|_V)` vanishes in positive degrees because `j` is
affine (`X` is separated). Two long exact sequences finish the step. The helper Markdown files
give the details.

From the Library the proof uses `DerivedSections.relativeCohomology`,
`DerivedSections.relativeGlobalSections`, `DerivedSections.isIso_pushforwardComparison`,
`DerivedSections.pushforwardComparison`, `pushforwardInjectiveAcyclic`,
`PushforwardInjectiveAcyclic.toAbSheaf`, the `AffineVanishing` Čech results
(`IsCechAcyclic`, `isCechAcyclic_of_isQuasicoherent`,
`isZero_higherDirectImage_of_isCechAcyclic`, `spec_exists_pow_smul_eq_map`, `spec_exists_pow_smul_eq_zero`, `rres`, `res_smul`,
`restrictAppIso_hom_smul`, `image_fromSpec_top`, `image_fromSpec_le`), `Cech.res` and the
long exact sequence of `Langlands.Cohomology.RightDerivedSequence`.

## Provenance

The statement is derived from Stacks Tag 02UZ (Grothendieck vanishing, Tohoku Theorem 3.6.5)
and Tag 01F1; its Markdown records the sources and the derivation. This proof does not follow
the source's argument. The source proves vanishing for all abelian sheaves on a noetherian
space, by reducing to irreducible spaces and to the sheaves `j_! ℤ_U`. The Lean proof covers
only the quasi-coherent case, which is all the statement asks for. It stays inside
quasi-coherent modules: it uses affine vanishing, the affine pushforward comparison and the
unit `M ⟶ j_* (M|_V)` for affine opens `V`. Separatedness of `X` makes `V ⟶ X` affine.
