# Bounded real points of closed tori in anisotropic groups over `ℝ`

This helper module proves that a closed torus of an anisotropic group over `ℝ` has bounded
matrix entries on its real points, in every matrix representation. It is the real analogue of
the compactness of anisotropic tori over non-archimedean local fields
(`IsAnisotropic.isCompact_univ_of_isTorus`).

## Declarations

- `RealAnisotropicTorus.isCompact_preimage_algebraMap`: for a finite extension `E` of `ℝ`
  with its module topology, the preimage in `ℝ` of a compact subset of `E` under
  `algebraMap ℝ E` is compact. (The inclusion is a closed embedding,
  `LinearMap.isClosedEmbedding_of_injective`.)
- `RealAnisotropicTorus.exists_abs_rationalPointAlgebraHom_le`: let `G` be anisotropic over
  `ℝ`, and `i : T ⟶ G` a closed subgroup with `IsTorus T.toGrp` (and `T` affine, locally of
  finite type). For every global function `f` of `T` there is `α` with
  `|f(s)| ≤ α` for every real point `s` of `T`. Here `f(s)` is
  `rationalPointAlgebraHom ℝ T.X s f`.
- `RealAnisotropicTorus.rationalMatrix_map_apply_apply`: the entry `(j, l)` of
  `ρ.rationalMatrix (rationalPoints.map i s)` is the value at `s` of the global function
  `(i ≫ ρ)^*(entry j l)` of `T`.
- `IsAnisotropic.exists_abs_rationalMatrix_le_of_closedTorus` (main result): let `G` be a
  group scheme over `ℝ` with `IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom` and
  `IsAnisotropic G`, let `ρ : MatrixRepresentation G n`, and let `i : T ⟶ G` be a closed
  torus. Then there is `α` with `|ρ(i(s)) j l| ≤ α` for every real point `s` of `T` and all
  `j l`.

## Proof

The proof of `exists_abs_rationalPointAlgebraHom_le` follows the Library's proof of
`Langlands.Plancherel.torusNormKernelCompactness` with `ℝ` in place of a non-archimedean
local field.

1. `torusFiniteGaloisSplitting` gives a finite Galois extension `E/ℝ` and an isomorphism `e`
   of `T_E` with a split torus `𝔾ₘ^I`.
2. `exists_continuous_of_splitCharacters e` gives a continuous `Φ : (I → Eˣ) → E` with
   `f_E(s') = Φ(χ_i(s'))` for the coordinate characters `χ_i = splitCharacter e i` of `T_E`.
   `rationalPointAlgebraHom_rationalExtend` gives `f_E(s_E) = algebraMap ℝ E (f(s))` for a real
   point `s`.
3. `T` is a closed torus in an anisotropic group, so
   `IsAnisotropic.algebraNorm_characterEval_eq_one_of_closedTorus` gives
   `Algebra.norm ℝ (χ_i(s_E)) = 1`. The set `KU = {u : Eˣ | ‖Algebra.norm ℝ u‖ = 1}` is
   compact by the Library's `isCompact_units_algebraNorm_eq_one`, which holds over every
   nontrivially normed field with compact closed balls, in particular over `ℝ`.
4. So `f(s)` lies in the preimage under `algebraMap ℝ E` of the compact set
   `Φ(KU^I)`, which is compact by `isCompact_preimage_algebraMap` and hence bounded.

The main result applies this to the functions `(i ≫ ρ)^*(entry j l)` and takes the sum of the
absolute values of the finitely many bounds. The instances `IsAffineHom` and
`LocallyOfFiniteType` for `T` come from the closed immersion `i`.

## Provenance (internal)

An internal step of the compactness half of `RealAnisotropicCompactConnectedStatement`
(Borel–Tits, *Groupes réductifs* (1965), Corollary 9.4, printed p.127, for `k = ℝ`). The
statement is the archimedean counterpart of the Library's non-archimedean
`IsAnisotropic.exists_isCompact_powers_map_of_closedTorus`.
