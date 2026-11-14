# Scalar matrices acting through a Hecke character

Author: Worker 5137.

This helper module belongs to the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement` (Task 5210).
It prepares the proof in `Langlands.Automorphic.CentralCharacterTopCoefficient` that an
irreducible cuspidal realization has central character `δ` as soon as `δ_v(ϖ_v)` is the top
Satake coefficient at almost every place. The definitions `ScalarActsBy` and
`centralCharacterSubgroup` are internal tools of that proof, not notions from the
literature: they express "the scalar matrix of `z` acts by `χ(z)`" one idele at a time.

`F` is a number field. The file sets
`backward.isDefEq.respectTransparency false`, like other operator-realization files, to keep
unification on the realization spaces fast.

## Group-theoretic lemmas

- `Langlands.Global.FiniteAdelicGL.localInclusion_scalar_commute`: a scalar matrix
  `scalar a ∈ GL_n(F_v)` inserted at the place `v` commutes with every finite adelic matrix
  (check at each place with `ext_localProjection`).
- `Langlands.Global.AdelicGL.scalar_finiteIdeleInclusion`: the adelic scalar matrix of the
  local idele `finiteIdeleInclusion F v a` is `ofFinite` of the local scalar matrix
  `scalar a` inserted at `v`. Entrywise, with `IdeleDensity.coord_finiteIdeleInclusion`.
- `Langlands.Global.AdelicGL.scalar_diagonalUnits`: the scalar matrix of a principal idele
  `diagonalUnits F a` is the rational matrix `rational F n (scalar a)`.
- `Langlands.Global.CompletionPadic.subgroup_eq_top_of_uniformizer_mem`: a subgroup `G` of
  `F_v^×` containing the integral units and the canonical uniformizer `ϖ` is everything.
  Proof: for `a ∈ F_v^×` with valuation `exp m`, the element `a ϖ^m` has valuation `1`, so it
  is an integral unit, and `a = (a ϖ^m) (ϖ^m)⁻¹ ∈ G`.

## Namespace `Langlands.Automorphic.OperatorRealization`

Let `S : OperatorRealization F n` and `χ : HeckeCharacter F`.

- `ScalarActsBy S χ z`: for every `f` in the realization space and every
  `x ∈ GL_n(𝔸_F)`, `f(scalar z · x) = χ(z) f(x)`, where `χ(z)` is the central idele
  character `centralIdeleCharacter F χ z`.
  `scalarActsBy_one`, `scalarActsBy_mul`, `scalarActsBy_inv`: this holds for `z = 1` and is
  stable under products and inverses (because `scalar` and `centralIdeleCharacter` are
  homomorphisms).
- `centralCharacterSubgroup S χ`: the subgroup of ideles `z` with `ScalarActsBy S χ z`.
  `mem_centralCharacterSubgroup` unfolds membership.
- `isClosed_centralCharacterSubgroup`: it is closed. It is an intersection over `f` and `x`
  of the sets where two continuous functions of `z` agree.
- `diagonalUnits_mem_centralCharacterSubgroup`: it contains the principal ideles. Their
  scalar matrices are rational (`scalar_diagonalUnits`), automorphic forms are left
  invariant under rational matrices (`evaluate_rational`), and `χ` is trivial on principal
  ideles (`centralIdeleCharacter_principal`).
- `hasCentralCharacter_of_centralCharacterSubgroup_eq_top`: if the subgroup is `⊤`, then
  `S.HasCentralCharacter χ`. This is the characterization `hasCentralCharacter_iff`, with
  membership in `centralCharacterAutomorphicSubrepresentation`.
- Evaluation of `c • f` is `c` times evaluation of `f`. This is
  `evaluate_toContinuous_smul`, imported from
  `Langlands.Automorphic.OperatorRealizationEvaluation`.
- `evaluate_scalar_finiteIdeleInclusion`: left translation by the scalar matrix of a local
  idele `a ∈ F_v^×` equals the local action `S.localRepresentation v (scalar a)`. The scalar
  matrix is central (`AdelicGL.scalar_commute`), so left translation by it equals right
  translation, which is `finiteRepresentation` of the matrix inserted at `v`
  (`scalar_finiteIdeleInclusion`, `evaluate_finiteRepresentation`).
- `finiteIdeleInclusion_mem_centralCharacterSubgroup_iff`: `finiteIdeleInclusion F v a`
  lies in `centralCharacterSubgroup S χ` iff
  `S.localRepresentation v (scalar a) f = χ_v(a) • f` for all `f`, where
  `χ_v = χ.finiteComponent v`. The value of the central character on the local idele is
  `χ_v(a)` by definition. The two sides are compared after evaluation, using injectivity of
  `S.toContinuous` and of `toContinuousMap`.
- `localScalar_eq_smul_of_ne_zero`: if `S` is irreducible and the local scalar matrix
  `scalar a` at `v` acts by `c` on one nonzero vector `b`, then it acts by `c` on every
  vector. Proof: let `N` be the `c`-eigenspace of
  `e = localInclusion F n v (scalar a)` acting by `finiteRepresentation`. Since `e` is
  central in the finite adelic group (`localInclusion_scalar_commute`) and commutes with
  the compact and enveloping-algebra actions (`finiteRepresentation_compactRepresentation`,
  `finiteRepresentation_envelopingAction`), `N` is stable under all generators. It contains
  `b ≠ 0`, so it is everything (`eq_top_of_generatorStable`). Finally,
  `localRepresentation v` is `finiteRepresentation ∘ localInclusion`
  (`localRepresentation_apply`).
