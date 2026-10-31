# Proof: the Mumford map of the diagonal Poincaré pullback of a polarization is `2 λ`

Module `Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof`.

## Main theorem

`Langlands.AbelianScheme.polarizationDiagonalMumford : PolarizationDiagonalMumfordStatement.{u}`
proves the Library statement `Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement`
(module `Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordStatement`;
Mumford, Fogarty, Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 6.10). For a relative
polarization `λ : A ⟶ A^∨`, the line bundle `(1, λ)^* P` has unit-section normalization data
`B`, `evaluationB`, `M`, `evaluation`, and its Mumford map `Λ((1, λ)^* P)` is the scheme map of
`2 • λ`. The proof uses only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The constructor hypotheses of the statement are used as hypotheses, together
with the Library's proved theorems `factorizationOfGlobalFunctions`,
`smoothProperConnectedGlobalFunctions` and `picardZeroLineBundleClassification`.

Proof. The normalization data are chosen with the Library's
`LineBundle.exists_tensorObj_iso_structureSheaf`: `B` is an inverse of `e^* (1, λ)^* P` on `S`
(`e` the unit section), and `M` is an inverse of the normalized bundle. Since `2 • λ = λ + λ`
(`two_nsmul`) and addition of homomorphisms of abelian schemes is the pointwise product,
the scheme map of `2 • λ` is `λ₀ * λ₀` by `rfl`, where `λ₀ = (groupHom λ).hom.hom`. The
result is then `mumfordSchemeMap_poincareDiagonal_eq_mul`, whose point hypothesis is
`IsPolarization.exists_poincareSliceSymmetric`.

## Auxiliary lemmas

- `eq_one_of_forall_point` (rigidity): let `A`, `D` be abelian schemes over `S` and
  `d : A.X ⟶ D.X` with `1 ≫ d = 1` (`d` maps the unit section to the unit section). Assume
  every point `x` of `A.X.left` is `t.left z` for some `t : T ⟶ A.X` and `z` with
  `t ≫ d = 1`. Then `d = 1`.

  Proof. For each point `y`, choose such `t` and `z`. Then `t.left ≫ d.left` is
  `T.hom ≫ e_D`, so `d(y) = (e_A ≫ d)(p(y))` with `p : A ⟶ S` the structure map. The
  Library's `factorizationOfGlobalFunctions` (with `smoothProperConnectedGlobalFunctions` for
  the smooth, proper, geometrically connected `p`) then gives `d = p ≫ e_A ≫ d = p ≫ e_D`,
  the unit point (`unitPoint_left`).
- `IsPolarization.exists_poincareSliceSymmetric`: if `λ` is a polarization, then every
  point `x` of `A` is `t.left z` for a point `t : T ⟶ A.X` such that `T.left` has exactly one
  point and `PoincareSliceSymmetric A hA λ₀ t` holds.

  Proof. Let `K` be an algebraic closure of the residue field `κ(x)` and
  `s : Spec K ⟶ Spec κ(x) ⟶ A ⟶ S`. The second component of `IsPolarization` at `(K, s)`
  provides a field extension `φ : K →+* K'` such that, on `A_{K'} = (A_K)_{K'}`, the twice
  base-changed map `dualBaseChangeMap … (dualBaseChangeMap … s λ₀)` equals the Mumford map
  of a line bundle `L₂` with normalization data (`hf2`). The ampleness of `L₂` and the
  isogeny condition are not used. Let `t₂ : Spec K' ⟶ A_{K'}` be the `K'`-point given by `x`.
  By `poincareSliceSymmetric_mumfordSchemeMap` (module `PoincarePointClasses`), the
  slices of that Mumford map are symmetric at `t₂`. Two applications of
  `poincareSliceSymmetric_of_baseChange` (module `PoincareSliceSymmetryBaseChange`) carry the
  symmetry down to `A_K` and then to `A`. The resulting point of `A` has underlying morphism
  `Spec K' ⟶ Spec K ⟶ Spec κ(x) ⟶ A` (`pullback.lift_fst` twice), so it hits `x`
  (`Scheme.fromSpecResidueField_apply`), and `Spec K'` has exactly one point.
- `mumfordSchemeMap_poincareDiagonal_eq_mul`: for `λ₀ : A.X ⟶ A^∨.X` with `[IsMonHom λ₀]` and
  normalization data for `(1, λ₀)^* P`, if every point of `A` is hit by a point over a
  one-point scheme at which the Poincaré slices of `λ₀` are symmetric, then
  `Λ((1, λ₀)^* P) = λ₀ * λ₀`.

  Proof. Let `g = Λ((1, λ₀)^* P)` and apply `eq_one_of_forall_point` to `g / (λ₀ * λ₀)`; then
  `div_eq_one` gives the claim. At the unit, `η ≫ g = η` is the Library's
  `mumfordSchemeMap_unit` and `1 ≫ λ₀ = 1` (`MonObj.one_comp`). At a point `t` from the
  hypothesis, `t ≫ g = (t ≫ λ₀) * (t ≫ λ₀)` is `comp_mumfordSchemeMap_poincareDiagonal`
  (module `PoincareDiagonalClasses`), and composition distributes over `/` and `*`
  (`GrpObj.comp_div`, `MonObj.comp_mul`).

## Helper modules

The proof uses these new modules, all part of this contribution:

- `LineBundleIsoClassGroup`: the commutative group of isomorphism classes of line bundles,
  with pullback as a homomorphism;
- `PoincareSliceSymmetry`: the proposition `PoincareSliceSymmetric`;
- `PoincarePointClasses`: point classes of families; Mumford maps have symmetric slices;
- `PoincareSliceSymmetryBaseChange` (by Worker 943): descent of slice symmetry along base
  change;
- `PoincareDiagonalClasses`: bilinearity of Poincaré classes and the pointwise identity
  `t ≫ Λ((1, λ₀)^* P) = (t ≫ λ₀)^2`.

## Comparison with the literature

GIT's proof of Prop. 6.10 (3rd ed., printed p. 121) reduces the relative statement to the
case `S = Spec k` with `k` algebraically closed by Corollary 6.2. There `λ = Λ(L)` for a line
bundle `L` on the abelian variety, and it suffices that `L^Δ(λ) ⊗ L^{-2}` is algebraically
equivalent to `0`, where `L^Δ(λ) = (1, λ)^* P`. GIT writes `(1, λ) = (1 × λ) ∘ Δ` and uses
`(1 × λ)^* P ≅ μ^* L ⊗ p₁^* L^{-1} ⊗ p₂^* L^{-1}` to get `L^Δ(λ) ≅ [2]^* L ⊗ L^{-2}`. The
classical fact that `[2]^* L` is algebraically equivalent to `L^4` (Lang, *Abelian
Varieties*, Prop. 2, p. 92) then finishes the proof.

The Lean proof takes a different route and uses neither `[2]^* L ≅ L^4` up to algebraic
equivalence nor Corollary 6.2. Rigidity (`eq_one_of_forall_point`) reduces the identity
`Λ((1, λ)^* P) = λ * λ` to the unit section and to points `t` over one-point schemes. At such
a point, `comp_mumfordSchemeMap_poincareDiagonal` computes the class of the pulled-back
family by bilinearity of the Poincaré bundle: the two cross terms agree by the slice symmetry
of `λ` at `t`, and the remaining terms cancel. The slice symmetry comes from the
`IsPolarization` hypothesis: after a field extension, `λ` is a Mumford map `Λ(L₂)`, whose
slices are symmetric because the Mumford family is symmetric. Base change then carries the
symmetry back to `A`.
