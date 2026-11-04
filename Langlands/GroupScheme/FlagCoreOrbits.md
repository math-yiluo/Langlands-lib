# Closed orbits of a line, its dual line and their tensor for the flag covering core

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. The core's linear
algebra (`Langlands.GroupScheme.FlagCoreLinear`) uses three orbit maps of a
representation `ρ` on rational points: `orbitVec` (`g ↦ ρ(g) e`), `dualOrbitVec`
(`g ↦ w₀ ρ(g)⁻¹`) and `tensorOrbitVec` (their pure tensor). It takes closed orbits of
these maps as hypotheses, in the form `FlagCore.IsClosedOrbit`. This module derives
those three closed-orbit facts from the general closed-orbit lemma
`FlagCore.isClosedOrbit_of_isProper` of `Langlands.GroupScheme.FlagCoreQuotient`,
applied to `ρ`, to its dual `ρ.dual` and to the tensor `ρ.tensor ρ.dual`.

Everything is in the namespace `Langlands.GroupScheme.FlagCore`. Here `k` is a
field, `G` is a group scheme over `Spec k`, and `m` is a finite index type with
decidable equality. "Rational points" are morphisms
`Over.mk (𝟙 (Spec k)) ⟶ G.X`. For `v : m → k` and a test scheme `T`, `v_T` denotes
the vector `(scalarMap T (v i))_i` with entries in `Γ(T, ⊤)`.

## Definition

`StabilizesLine σ v b`, for a matrix representation `σ : MatrixRepresentation G m`,
a vector `v : m → k` and a subgroup `b : B ⟶ G`: the subgroup stabilizes the line
of `v`. On every test scheme `T`, every `T`-point `x` of `G` in
`SubgroupFunctor.range b` satisfies `σ(x) v_T = a • v_T` for some unit `a` of
`Γ(T, ⊤)`.

## Lemmas about lines

- `fibersStabilizeLine_of_fibersInCosets hq hs`: if the fibers of `q : G.X ⟶ Q` lie
  in cosets of `B` (`FibersInCosets q b`) and `B` stabilizes the line of `v`
  (`StabilizesLine σ v b`), then the fibers of `q` stabilize the line of `v`
  (`FibersStabilizeLine σ v q`). Proof: if `g ≫ q = h ≫ q`, then `g⁻¹ * h` lies in
  the range of `b`, and `hs` applies to it.
- `StabilizesLine.tensor hs hs'`: if `B` stabilizes the line of `v` in `σ` and the
  line of `w` in `σ'`, then it stabilizes the line of the pure tensor
  `(v i * w j)_(i, j)` in `σ.tensor σ'`. Proof: the point matrix of the tensor is
  the Kronecker product (`MatrixRepresentation.tensor_pointMatrix`), which maps a
  pure tensor to the pure tensor of the images
  (`GeneralLinear.kroneckerHom_mulVec`). The eigenvalue is the product `a * a'`
  of the two eigenvalues.

## Rational matrices of the dual and the tensor

- `rationalMatrix_coe σ g`: the matrix `σ.rationalMatrix g` is the point matrix of
  `g` with its entries mapped to `k` by `Γ(Spec k, ⊤) ≅ k`. This holds by
  definition.
- `rationalMatrix_dual ρ g`: `ρ.dual.rationalMatrix g` is the transpose of the matrix
  `ρ.rationalMatrix g⁻¹`. Proof: `MatrixRepresentation.dual_pointMatrix` and
  `GeneralLinear.matrixContragredient_coe` give the inverse transpose of the point
  matrix, and `map_inv` moves the inverse inside `rationalMatrix`.
- `rationalMatrix_tensor ρ σ g`: `(ρ.tensor σ).rationalMatrix g` is the Kronecker
  product of `ρ.rationalMatrix g` and `σ.rationalMatrix g`. Proof: entrywise, by
  `MatrixRepresentation.tensor_pointMatrix_entry` and multiplicativity of the
  entry map.
- `dualOrbitVec_rationalMatrix ρ w₀ g`: `dualOrbitVec ρ.rationalMatrix w₀ g`, that is
  `w₀ ρ(g⁻¹)`, equals `ρ.dual.rationalMatrix g *ᵥ w₀`. Proof: `rationalMatrix_dual`
  and `mulVec_transpose`.
- `tensorOrbitVec_rationalMatrix ρ e w₀ g`: `tensorOrbitVec ρ.rationalMatrix e w₀ g`
  equals `(ρ.tensor ρ.dual).rationalMatrix g *ᵥ (e i * w₀ l)_(i, l)`. Proof:
  `rationalMatrix_tensor`, `GeneralLinear.kroneckerHom_mulVec` and
  `dualOrbitVec_rationalMatrix`.

## Closed orbits

The three theorems below assume `k` algebraically closed, `G.X.hom` locally of finite
type, and `q : G.X ⟶ Q` over `Spec k` with `q.left` flat, surjective and
quasi-compact and `Q.hom` proper.

- `isClosedOrbit_orbitVec q ρ he hq`: for `e ≠ 0` with
  `FibersStabilizeLine ρ e q`, the orbit map `orbitVec ρ.rationalMatrix e` satisfies
  `IsClosedOrbit`. This is `isClosedOrbit_of_isProper` for `ρ`.
- `isClosedOrbit_dualOrbitVec q ρ hw₀ hq`: for `w₀ ≠ 0` with
  `FibersStabilizeLine ρ.dual w₀ q`, the dual orbit map
  `dualOrbitVec ρ.rationalMatrix w₀` satisfies `IsClosedOrbit`. This is
  `isClosedOrbit_of_isProper` for `ρ.dual`, rewritten by
  `dualOrbitVec_rationalMatrix`.
- `isClosedOrbit_tensorOrbitVec q ρ he hw₀ hq`: for `e ≠ 0`, `w₀ ≠ 0` with
  `FibersStabilizeLine (ρ.tensor ρ.dual) (e i * w₀ l)_(i, l) q`, the tensor orbit
  map `tensorOrbitVec ρ.rationalMatrix e w₀` satisfies `IsClosedOrbit`. The pure
  tensor of two nonzero vectors is nonzero (a nonzero entry `e i * w₀ l`), so this
  is `isClosedOrbit_of_isProper` for `ρ.tensor ρ.dual`, rewritten by
  `tensorOrbitVec_rationalMatrix`.

## Provenance

These are internal helper results for the proof of task 877d0194. They follow the
geometric part of the proof of Milne, *Algebraic Groups* (2017), Theorem 17.65
(printed pp. 374-375): orbits of lines stabilized by a Borel subgroup are closed
because `G/B` is complete. Milne uses this for a line in `V` and a line in the dual
`V^∨`. The route of `FlagCoreLinear` (see its Provenance section) also needs the
closed orbit of the tensor `e ⊗ w₀` in `V ⊗ V^∨`, which is not in Milne's proof;
this module records all three cases. The definition `StabilizesLine` is an internal name for the hypothesis that a
subgroup stabilizes a line on all test schemes; it does not come from the source.
