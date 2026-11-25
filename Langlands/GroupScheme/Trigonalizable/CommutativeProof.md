# Proof: commutative groups over algebraically closed fields are trigonalizable

This module proves the Library statement
`Langlands.GroupScheme.AlgClosedCommutativeTrigonalizableStatement` (Milne, *Algebraic
Groups* (2017), Corollary 16.14, printed p.329) at every universe `u`. The theorem is

```text
theorem Langlands.GroupScheme.algClosedCommutativeTrigonalizable :
    AlgClosedCommutativeTrigonalizableStatement.{u}
```

It adds no hypotheses to the statement. The hypotheses are used as follows.

- `[IsAlgClosed k]` gives eigenvalues of endomorphisms of nonzero finite-dimensional spaces.
- `[IsCommMonObj G.X]` makes two particular points of `G` commute.
- `[IsAffineHom G.X.hom]` provides the coordinate algebra `O(G)` and the affine model
  `Spec O(G) ≅ G.X`.
- `[LocallyOfFiniteType G.X.hom]` is not used.

The proof does not follow Milne's route through Theorems 16.13 and 16.6 (the decomposition
`G = G_u × G_s`). It is a direct linear-algebra argument on the universal matrix of the
representation. This argument never uses `k`-points of `G`, so it also covers non-reduced `G`.

Helper declarations are in the namespace
`Langlands.GroupScheme.AlgClosedCommutativeTrigonalizable`. The module sets
`backward.isDefEq.respectTransparency false`, as the Library module
`Langlands.GroupScheme.MatrixRepresentation.NonAffineNormalFixedCoordinates` also does.
Without it, `Algebra.TensorProduct.includeLeft` fails to elaborate as a morphism of
`CommAlgCat (CommRingCat.of k)`.

## Notation

`k` is a field, `G` is a group scheme over `Spec (CommRingCat.of k)` with
`[IsAffineHom G.X.hom]`, and `ρ : MatrixRepresentation G n`. These Library declarations are
used.

- `B = CharacterUnits.Coord G` is the coordinate algebra `O(G)`.
- `U = CharacterUnits.universalPoint G` is the universal point, a point of `G` with values in
  `B`. `CharacterUnits.universalPoint_eq` identifies it with the affine model isomorphism
  `(Lie.coordinateIso G).hom : Spec B ⟶ G.X`.
- `M = ρ.universalCharacterMatrix` is, by definition, the matrix `ρ.affineMatrix B U` over `B`.
- For a functional `ℓ : B →ₗ[k] k`, `AffineCoefficients.coefficientMap ρ ℓ = M.map ℓ` is a
  matrix over `k`.

## Step 1: common eigenvectors (linear algebra)

`exists_common_eigenvector_of_le`: let `S` be a set of pairwise commuting endomorphisms of
a finite-dimensional space `V` over an algebraically closed field. Then every nonzero subspace
`W` preserved by every element of `S` contains a nonzero `w` that is an eigenvector of every
element of `S`. The proof is strong induction on `d = finrank W`.

- If every `f ∈ S` acts on `W` as a scalar, any nonzero `w ∈ W` works.
- Otherwise, pick `f ∈ S` that is not a scalar on `W`. Its restriction to `W` has an
  eigenvalue `t` (`Module.End.exists_eigenvalue`, which needs `IsAlgClosed`). Let
  `W' = W ⊓ ker (f - t)`. It is nonzero because it contains an eigenvector. It is strictly
  smaller than `W` because `f` is not the scalar `t` on `W`. Each `g ∈ S` preserves `W'`
  because `g` commutes with `f`. The induction hypothesis applied to `W'` (via
  `Submodule.finrank_lt_finrank_of_lt`) gives the vector.

`exists_common_eigenvector` is the case `W = ⊤`, for nonzero `V`.

## Step 2: the transfer from the affine model to all tests

`isStableLine_of_affine_model` works over any base ring `R`. Suppose
`j : Spec A ≅ G.X` is an affine model, `v : n → R`, and `c : A` satisfy

`ρ.affineMatrix A j.hom *ᵥ v_A = c • v_A`, where `v_A = (algebraMap R A (v i))_i`.

Then `ρ.IsStableLine v`. The argument is the stable-line analogue of the Library's
`MatrixRepresentation.isFixedVector_iff_affine_model`.

1. On the test `Spec A`, the equation transfers to the point matrix with multiplier
   `c' = e.symm c`. Here `e = Corepresented.affineSectionsAlgEquiv A`, and the proof uses
   `pointMatrix_eq_affineMatrix`, `UnipotentMatrixCriterion.scalarMap_affine` and
   `RingHom.map_mulVec`.
2. For an arbitrary test `T` and point `x : T ⟶ G.X`, write `x = (x ≫ j.inv) ≫ j.hom`.
   Then `pointMatrix_naturality` expresses `ρ(x)` as the image of `ρ(j.hom)` under the
   ring map `(x ≫ j.inv).left.appTop`.
3. Applying that ring map to the equation of step 1, with `RingHom.map_mulVec` and
   `scalarMap_naturality`, gives the stable-line equation on `T` with multiplier
   `(x ≫ j.inv).left.appTop c'`.

## Step 3: the coefficient matrices commute

`coefficientMap_mul_comm`, with `[IsCommMonObj G.X]`: for all `ℓ, m : B →ₗ[k] k`,

`coefficientMap ρ ℓ * coefficientMap ρ m = coefficientMap ρ m * coefficientMap ρ ℓ`.

Let `D = B ⊗[k] B`, with the inclusions `a = includeLeft` and `b = includeRight`. Pull `U`
back along them to get two points `x, y` of `G` with values in `D`. Under the scoped
`CategoryTheory.MonObj` instance `Hom.commMonoid`, points of a commutative monoid object form
a commutative monoid, so `x * y = y * x`. `ρ.affineMatrix D` is a monoid homomorphism and
`affineMatrix_naturality` holds, so the matrix identity is

`M.map a * M.map b = M.map b * M.map a`   (over `D`).

Apply the linear functional `Λ = mul' ∘ (ℓ ⊗ m) : D → k` to the `(i, j)` entry. Then
`Λ(a p * b q) = Λ(p ⊗ q) = ℓ p · m q` and `Λ(b p * a q) = Λ(q ⊗ p) = m p · ℓ q`. The
identity becomes

`∑ₗ ℓ(M i l) m(M l j) = ∑ₗ m(M i l) ℓ(M l j)`,

which is the `(i, j)` entry of the claim.

## Step 4: from a common eigenvector to the universal point

`exists_universal_smul`: suppose `v ≠ 0` and, for every `ℓ`, `coefficientMap ρ ℓ *ᵥ v = t_ℓ • v`
for some `t_ℓ : k`. Then `M *ᵥ v_B = c • v_B` for some `c : B`.

Choose `i₀` with `v i₀ ≠ 0`, set `w = M *ᵥ v_B` and `c = (v i₀)⁻¹ • w i₀`. Each coordinate
`w i - c · v_B i` lies in the `k`-vector space `B`. It is shown to be zero by
`Module.forall_dual_apply_eq_zero_iff`: for every functional `ℓ`, the Library lemma
`AffineCoefficients.coefficientMap_mulVec` gives `ℓ (w r) = t_ℓ · v r`. So the functional
takes the value `t_ℓ v i - (v i / v i₀) t_ℓ v i₀ = 0`.

## Main theorem

Introduce `k`, `G`, the instances, `n` and `ρ`. Let `S` be the set of the linear maps
`(coefficientMap ρ ℓ).mulVecLin` on `n → k`. They commute pairwise by step 3, using
`Matrix.mulVecLin_mul`. Since `n` is nonempty, `n → k` is nonzero, so step 1 gives a
common eigenvector `v ≠ 0`. Step 4 gives `c` with `M *ᵥ v_B = c • v_B`. Since
`M = ρ.affineMatrix B U` and `U = (Lie.coordinateIso G).hom`, step 2 with
`j = Lie.coordinateIso G` gives `ρ.IsStableLine v`.

## Axioms

An axiom check of the theorem reports only `propext`, `Classical.choice` and `Quot.sound`.
