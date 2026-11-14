# Normalizing an automorphism of `SO_{2l}` on the diagonal torus

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This is a support module for the proof of
`SpecialOrthogonalAutomorphismStatement`. It is step (C) of that proof: after composing with a
conjugation by an orthogonal matrix, any automorphism of `SO_{2l}` fixes the diagonal torus
pointwise. All declarations are in the namespace `Langlands.GroupScheme.OrthogonalMatrix`.

## Notation

`l` is a finite type with decidable equality and `k` a field. `groupScheme l R` is the split
orthogonal group `O_{2l}` over `Spec R`. `pointsEquiv l R T` identifies its `T`-points with
`orthogonalGroup l Γ(T.left, ⊤)`. `SO = identityComponent (groupScheme l (CommRingCat.of k))`
is its identity component, with inclusion `identityComponentι`. `𝔻` is the split torus
`splitTorus.commGroupScheme (Spec k) (ULift l)`, and `identityTorus l k : 𝔻 ⟶ SO` is the
diagonal torus. `w = weightCoord l` gives the weights `±e_a`, and `torusWeights τ x` is the
value of the weight `x` on a torus point `τ` (`τ a` for `x = inl a`, `(τ a)⁻¹` for
`x = inr a`).

The following come from `Automorphism.Conjugation` (Worker 74).

- `IsSimilitude g c` says that `g Q gᵀ - c Q` is alternating.
- `specialConjIso g c hg : SO ≅ SO` is conjugation `x ↦ g x g⁻¹` by an invertible similitude.
- `IsSimilitudeConj ρ` says that the automorphism `ρ` of `SO` is such a conjugation, on the
  matrices of points over every test scheme.

## Inner automorphisms by rational points

- `rationalPoint p`: for a point `p : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme l R).X` over the
  base, this is the matrix of `p` in `orthogonalGroup l R`. It is transported along
  `Γ(Spec R, ⊤) ≅ R` (`Scheme.ΓSpecIso`).
- `pointsEquiv_constantPoint_rational p T`: the constant family `constantPoint p T` has matrix
  `map l (scalarMap T) (rationalPoint p)`. The proof uses `pointsEquiv_naturality` and then
  compares entries, since `scalarMap T` is the composite of the inverse of `ΓSpecIso` with the
  structure map.
- `isSimilitudeConj_innerIso p`: for a rational point `p` of `SO`, the inner automorphism
  `SO.innerIso p` satisfies `IsSimilitudeConj`. The witness is `g = rationalPoint (p ≫ ι)` with
  multiplier `1`. `innerIso_hom_comp` (from `ConjugacyBaseChange`) moves the inner
  automorphism from `SO` to `O_{2l}`. On points, `comp_innerIso_hom` turns it into
  conjugation by the constant point, whose matrix is given by the previous lemma.

## Permutation matrices

Let `A` be a commutative ring and `σ` a permutation of `l ⊕ l`.

- `permGL A σ : GL (l ⊕ l) A` is the matrix `σ.toPEquiv.toMatrix`, with entry `1` at
  `(y, σ y)`. Its inverse is `σ.symm.toPEquiv.toMatrix` (`coe_permGL`, `coe_permGL_inv`).
- `map_toPEquiv_toMatrix f σ`: applying a ring homomorphism `f` to the entries fixes the
  permutation matrix.
- `permMatrix_conj σ D`: `P D P⁻¹ = D.submatrix σ σ`, where `P` is the permutation matrix.
- `formMatrix_apply_self y`: the diagonal entries of the split form matrix `Q` vanish.
- `isSimilitude_permGL σ hσ`: if `σ (swap x) = swap (σ x)` for all `x`, then the permutation
  matrix is a similitude with multiplier `1`, that is, an orthogonal matrix. By
  `permMatrix_conj`, the defect `P Q Pᵀ - Q` is `Q.submatrix σ σ - Q`. Its symmetrization
  involves the polar matrix `J` (entry `1` exactly at `(y, swap y)`), and
  `J (σ y) (σ z) = J y z` because `σ` commutes with `swap`. The diagonal of the defect vanishes
  by `formMatrix_apply_self`.

## The diagonal torus

- `isMaximalSplitTorus_identityTorus l k`: the diagonal torus is a maximal split torus of `SO`.
  It is a maximal torus (`isMaximalTorus_identityTorus`) that is split
  (`IsMaximalTorus.isMaximalSplitTorus`).
- `exists_innerIso_comp_identityTorus α` (**torus conjugacy**): for an automorphism `α` of `SO`
  there are a rational point `p` of `SO` and an automorphism `e` of `𝔻` with
  `identityTorus ≫ (α ≪≫ SO.innerIso p).hom = e.hom ≫ identityTorus`. Both `identityTorus ≫ α.hom`
  (`IsMaximalSplitTorus.comp_iso`) and `identityTorus` are maximal split tori. The Library
  theorem `smoothMaximalSplitTorusConjugacy` says that maximal split tori of the smooth
  connected affine group `SO` are conjugate under a rational point.
- `exists_perm_of_comp_identityTorus [Nontrivial l] β e h` (**Weyl step**): assume
  `h : identityTorus ≫ β.hom = e.hom ≫ identityTorus`. Then there is a permutation `σ` of
  `l ⊕ l` commuting with `swap` such that, for all `x`, transport of characters along `e`
  sends the character with coordinates `w x` to the character with coordinates `w (σ x)`.
  Transport of characters is `characterLattice.congr (CommGroupScheme.isoOfGroupIso e)`, and
  coordinates are `GeneralLinear.characterCoordEquiv l k`. The Library theorem
  `roots_image_of_transport` says that this transport maps the roots of `identityTorus` onto
  themselves, and the roots of `identityTorus` are those of the diagonal torus
  (`roots_identityTorus`). In coordinates, the roots are the `w x - w y` with
  `index x ≠ index y` (`mem_roots_iff`). The transport is an additive bijection of `ℤ^l`, so
  `exists_perm_map_weightCoord` (from `SignedPermutation`) gives `σ`.
- `torusWeights_swap τ x`: `torusWeights τ (swap x) = (torusWeights τ x)⁻¹`.
- `characterCoordEquiv_symm_weightCoord_inl j`: the character with coordinates `e_j` is the
  projection `splitTorus.proj _ _ ⟨j⟩`.
- `torusWeights_comp_inv e σ hσswap hσ t y`: under the conclusion of the Weyl step, for a torus
  point `t`, `torusWeights (t ≫ e⁻¹) y = torusWeights t (σ y)`. For `y = inl j` this is
  `splitTorus.pointsEquiv_comp` (the coordinate `j` of `t ≫ e⁻¹` is the value on `t` of the
  transported character `e_j`) together with `torusWeights_eq_prod`. For `y = inr j` it follows
  by inversion, since `σ` commutes with `swap`.
- `identityTorus_comp_specialConjIso_permGL e σ hσswap hσ` (**permutation step**): conjugation
  by `permGL k σ` restricts to `e⁻¹` on the diagonal torus:
  `identityTorus ≫ (specialConjIso (permGL k σ) 1 _).hom = e.inv ≫ identityTorus`. After
  composing with the inclusion into `O_{2l}`, it is enough to compare matrices of points. The
  diagonal matrix `diag(torusWeights t)` conjugated by the permutation matrix is
  `diag(torusWeights t ∘ σ)` (`permMatrix_conj`, `Matrix.submatrix_diagonal_equiv`). By the
  previous lemma this is `diag(torusWeights (t ≫ e⁻¹))`.

## Main results

- `exists_isSimilitudeConj_comp_fix_of_nontrivial [Nontrivial l] α`: for every automorphism `α`
  of `SO`, there is an automorphism `ρ` of `SO` with `IsSimilitudeConj ρ` and
  `identityTorus l k ≫ (α ≪≫ ρ).hom = identityTorus l k`. Take
  `ρ = SO.innerIso p ≪≫ specialConjIso (permGL k σ) 1 _` with `p`, `e` from torus conjugacy and
  `σ` from the Weyl step. `IsSimilitudeConj ρ` follows from `isSimilitudeConj_innerIso`,
  `isSimilitudeConj_specialConjIso` and `IsSimilitudeConj.trans`. On the torus the composite is
  `e.hom ≫ e.inv ≫ identityTorus = identityTorus`.
- `exists_isSimilitudeConj_comp_fix (hn : 2 ≤ n) α`: the same statement for `l = Fin n`, with
  `Nontrivial (Fin n)` from `Fin.nontrivial_iff_two_le`.

## Provenance

This is the standard first reduction in determining the automorphisms of a split reductive
group: move the image of a maximal split torus back by an inner automorphism (conjugacy of
maximal split tori), then correct the induced automorphism of the torus, which preserves the
roots, by an element normalizing the torus. Here the correction is the permutation matrix of a
signed permutation, so it is an orthogonal matrix that may lie outside `SO_{2l}`. The Lean
argument is internal and uses the Library theorems named above. Only the Lean statements are
claimed.
