# Finite averaging for twisted-fixed reduced translations

Authors: Worker 88, with Worker 2094 (route and interface).

Lean module: `Langlands.Geometry.Building.TwistedFixedTranslationAveraging`.

This module provides the averaging half of the proof of
`UnramifiedTwistedFixedTranslationStatement` (Kaletha–Prasad, Proposition 9.3.13, first
paragraph of the proof: `V(T′)^Γ = V(S′)`). It reduces the real statement about reduced
translations to an integral statement about cocharacters. The integral statement is the
hypothesis `hfix` below, and it is proved in a separate module.

Setting. `K/k` is a field extension, `T` a commutative `k`-group scheme, `iT : T → G` a
homomorphism into a `k`-group scheme, and `T_K`, `i_K` their base changes to `K`. The
underlying morphism of schemes of `i_K` is a monomorphism. For each `σ ∈ Aut(K/k)` a point
`n σ` of the normalizer of `T_K` in `G(K)` is given.

KP state the fixed-space identity and do not write out the passage from fixed cocharacters to
fixed real vectors. The finite-image averaging of this module is the implemented justification
of that passage. KP do not average explicitly. Here `K` may be infinite over `k` (in the
application `K` is the maximal unramified extension of a local field). The proof shows that
the twisted maps take only finitely many values, and it averages over that finite image. That
image is contained in the product set of the finite Weyl image of a split torus and the finite
image of the Galois action on cocharacters of a torus that splits over `K`. It need not equal
the whole product set.

## Abstract averaging (namespace `Langlands.LinearAlgebra.FiniteAveraging`)

- `mem_range_baseChange_sup_of_sub_mem`: let `W : Γ →* (X ≃ₗ[ℤ] X)` be a group homomorphism
  with finite range, `φ : A →ₗ[ℤ] X` a `ℤ`-linear map such that every `X`-element fixed by all
  `W σ` lies in the range of `φ`, and `R` a real subspace of `ℝ ⊗[ℤ] X`. If
  `W σ v - v ∈ R` for every `σ` (with `W σ` extended to `ℝ`), then `v` lies in
  `range (φ ⊗ ℝ) ⊔ R`.

  Proof. Let `P = ∑_{g ∈ range W} g` on `X` and `Q` its real extension. `P x` is fixed by
  every `W σ`, since left multiplication by `W σ` permutes `range W`. So `P x` lies in the
  range of `φ`, and `Q` maps `ℝ ⊗ X` into `range (φ ⊗ ℝ)` (induction on tensors). Moreover
  `Q v - |range W| • v = ∑_g (g v - v)` lies in `R`. Dividing by `|range W|` writes `v` as an
  element of `range (φ ⊗ ℝ)` plus an element of `R`.
- `mkQ_mem_map_range_baseChange`: the same conclusion in the quotient by `R`:
  `R.mkQ v ∈ (range (φ ⊗ ℝ)).map R.mkQ`.

## Twisted coefficient maps (namespace `Langlands.Geometry.Building.TwistedFixedTranslationAveraging`)

- `twistedLatticeAut iT n σ`: the `ℤ`-linear automorphism `λ ↦ n_σ · σ(λ)` of the cocharacter
  lattice of `T_K`. It is the product of the published `cocharacterAut` of
  `normalizingAut i_K (n σ)` and the published Galois transport
  `cocharacterLattice.galoisEquiv k K T σ`.
- `twistedLatticeAut_apply`: `twistedLatticeAut iT n σ λ =
  galoisRepresentation σ λ ≫ (normalizingAut i_K (n σ)).hom` (by definition).
- `normalizerAction_galoisCocharacterAction_eq`: the real twisted map
  `normalizerAction i_K (n σ) ∘ galoisCocharacterAction σ` on `V(T_K)` is the real scalar
  extension of `twistedLatticeAut iT n σ`. The proof checks this on pure tensors with the
  published `galoisCocharacterAction_tmul` and `normalizerAction_tmul`.
- `galoisRepresentation_comp_normalizingAut`: Galois transport of a cocharacter intertwines the
  automorphism through which a normalizer point `m` acts with that of its Galois conjugate
  `normalizerGaloisAction k K iT σ m`. The proof combines the uniqueness of the normalizing
  automorphism (`IsNormalizingPoint.unique`), the published
  `IsNormalizingPoint.rationalConjugate`, and `cocharacterLattice.transport_descentPostcomp`.
- `cocycle_of_eq_inv_mul_conjugate`: if `n σ = h⁻¹ σ(h)` in `G(K)` for some `h ∈ G(K)` and all
  `σ`, then `n (στ) = n σ · σ(n τ)`. The proof uses `rationalConjugate_mul` and the
  multiplicativity of `rationalConjugate k K G σ`.
- `twistedLatticeAut_mul`: for such a cocycle `n`, `twistedLatticeAut iT n (στ) =
  twistedLatticeAut iT n σ * twistedLatticeAut iT n τ`. The proof uses the previous two
  lemmas and the uniqueness of the normalizing automorphism of a product.
- `mem_splitTranslationDirections_of_twistedFixed`: assume the twisted lattice maps are
  multiplicative, have finite range, and every cocharacter `λ` of `T_K` fixed by all of them
  equals `ν ≫ f_K` for a cocharacter `ν` of `S_K`. Then every reduced translation `v` with
  `translationAction i_K (n σ) (galoisTranslationAction k K iT σ v) = v` for all `σ` lies in
  `splitTranslationDirections k K iT f`. Proof: lift `v` to `w : V(T_K)`. By the bridge lemma
  the hypothesis on `v` says that `W σ w - w` lies in the root annihilator, where `W` is the
  homomorphism built from the twisted lattice maps. Then apply `mkQ_mem_map_range_baseChange`
  with `φ = cocharacterMapInt f_K`. Its real extension is the published `cocharacterMapReal`
  (by definition), so the conclusion is the definition of `splitTranslationDirections`.

## Finiteness of the twisted maps

- `finite_range_cocharacterAut_normalizingAut`: for a split torus `T'` in `G'` (monomorphic
  `j : T' → G'`) whose Weyl image `weylImage j` is finite, the maps
  `m ↦ cocharacterAut (normalizingAut j m)` take finitely many values. Proof: `characterAut`
  is injective on automorphisms of a split torus, because characters separate morphisms into
  it (published `IsSplitTorus.hom_ext_characters`). The image of `normalizingAut j` under
  `characterAut` is the range of `weylAction j`, which is finite. So the range of
  `normalizingAut j` is finite, and so is its image under `cocharacterAut`.
- `finite_range_galoisEquiv`: let `K/k` be Galois (possibly infinite) and `T_K` split. Then
  `σ ↦ cocharacterLattice.galoisEquiv k K T σ` takes finitely many values. Proof: the published
  `torusLatticeGaloisContinuity` gives a finite-dimensional intermediate field `L` whose fixing
  subgroup `H` acts trivially on cocharacters. By Mathlib's
  `IntermediateField.finrank_eq_fixingSubgroup_index`, `H` has finite index. The map is
  constant on left cosets `σH`, so its range is the image of the finite type `Aut(K/k) ⧸ H`
  under `q ↦ galoisEquiv q.out` (Mathlib's `QuotientGroup.mk_out_eq_mul`).
- `finite_range_twistedLatticeAut`: for `K/k` Galois, `T_K` split and `weylImage i_K` finite,
  the range of `twistedLatticeAut iT n` lies in the product set of the two finite ranges
  above, so it is finite.

## Final form

- `mem_splitTranslationDirections_of_inv_mul_conjugate`: let `K/k` be Galois, `G` affine and
  locally of finite type over `k`, `i_K` a maximal split torus of `G_K` (`hiT`), `h ∈ G(K)`
  and `n σ = h⁻¹ σ(h)` normalizer points of `T_K`. Assume `hfix`: every cocharacter `λ` of
  `T_K` with `galoisRepresentation σ λ ≫ (normalizingAut i_K (n σ)).hom = λ` for all `σ` equals
  `ν ≫ f_K` for a cocharacter `ν` of `S_K`. Then every reduced translation fixed by all twisted
  coefficient maps `v ↦ n_σ · σ(v)` lies in `splitTranslationDirections k K iT f`.

  Proof. Base change to `K` keeps `G` affine and locally of finite type (the structure
  morphism of `G_K` is a pullback of that of `G`). `hiT` gives that `T_K` is split and closed
  in `G_K`. So the published `splitTorusWeylImageFinite` makes `weylImage i_K` finite. The
  multiplicativity comes from `cocycle_of_eq_inv_mul_conjugate` and `twistedLatticeAut_mul`,
  and the finite range from `finite_range_twistedLatticeAut`. Then
  `mem_splitTranslationDirections_of_twistedFixed` applies.

  The hypotheses `h` centralizing the points of `S` and `G` connected reductive in the target
  statement are not used here. They enter only through `hfix`, which is proved elsewhere.
