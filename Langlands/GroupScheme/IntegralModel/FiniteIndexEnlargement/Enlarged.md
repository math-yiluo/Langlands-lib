# The enlarged Hopf algebra

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. Its definitions
(`incl`, `HasReps`, `enlarged`, `enlargedHopfAlgebra`) are auxiliary constructions, derived
for this proof.

## Flat kernels

`mem_range_lTensor_of_forall`: let `ι : N →ₗ[R] N'`, and let `f : I → (N' →ₗ[R] Q)` be a finite
family whose common kernel is exactly the range of `ι`. If `M` is flat and
`z : M ⊗[R] N'` satisfies `(id ⊗ f i) z = 0` for every `i`, then `z` lies in the range of
`id ⊗ ι`.

Proof: the sequence `N → N' → ∏ᵢ Q` is exact. Tensoring with the flat module `M` keeps it
exact, and `M ⊗ ∏ᵢ Q ≅ ∏ᵢ (M ⊗ Q)` is `TensorProduct.piRight`. `mem_range_rTensor_of_forall`
is the mirror version, obtained through the swap `comm_rTensor_apply`.

## Translation identities

Use the setting of module `Translation`: a Hopf algebra `A` over `R`, a field `K` over `R`, and
`ev : P →* WithConv (A →ₐ[R] K)`. Let `incl : A →ₗ[R] K ⊗[R] A` be `a ↦ 1 ⊗ a`.

- `leftComm_lTensor_rightTrans`: coassociativity written with right translations. Applying
  `id_A ⊗ rightTrans x` to `Δ a` and moving the `K` factor to the front gives
  `(id_K ⊗ Δ) (rightTrans x a)`.
- `assoc_rTensor_leftTrans`: likewise, `(leftTrans x ⊗ id_A) (Δ a)`, reassociated, is
  `(id_K ⊗ Δ) (leftTrans x a)`.
- `leftComm_symm_tmul_one` and `assoc_symm_tmul_one`: the inverse rearrangements send
  `1 ⊗ w` to `(id ⊗ incl) w` and `(incl ⊗ id) w`.
- `ev_inv_ofConv`: `ev x⁻¹ = ev x ∘ S`, where `S` is the antipode. The proof repeats Mathlib's
  argument that convolution inverses are given by the antipode: both sides are convolution
  inverses of `ev x`. Hence `ev_inv_apply : ev x⁻¹ a = ev x (S a)`.

## The enlarged subalgebra

`HasReps U V` says that `V` is a finite union of cosets `r * U` with `r` in some finite set
`T ⊆ V`.

`enlarged ev V : Subalgebra R A` is the subalgebra of `a : A` with `ev x a ∈ R` for every
`x ∈ V` (`mem_enlarged`). It contains the scalars and is closed under sums and products because
each `ev x` is a ring map. `antipode_mem_enlarged`: the antipode preserves it, since
`ev x (S a) = ev x⁻¹ a` and `V` is closed under inverses.

Now add the standing hypotheses of the separating module:

- `R` is a Henselian discrete valuation ring with algebraically closed residue field and fraction
  field `K`;
- `A` is smooth;
- `U` satisfies `hU` and `hsurj`;
- `U ≤ V`, with the conjugation hypothesis `hnorm`;
- `T ⊆ V` is finite with `V = ⋃_{r ∈ T} r U`.

Then:

- `mem_enlarged_iff_rightTrans`: `a ∈ enlarged ev V` iff, for each `r ∈ T`, the right translate
  `rightTrans r a` has the form `1 ⊗ b` with `b : A`. One direction is the translation lemma.
  For the other, write `x = r u = (r u r⁻¹) r` with `r u r⁻¹ ∈ U`. Then
  `ev x a = ev (r u r⁻¹) b ∈ R`.
- `mem_enlarged_iff_leftTrans`: the same with left translates; here `x = r u` directly.
- `forall_mkQ_rightTrans_iff` and `forall_mkQ_leftTrans_iff` restate these: the enlarged
  algebra is the common kernel of the finitely many linear maps `A → (K ⊗ A) / range incl`
  induced by the translates.
- `comul_mem_range_lTensor`: for `b ∈ enlarged ev V`, `Δ b` lies in the image of `A ⊗ B`, where
  `B = enlarged ev V`. Apply the flat-kernel lemma with `M = A`; `A` is flat, being smooth. The
  needed vanishing is `leftComm_lTensor_rightTrans` combined with `rightTrans r b = 1 ⊗ c`.
- `comul_mem_range_ι₂` (**the comultiplication preserves the enlarged algebra**): for
  `b ∈ B`, `Δ b` lies in the image of `B ⊗ B` (the map `SubHopf.ι₂`). Proof:
  1. Write `Δ b = (id ⊗ val) c'` with `c' ∈ A ⊗ B`.
  2. Apply the mirror flat-kernel lemma with the flat module `B` to show that `c'` comes from
     `B ⊗ B`.
  3. For the vanishing at each `r ∈ T`, write `leftTrans r b = 1 ⊗ c`. Then `c ∈ B`, and by the
     previous step `Δ c` comes from `A ⊗ B`.
  4. `assoc_rTensor_leftTrans` identifies `(leftTrans r ⊗ id) c'` with an element in the image
     of `incl ⊗ id`. This is checked after the injective map `id ⊗ val`, which is injective
     because `K ⊗ A` is flat over `R`.
- `flat_enlarged`: `B` is flat over `R`. It is torsion-free as a submodule of the flat module
  `A`, and torsion-free modules over a Dedekind domain are flat.
- `comul_mem_range_ι₂_of_hasReps`: the same as `comul_mem_range_ι₂`, from `HasReps U V`.
- `enlargedHopfAlgebra`: the Hopf algebra structure on `enlarged ev V`, given by
  `SubHopf.hopfAlgebra` from the two preservation results.

## Provenance

The enlarged algebra is the coordinate ring of the enlargement in Kaletha–Prasad Proposition
A.7.1. The flatness argument showing that it is a Hopf subalgebra is derived for this
formalization. It uses only coassociativity and translations, never the separation of
functions by points, which fails for `K ⊗[R] A`.
