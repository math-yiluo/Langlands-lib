# Group schemes with smooth connected fibres over a reduced base are smooth

Authors: Worker 50 and Worker 9.

The theorem `Langlands.GroupScheme.reducedBaseConnectedFibreSmooth.{u}` proves the
unchanged published proposition
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement.{u}` (SGA 3, Exposé VI_B,
Corollaire 4.4, for a reduced locally Noetherian base and connected fibres):

```lean
∀ (S : Scheme.{u}) (H : GroupScheme S), IsReduced S → IsLocallyNoetherian S →
  LocallyOfFiniteType H.X.hom →
  (∀ s : S, Smooth (H.X.hom.fiberToSpecResidueField s)) →
  (∀ s : S, ConnectedSpace (H.X.hom.fiber s)) →
  IsLocallyConstant (fun s : S => topologicalKrullDim (H.X.hom.fiber s)) →
    Smooth H.X.hom
```

The universe is arbitrary and no hypothesis is added. The module also proves the local
criterion `Langlands.GroupScheme.ReducedBaseSmooth.mem_smoothLocus_of_fibres`: let
`q : Y ⟶ S` be locally of finite type over a reduced locally Noetherian scheme, with a
section `e` (`e ≫ q = 𝟙 S`). If all residue fibres of `q` over an open `U` are smooth of
relative dimension `n`, then `e s` lies in `q.smoothLocus` for every `s ∈ U`.

## Implemented proof

The proof does not follow the route printed in SGA 3, which obtains flatness from
EGA IV₃ 15.6.7 and then applies Théorème 3.10 there. Instead it shows directly that the unit
section lies in the smooth locus and then translates. The helper modules are in
`Langlands/GroupScheme/ReducedBaseSmooth/`.

1. **Relative dimension near each base point** (`DimensionBridge`, Worker 50).
   `exists_open_smoothOfRelativeDimension_fiber` gives, for every `s : S`, an open
   `U ∋ s` and `n : ℕ` such that every residue fibre of `H.X.hom` over `U` is smooth of
   relative dimension `n`. It uses the Library theorem `smoothConnectedRelativeDimension`
   on each connected smooth fibre, the Library computation of the dimension of a scheme
   smooth of relative dimension `n` over a field, and the local constancy of the fibre
   dimension.
2. **The unit section lies in the smooth locus** (`mem_smoothLocus_of_fibres`, defined in
   this module). It is Worker 9's `mem_smoothLocus_of_fibres_of_finrank` (`Chart`) applied
   to Worker 50's `finrank_residueField_tensor_kaehler_eq` (`OmegaRank`). For `s ∈ U`,
   `Chart` chooses affine opens `Spec R ⊆ S` around `s` and `Spec A ⊆ Y` around `e s`
   with `A` of finite type over `R`. The fibre of `Spec A → Spec R` over the image `x` of
   `s` is smooth of relative dimension `n` (`FibreTransfer` and Mathlib's
   `Spec.fiberToSpecResidueFieldIso`). `OmegaRank` then gives
   `dim κ(y) ⊗[A] Ω[A⁄R] = n` at the point `y` of `e s`. Elements `a₁, …, aₙ` of `A` whose
   differentials span this space make `A` unramified at `y` over `R[X₁, …, Xₙ]`.
   Mathlib's `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` then exhibits a
   principal open `Spec A_f ∋ y` as a closed subscheme of a scheme étale over `𝔸ⁿ_R`, hence
   smooth of relative dimension `n` over `Spec R` (`Slice`). `Local` base-changes this chart
   to an open neighbourhood of `s` through which the section factors. It then applies
   `Core`: over a reduced base, a closed subscheme `Y'` with a section, inside a scheme
   `Z` smooth of relative dimension `n`, whose fibres are all smooth of relative dimension
   `n`, is smooth on an open neighbourhood of the section. In `Core`, the union of the
   fibrewise connected components of `Z` through the section is open (the Library's
   section-component openness, applied to the smooth and hence geometrically reduced `Z`).
   Fibrewise, this union lies inside `Y'`: if a closed subscheme of a scheme smooth of
   relative dimension `n` over a field is itself smooth of relative dimension `n`, it
   contains the connected component through any of its closed points, because the stalk
   map there is a surjection between domains of the same dimension `n`. Over this open set the closed immersion is surjective onto a reduced
   scheme (smooth over a reduced base), hence an isomorphism.
3. **Translation** (`Translation`, Worker 9). `smooth_of_range_unit_subset_smoothLocus`:
   if the unit section lies in the smooth locus `V` of `H.X.hom`, then the multiplication
   `V ×_S V → H` is smooth (a shear isomorphism followed by a projection) and surjective
   (on each fibre over a field, products of two points of an open set containing the
   identity cover the connected smooth group; this uses the Library's field product-cover
   results). Smoothness then descends along this smooth surjection onto the locally
   Noetherian `H`.

The final theorem introduces the hypotheses as instances and applies step 3. For a point
`η s` of the unit section, step 1 at `s` supplies `U` and `n`, and step 2 shows
`η s ∈ H.X.hom.smoothLocus`. The unit section is `η[H.X].left`, and `Over.w η[H.X]`
provides `η ≫ H.X.hom = 𝟙 S`.

## Module list

- `Langlands.GroupScheme.ReducedBaseSmooth.Translation` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.Core` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.FibreTransfer` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.Local` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.Slice` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.Chart` (Worker 9)
- `Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge` (Worker 50)
- `Langlands.GroupScheme.ReducedBaseSmooth.OmegaRank` (Worker 50)
- `Langlands.GroupScheme.ReducedBaseSmoothProof` (this module, Worker 50)
