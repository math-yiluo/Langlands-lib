# Collapse of a filtration under normalized Jacquet functors

Draft by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This is a generic lemma
used in the computation of the Jacquet module of the Gelfand–Graev representation
(`GelfandGraevJacquetStatement`). The Mackey filtration of the restricted Gelfand–Graev
representation has one graded piece per `N`–`P` double coset. After the vanishing lemma
(`GelfandGraevJacquetVanishing`) only the open piece survives. This module turns that into an
equivalence of normalized Jacquet actions.

## Setting

`P` is a topological group and `U` a subgroup of `P`. All coinvariants are the actual
`U`-coinvariants `Jacquet.Coinvariants ρ U` of `Jacquet/Coinvariants`. For an intertwiner
`f : ρ → σ` of `P`-representations, `coinvariantsMap U f` is the induced linear map on
`U`-coinvariants.

`A` is a representation of `P` and `s : ObjectRepFiltration A m` a filtration
`0 = A_0 ⊆ A_1 ⊆ … ⊆ A_m = A` by invariant subspaces. `gr_i = A_{i+1} / A_i` is the `i`th graded
quotient (`s.gradedRepresentation i`), with projection `s.gradedProjection i : A_{i+1} → gr_i`.

## Results

- `representationEquivComp`: restricting an equivalence of representations along a group
  homomorphism `H → P` gives an equivalence of the restricted representations.
- `normalizedEquivOfModulus`: an equivalence `ρ ≃ σ` of `P`-representations induces an equivalence
  of the normalized Jacquet actions `Jacquet.normalizedActionOfModulus ρ N M hMN δ` and
  `Jacquet.normalizedActionOfModulus σ N M hMN δ`, for every subgroup `N`, every subgroup `M` of
  its normalizer and every modulus `δ : M → ℝ≥0ˣ`.
- `subsingleton_coinvariants_of_equiv`: if `ρ ≃ σ` and the `N`-coinvariants of `σ` are zero, so
  are those of `ρ`.
- `stepInclusion s h` (for `k ≤ l`) is the inclusion `A_k → A_l`, and `stepSubtype s k` is the
  inclusion `A_k → A`, both as intertwiners.
- `range_stepInclusion_eq_ker`: the image of `A_i → A_{i+1}` is the kernel of
  `A_{i+1} → gr_i`.
- `coinvariantsMap_range_eq_ker`: the same holds after taking `U`-coinvariants. This is the
  right exactness of coinvariants, `coinvariants_map_range_eq_ker`.
- `coinvariants_filtration_bijective`: assume that every finite subset of `U` lies in a compact
  open subgroup of `U`, that `A` is smooth for `U`, and that `(gr_i)_U = 0` for every `i ≠ j`.
  Then the maps `(A_{j+1})_U → A_U` and `(A_{j+1})_U → (gr_j)_U` induced by `stepSubtype s j.succ`
  and `s.gradedProjection j` are bijective.
- `coinvariantsFiltrationEquiv`: under the same hypotheses, for every subgroup `M` of the
  normalizer of `U` and every modulus `δ`, the normalized Jacquet actions of `M` on `A_U` and on
  `(gr_j)_U` are equivalent. The equivalence is the inverse of the first bijection followed by
  the second. Both maps are `Jacquet.normalizedMapOfModulus` of intertwiners, so they commute
  with the normalized `M`-actions.

## Proof of `coinvariants_filtration_bijective`

- *Early steps vanish.* By induction on `k ≤ j` (`Fin.induction`), `(A_k)_U = 0`. For `k = 0`
  the step is zero. For `k = i + 1` with `i < j`, `(gr_i)_U = 0`, so every element of
  `(A_{i+1})_U` lies in the kernel of the map to `(gr_i)_U`. By right exactness it comes from
  `(A_i)_U`, which is zero by induction.
- *Late steps surject.* By downward induction on `k ≥ j + 1` (`Fin.reverseInduction`), the map
  `(A_k)_U → A_U` is surjective. For `k = m` this follows from surjectivity of coinvariants
  (`coinvariants_map_surjective`), since `A_m = A`. For `k = i` with `j < i < m`,
  `(gr_i)_U = 0`, so `(A_i)_U → (A_{i+1})_U` is surjective by right exactness. Compose with the
  surjection `(A_{i+1})_U → A_U` given by induction.
- *First map.* It is surjective by the case `k = j + 1`. It is injective because the inclusion
  `A_{j+1} → A` is injective and `A` is smooth for `U`. This uses the left exactness of
  coinvariants of smooth representations, `coinvariants_map_injective_of_smooth`, which needs
  the compact open subgroups of `U`.
- *Second map.* It is surjective because `A_{j+1} → gr_j` is surjective. Its kernel is the image
  of `(A_j)_U`, which is zero by the first item.

## Provenance

This is the standard argument that an exact functor which kills all but one graded piece of a
finite filtration sends the filtration to that piece. It is used in the Bernstein–Zelevinsky
geometric lemma (Bernstein–Zelevinsky 1977, §5). The Library result
`Langlands.Jacquet.Localization.FiltrationCollapseStatement` concerns character localization and
only provides an abstract linear equivalence. This module
reproves the collapse with explicit maps so that the equivalence is `M`-equivariant. The
formulation is internal.
