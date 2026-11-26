# Finite-index induction of a character: coset matrices and continuity

Module `Langlands.Galois.HeckeInduction.InducedCharacter`, name space
`Langlands.FiniteRepresentation.InducedCharacter`. Throughout, `L` is a field, `G` a group,
`S : Subgroup G` of finite index and `χ : S →* Lˣ` a character. The right cosets
`Cosets S` and the functions `coset`, `factor` and `coordinates` are those of
`Langlands.Weil.Representation.Induction`: `factor S g = g * (coset S g).out⁻¹ ∈ S`.

## Objects

- `characterRep S χ` is `twist χ (of 1)`, the rank-one representation of `S` on `L` given by
  `χ` (`characterRep_apply`: `s` acts by multiplication by `χ s`).
- `induced S χ` is `induce S (characterRep S χ)`, the published finite-index induction on the
  space of functions `f : G → L` with `f (s * x) = χ s * f x`, on which `G` acts by right
  translation. Both are abbreviations, so `induced S χ` is literally the representation
  `FiniteRepresentation.induce S (FiniteRepresentation.twist χ (FiniteRepresentation.of 1))`.
- `ev χ f x` is the value at `x` of the function `f` (`ev_mul`, `ev_add`, `ev_injective`,
  `ev_representation`: `ev χ (g • f) x = ev χ f (x * g)`).
- `cosetCoords χ : induced S χ ≃ₗ[L] (Cosets S → L)` is the published `coordinates`, the values on
  the chosen representatives; `cosetBasis χ` is the corresponding basis, `cosetBasis χ q` being
  the function supported on the coset `q` with value `1` at `q.out`.
- `cosetMul g q = coset S (q.out * g)` is right multiplication of right cosets;
  `cosetMul_iterate`: `(cosetMul g)^[k] (coset S x) = coset S (x * g ^ k)`.

## Results

- `coset_out_mul`, `coset_eq_iff` (`coset S x = coset S y ↔ y * x⁻¹ ∈ S`), `mem_of_coset_eq`,
  `coe_factor_out_mul`: elementary coset identities.
- `toMatrix_cosetBasis`: the matrix of `g` in `cosetBasis χ` has entry
  `χ (factor S (q.out * g))` in position `(q, cosetMul g q)` and zero elsewhere. The proof
  evaluates `g • cosetBasis χ q'` at `q.out`: it is the value of `cosetBasis χ q'` at
  `q.out * g`, namely `χ (factor S (q.out * g))` times the indicator of `coset S (q.out * g) = q'`.
- `prod_range_factor`, `prod_fin_factor_cycle`: along `m` steps of `cosetMul g` the factors
  `factor S (((cosetMul g)^[k] q).out * g) = x_k * g * x_(k+1)⁻¹` telescope. If
  `x * g ^ m * x⁻¹ ∈ S`, the product of the `χ`-values over the cycle through `coset S x` is
  `χ (x * g ^ m * x⁻¹)`; changing the representative `x` conjugates the return element inside `S`,
  which does not change the value of the character.
- `det_one_sub_X_smul_induced`: if `x : W → G` and `len : W → ℕ` satisfy `0 < len w`,
  `x w * g ^ len w * (x w)⁻¹ ∈ S`, and `⟨w, k⟩ ↦ coset S (x w * g ^ k)` is a bijection from
  `Σ w, Fin (len w)` onto the right cosets, then
  `det (1 - X • (toMatrix (cosetBasis χ) (cosetBasis χ) (g action)).map C) =
  ∏ w, (1 - C (χ (x w * g ^ len w * (x w)⁻¹)) * X ^ len w)`. It combines
  `toMatrix_cosetBasis`, `cosetMul_iterate`, `prod_fin_factor_cycle` and
  `Langlands.MonomialDeterminant.det_one_sub_X_smul_monomial`.
- `induced_eq_one`: if every conjugate `y * g * y⁻¹` lies in `S` and is killed by `χ`, then `g`
  acts trivially, since `ev χ f (y * g) = χ (y * g * y⁻¹) * ev χ f y`.
- `rank_characterRep`, `rank_induced`: the induced space has dimension the index of `S`
  (from the published `rank_induce`).
- `induced_cosetBasis_of_conj_mem`: an element `u` with `q.out * u * q.out⁻¹ ∈ S` for every coset
  acts on `cosetBasis χ q` by the scalar `χ (q.out * u * q.out⁻¹)`.
- `continuous_induced`: if `G` is a topological group, `S` is open, `L` is a topological ring
  and `s ↦ (χ s : L)` is continuous, then `g ↦ (induced S χ).representation g` is continuous for
  the module topology on `Module.End L (induced S χ)`, the topology of the Library's
  `IsContinuous`. On the open neighbourhood `U = {u | ∀ q, q.out * u * q.out⁻¹ ∈ S}` of `1` the
  action is `∑ q, χ (q.out * u * q.out⁻¹) • P q` with fixed rank-one endomorphisms `P q`; this is
  continuous, and a homomorphism into a topological monoid that is continuous at `1` is
  continuous (`continuous_of_continuousAt_one`).

## Provenance

This is a derived, internal module on the Library's representation
`FiniteRepresentation.induce`. The coset-coordinate description of an induced character is
the classical monomial description of induced representations; the implemented proofs are those
described above.
