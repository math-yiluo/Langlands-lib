# The complex conjugate of a complex vector space

Author: Worker 1808. Module `Langlands.Representation.Unitary.ConjugateSpace`.

This helper module supplies the complex conjugate of a complex vector space and
two uses of it: representations on the conjugate space, and conjugate-linear maps
of finite tensor products. The Library had no conjugate representation (see
`Aubert/General/NormalizedInductionHermitianDuality.md`, which works around it
with conjugate-linear maps). The module is used by
[SpehHermitian.md](../Classification/SpehHermitian.md).

Provenance: internal. These are elementary linear-algebra constructions with no
literature assertion; no theorem of the literature is assumed or stated.

## Declarations

All declarations are in namespace `Langlands`. Universes are arbitrary; no
topology, finiteness or norm is assumed.

### The conjugate space

| Declaration | Content |
| --- | --- |
| `ConjSpace V` | The type `V` itself (a `def`, so its instances are separate). |
| instance `AddCommGroup (ConjSpace V)` | The additive group of `V`. |
| instance `Module ℂ (ConjSpace V)` | `Module.compHom V (starRingEnd ℂ)`: `c • v` in `ConjSpace V` is `conj c • v` in `V`. |
| `ConjSpace.equiv V : V ≃ₗ⋆[ℂ] ConjSpace V` | The identity map, conjugate-linear. Its `map_smul'` field is `Complex.conj_conj`. |
| `ConjSpace.smul_def` | `c • v = equiv V (conj c • (equiv V).symm v)`, by definition. |
| `ConjSpace.ofConjLinear f` | A conjugate-linear `f : W →ₗ⋆[ℂ] V` as a linear map `W →ₗ[ℂ] ConjSpace V`, `w ↦ equiv V (f w)`. |
| `ConjSpace.toConjLinear f`, `toConjLinear_apply` | Conversely, a linear `f : W →ₗ[ℂ] ConjSpace V` gives the conjugate-linear `(equiv V).symm ∘ f`. |
| `ConjSpace.rep ρ`, `rep_apply` | For a monoid `G` and `ρ : Representation ℂ G V`, the representation of `G` on `ConjSpace V` with `rep ρ g v = equiv V (ρ g ((equiv V).symm v))`. Each operator is linear for the conjugated scalars because `ρ g` commutes with every scalar. |

### Irreducibility of conjugated pullbacks

`conjCompSubrepOrderIso ρ φ hφ`: for a surjective monoid homomorphism
`φ : H →* G`, an order isomorphism between the subrepresentations of
`(ConjSpace.rep ρ).comp φ` and those of `ρ`. A subrepresentation goes to its
preimage under `ConjSpace.equiv V` (a semilinear `Submodule.comap`), and back
under the inverse. Stability under `ρ g` follows from stability under
`ρ (φ h)` by surjectivity of `φ`. Both composites are the identity on carriers,
and the order is inclusion of carriers, so all three identities hold by
`Iff.rfl`. `isIrreducible_conjComp_iff` transports `IsSimpleOrder`
(Mathlib's `Representation.IsIrreducible`) along it.

### Conjugate-linear maps of finite tensor products

For a family of conjugate-linear maps `J i : V i →ₗ⋆[ℂ] W i` over an arbitrary
index type:

- `tensorConjMultilinear J`: the multilinear map
  `m ↦ equiv (⊗ᵢ J i (m i))` into `ConjSpace (⨂ᵢ W i)`. Additivity in one slot is
  that of `J i` and `tprod`; for scalars, `J i (c • x) = conj c • J i x`, multilinearity
  of `tprod` takes out `conj c`, and `equiv` turns it into `c`.
- `tensorConj J : (⨂ᵢ V i) →ₗ⋆[ℂ] (⨂ᵢ W i)`: `toConjLinear` of
  `PiTensorProduct.lift (tensorConjMultilinear J)`; `tensorConj_tprod` gives
  `tensorConj J (⊗ v) = ⊗ (J i (v i))`.
- `tensorConjEquiv J` for conjugate-linear equivalences, with inverse
  `tensorConj (J i).symm`; both composites are the identity by induction on
  tensors (`PiTensorProduct.induction_on`). `tensorConjEquiv_tprod` is its value
  on pure tensors.
- `tensorConjEquiv_external`: if `J i (ρ i (m i) v) = σ i (m i) (J i v)` for all `i`
  and `v`, then `tensorConjEquiv J` intertwines the external tensor actions
  `FiniteTensor.external ρ m` and `FiniteTensor.external σ m`. The proof is by
  induction on tensors, with `FiniteTensor.external_tprod`.
