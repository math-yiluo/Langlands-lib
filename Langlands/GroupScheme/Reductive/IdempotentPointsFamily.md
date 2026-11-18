# Factor projections of points along a complete orthogonal family of idempotents

Namespace `Langlands.GroupScheme.IdempotentPoints`. This internal helper extends the Library module
`Langlands.GroupScheme.AffineIdempotentPoints` (factor projections `proj K e` of points of an affine
group scheme `K` over an `R`-algebra `C`, for an idempotent `e` of `C`). It is used in the split
case of the proof of `WeilAbelianImageTrivialityStatement`.

## Contents

`K` is a group scheme over `Spec R` with affine total space, and `C` is an `R`-algebra.

- `map_eq_one_of_family`: let `φ` be a group homomorphism from the points of `K` over `C` to any
  group, and `e₁, …, eₙ` idempotents of `C` that are pairwise orthogonal and sum to `1`. If `φ`
  kills `proj K eᵢ g` for every `i` and every point `g`, then `φ` is trivial. Proof: by induction on
  finite sets `S` of indices, `∑_{i ∈ S} eᵢ` is idempotent and `φ` kills the components at it. For
  `S ∪ {j}`, write the component at `e_j + ∑_S eᵢ` as the product of its components at `e_j` and
  `1 - e_j`. This uses the Library lemma `IdempotentPoints.proj_mul_proj_one_sub` (module
  `WeilFactorRigidityReduction`) and `proj_proj`. For `S` the whole index set, the component at
  `1` is the point itself (`proj_one`).

## Provenance

Internal: elementary facts about points over a product decomposition of the coefficient ring.
