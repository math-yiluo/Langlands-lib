# Divisibility of actual division-algebra splitting degrees

This internal derived module proves two theorems. Throughout, `D` is
a division ring that is a finite-dimensional `k`-algebra, and `L` is a field
that is a finite-dimensional extension of `k`.

`Langlands.CentralSimple.division_splitting_size_dvd_field_degree` starts with
an actual matrix splitting `e : L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L` with
`0 < n`. Restricting along the second-factor inclusion `D → L ⊗[k] D` makes
the standard column module `Fin n → L` an actual left `D`-vector space. The
tower law shows that `dim_k D` divides the `k`-dimension of this module. The
splitting chart identifies `dim_k D = n²`, whereas the column module has
`k`-dimension `n [L:k]`. Cancelling the positive factor `n` gives
`n ∣ [L:k]`.

`Langlands.CentralSimple.division_degree_six_not_split_over_odd_extension`
specializes this calculation to division-algebra dimension 36. An actual
splitting then has size 6, so no finite extension of odd degree admits an
actual matrix splitting `L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L` with
`0 < n`.

Beyond the stated finiteness, division-ring and field assumptions and the
supplied algebra chart, no Galois, separability, centrality, characteristic
or Brauer-group hypothesis is used. The proof uses the implemented matrix
column module and the ordinary tower law for vector-space dimensions. The
first theorem is a variant of the divisibility used in the proof of Gille and
Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Proposition
4.5.8, printed page 103: there, the index of a central simple algebra divides
the degree of every finite separable splitting extension. Here the algebra is a
division algebra, the splitting size `n` plays the role of the index, the
extension need not be separable, and the proof is the direct column-module
count above rather than the source's Galois-cohomological argument.
