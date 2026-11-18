# Rearranging finite products of measures

Helper module for the proof of `Langlands.Global.RankinSelbergGlobal.RectangleTateStatement`
(see `RectangleTateProof.md`). It contains generic lemmas about finite products of measures
`Measure.pi` and binary products `Measure.prod`, in the namespace
`Langlands.Global.RankinSelbergGlobal.RectangleTate`. None of them mentions number fields.
They are elementary measure-theoretic facts, stated here because Mathlib does not provide
them in this form. There is no literature source; the provenance is internal.

Throughout, `a`, `b`, `c` are finite index types, and `β`, `γ` are measurable spaces.
All measures in the statements are σ-finite.

## Declarations

* `pi_smul_eq μ c`: for `c : a → ℝ≥0`,
  `Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ`.
  Proof: both sides agree on boxes (`Measure.pi_eq`, `Measure.pi_pi`), with
  `Finset.prod_mul_distrib`.

* `measurePreserving_uncurry μ`: uncurrying `(a → b → β) → (a × b → β)`
  (the inverse of `MeasurableEquiv.curry`) sends
  `Measure.pi (fun i => Measure.pi (fun j => μ i j))` to
  `Measure.pi (fun p : a × b => μ p.1 p.2)`.
  Proof: compare on boxes. The preimage of a box is an iterated box, and
  `Finset.prod_product` gives the product formula.

* `measurePreserving_swap μ`: the transposition `f ↦ (j ↦ i ↦ f i j)` sends
  `pi_i pi_j μ i j` to `pi_j pi_i μ i j`.
  Proof: it is the composite of uncurrying, the reindexing `measurePreserving_piCongrLeft`
  along `Equiv.prodComm`, and the inverse of uncurrying. The two maps agree pointwise.

* `measurePreserving_matrixProd μ ν`: splitting a matrix of pairs
  `M : a → b → β × γ` into the pair of matrices `((M i j).1, (M i j).2)` sends
  `pi_i pi_j (μ.prod ν)` to `(pi_i pi_j μ).prod (pi_i pi_j ν)`.
  Proof: compose Mathlib's `measurePreserving_arrowProdEquivProdArrow` row by row
  (`measurePreserving_pi`) and then across the rows.

* `measurePreserving_matrixProd_symm μ ν`: the inverse map (merging a pair of matrices into
  a matrix of pairs) is measure preserving in the other direction. It is the inverse
  (`MeasurePreserving.symm`) of the measurable equivalence behind
  `measurePreserving_matrixProd`.

* `measurePreserving_transpose k m μ`: for `μ : a → Measure β`, the map
  `f ↦ (i ↦ j ↦ v ↦ f v i j)` from `a → Fin k → Fin m → β` to
  `Fin k → Fin m → a → β` sends `pi_v pi_i pi_j μ v` to `pi_i pi_j pi_v μ v`.
  Proof: swap `v` with `i` (`measurePreserving_swap` with values in `Fin m → β`), then for each
  `i` swap `v` with `j` (`measurePreserving_pi` of `measurePreserving_swap`).

* `measurePreserving_rearrange k m μ ν`: for `μ : a → Measure β` and `ν : c → Measure γ`,
  the map
  `(p₁, p₂) ↦ (i ↦ j ↦ ((v ↦ p₁ v i j), (w ↦ p₂ w i j)))`
  sends `(pi_v pi_i pi_j μ v).prod (pi_w pi_i pi_j ν w)` to
  `pi_i pi_j ((Measure.pi μ).prod (Measure.pi ν))`.
  Proof: `measurePreserving_transpose` on both factors (`MeasurePreserving.prod`),
  followed by `measurePreserving_matrixProd_symm`.

In the proof of `RectangleTateStatement`, `a` is the set of real places, `c` the set of
complex places, `β = ℝ`, `γ = ℂ`, and `measurePreserving_rearrange` turns families of real
and complex `k × m` matrices into `k × m` matrices with entries in the mixed space
`ℝ^(r₁) × ℂ^(r₂)`.
