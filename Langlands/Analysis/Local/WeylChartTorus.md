# Haar measures near the identity and on the torus

The module `Langlands.Analysis.Local.WeylChartTorus` expresses Haar measure on `Rˣ` near the
identity, and Haar measure on the torus `torusGroup γ`, in the additive coordinates of
`Langlands.Analysis.Local.WeylChartCoordinates`. Here `F` is a complete, proper, ultrametric
nontrivially normed field, `R` a finite-dimensional, complete, ultrametric normed
`F`-algebra, and `R` and `Rˣ` carry their Borel structures.

## The unit map

`unitOf` is continuous on the set of units (`continuousOn_unitOf`) and Borel measurable
(`measurable_unitOf`), being the piecewise combination of a continuous map on an open set and
a constant.

## Near the identity

`ringHaar hγ` is the pushforward of `coordHaar γ` under `coordCLE hγ`, an additive Haar
measure on `R`. For a Haar measure `μ` on `Rˣ` and a small radius `r`, `identityConst hγ hr μ`
is `μ (unitBall) * (ringHaar (ringBall))⁻¹`.

- `map_val_restrict_of_subset_unitBall`: for every measurable `S ⊆ unitBall hγ hr`, the value
  map carries `μ` restricted to `S` to `identityConst hγ hr μ` times `ringHaar` restricted to
  `val '' S`. This follows from `map_val_restrict_compactOpen` for the compact open subgroup
  `unitBall` and restriction to `S`.

## The torus

`torusValue γ` sends a torus element to its value in the centralizer subalgebra. It is an
open embedding whose range is the set of elements of that subalgebra that are units of `R`
(`isOpenEmbedding_torusValue`, `range_torusValue`). `torusBall hγ hr` is the compact open
subgroup of the torus within coordinate radius `r` of `1`; `torusValue` maps it onto the
closed ball of radius `r` about `1` in the centralizer subalgebra
(`image_torusValue_torusBall`, `isOpen_torusBall`, `isCompact_torusBall`). The centralizer
coordinate is `torusUnit γ s = unitOf (1 + s)`; for `‖s‖ ≤ r`,
`torusValue (torusUnit γ s) = 1 + s` (`torusValue_torusUnit`). Also
`torusChart γ s = torusUnit γ s · γ` (`torusChart_eq`).

- `restrict_torusBall_eq`: for a Haar measure `μT` on the torus, `μT` restricted to
  `torusBall` equals `torusConst hγ hr μT` times the pushforward under `torusUnit γ` of
  additive Haar measure on the centralizer subalgebra restricted to the closed ball of radius
  `r` about `0`, where `torusConst = μT (torusBall) * (addHaar (closedBall 0 r))⁻¹`.

The proof pushes both sides forward along the open embedding `torusValue`. The left side
becomes a multiple of additive Haar measure on the ball about `1` by
`restrict_eq_smul_map_normalizedHaar` and the Library theorem
`map_normalizedHaar_eq_restrict_of_units` for the units of the centralizer subalgebra. The
right side becomes the translate of the restriction to the ball about `0`, which is the same
measure by translation invariance. Pulling back along the embedding gives the identity.
