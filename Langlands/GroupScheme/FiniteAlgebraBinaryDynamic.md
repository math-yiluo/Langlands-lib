# Actual contractions of binary elementary maps over finite algebras

Let `k : Type u` be a field and `D : Type u` a `k`-algebra with
`Ring D`. Choose finite bases `bD : Basis (Fin d) k D` and
`bA : Basis (Fin n) k (Matrix (Fin 2) (Fin 2) D)`.
The construction works in every characteristic, including
noncommutative `D`, and on every relative test scheme.

In `Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot`, the Boolean
`neg = false` selects the actual upper elementary map and `neg = true`
selects the lower map. The actual homomorphism `cocharacter neg` from
the ground-field multiplicative group to the binary matrix-algebra
unit group has scalar diagonal entries `(t,t⁻¹)` for the upper map and
`(t⁻¹,t)` for the lower map. Here scalar sections enter the left factor
of `Γ(T,O_T) ⊗[k] D`. `tensorMatrixEquiv_cocharacter` gives the formula
on every relative test `T`.

For an additive test point with tensor parameter `a`, `contraction neg`
is the actual morphism on `T × A¹` whose elementary matrix parameter is
`s²a`, with `a` pulled back from `T`. The theorem
`tensorMatrixEquiv_comp_contraction` gives this formula after every
further test pullback. Centrality of scalar sections implies that
conjugation by the selected scalar diagonal multiplies the elementary
parameter by `t²`, even when the tensor coefficient algebra is
noncommutative. Consequently `contraction_isOrbitExtension` identifies
the curve over `T × Gm` with the actual conjugation orbit, and
`contraction_evalZero` proves that its value at zero is the identity.

The theorem `elementary_range_le_dynamicUnipotent` states containment
of the entire actual elementary image subgroup functor in the dynamic
unipotent subgroup functor of the corresponding actual cocharacter.
This includes all upper or lower elementary tensor parameters by the
surjectivity established in `FiniteAlgebraBinaryRoots`.

This is an internal construction from the existing elementary matrix
identities, actual matrix point models, vector coordinates and dynamic
subgroup definitions. The proof packages the scalar diagonal as a
natural point homomorphism and applies `homOfPoints` to obtain the
actual cocharacter. The inverse actual matrix point comparison
constructs the polynomial curve. Entrywise coefficient naturality,
the central scalar conjugation calculation and the affine line's
unit and zero restrictions prove its orbit and limit properties.

The target group here is the full binary matrix-algebra unit scheme.
Reduced-norm-one lifts, structural properties of the norm-one kernel,
parabolic radical containment, arithmetic generation and local SK1,
classification and the unrestricted local Kneser–Tits theorem remain
separate obligations.
