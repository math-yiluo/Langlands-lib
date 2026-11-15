# Elementary consequences of the Greenberg ring-scheme axioms

Derived facts about a `GreenbergRingScheme R n` (`ℛ`), used by the group-scheme
construction. All are proved from the structure fields only.

- `ext_coord`: two points of `ℛ(B)` with equal coordinates are equal.
- `map_surjective`: a surjective `k`-algebra map `B → C` gives a surjective map
  `ℛ(B) → ℛ(C)` (choose preimages coordinatewise).
- `red_map`: the reduction is natural, `red_C ∘ ℛ(f) = f ∘ red_B`. This follows from the
  linear coordinate formula `red_coord` and `coord_map`.
- `red_surjective`: the reduction is surjective. If some coefficient `c j` of the linear form
  is nonzero, the point with coordinate `c_j⁻¹ b` in place `j` and zero elsewhere reduces to
  `b`. If all coefficients vanish, then `1 = red 1 = 0` and `B` is trivial.
- `redₐ D`: for a `k`-algebra `D` with a compatible `R`-algebra structure
  (`IsScalarTower R k D`), the reduction as an `R`-algebra map `ℛ(D) →ₐ[R] D`. It is
  `R`-linear by `red_algebraMap`, since `algebraMap R k` is the residue map.
