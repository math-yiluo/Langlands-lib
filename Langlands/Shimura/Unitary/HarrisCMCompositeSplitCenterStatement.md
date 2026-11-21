# The oriented split center of Harris's CM composite

`Langlands.Shimura.FiniteUnitary.HarrisCMCompositeSplitCenterStatement` uses
the given CM field `E` and intermediate fields `E₀`, `K₀` with `E₀` totally
real and `E₀ ⊔ K₀ = ⊤`. At a finite place `v` of `E` whose rational residue
characteristic splits in the imaginary quadratic `K₀`, put `w` equal to the
actual place below `v` in `E₀`. The statement asserts:

- The actual extension `E/E₀` is quadratic. Both `v` and its CM conjugate lie
  over `w`; they are distinct and exhaust the places above `w`.
- The completed center at `w` has a `SplitPlaceIdentification E₀ E w` with
  conjugation acting by coordinate swap. The two completion isomorphisms from
  `(E₀)_w` are algebra isomorphisms over `(E₀)_w` via the canonical completion
  maps. Under these isomorphisms the first and second coordinates are the
  `completedCenterMap` evaluations at `v` and its CM conjugate, respectively.

## Provenance and boundary

This is the derived arithmetic comparison between Harris, *The local Langlands
correspondence for GL(n) over a p-adic field, n < p* (1998), §1, Theorem 1.2(i),
p. 185, and the prescribed split-place input in Clozel, *Représentations
galoisiennes associées aux représentations automorphes autoduales de GL(n)*
(1991), §2, Proposition 2.3(i)–(ii) and its prescribed-place remark, pp. 105–106.
The coordinates are retained because Clozel's transfer uses representations
at the actual two CM places, not an unlabelled isomorphism class of local
centers. The natural proof inputs are split-place distinctness and the
completed tensor product over the places above `w`. The proposition does not
yet assert a global algebra with involution, a real signature, or any transfer
of representations.
