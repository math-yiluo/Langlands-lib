# Fixed coordinates of twisted induction under a lifted subgroup action

This internal categorical development continues the Kan coordinates of actual twisted induction (`projection`, `transport`, `map_projection`, `moduleCoordinates` in the existing coordinate modules). It describes the sections of the induction fixed by a subgroup, for a local action that lifts the base action. This is the formula "fixed vectors of an induced module are a product over cosets", stated for the right Kan extension `(ι P ρ).op.ran.obj F` along the inclusion of the ordinary site into the twisted site.

## Setting

`F` is an ordinary presheaf of `R`-modules on `P.Over ⊤ X`, and `U` is an object of the twisted site. A local action `a : H →* (End U)ᵐᵒᵖ` of a subgroup `H ≤ G` is a lift (`IsLift a`) when each `a h` has twist `h⁻¹`. The group `H` then acts on sections of the induction by restriction along `a h`.

## Arrows between translated objects

- `transportTo f g g' hg` is the ordinary arrow `gU ⟶ g'V` with the same underlying arrow as a twisted arrow `f : U ⟶ V`. The target label `g'` is given together with a proof `hg` that it equals `g * (twist f)⁻¹`. With `g' = g * (twist f)⁻¹` and `rfl` it is definitionally `transport f g` (`transportTo_eq_transport`). Supplying the label separately avoids dependent rewriting of the label.
- `left_comp_left` and `left_one` record that the underlying arrows of a local action compose by the group law: `a h` followed by `a k` is `a (h * k)`, and `a 1` is the identity.
- For `K ≤ G`, `g : G` and a left coset `c = gK`, `cosetShift g c hc` is the element `g⁻¹ * c.out` of `K`. `mul_cosetShift` states `g * cosetShift = c.out`.
- For a lift `a` and `K ≤ H`, `cosetTransport ha hKH g c hc : gU ⟶ (c.out)U` is `transportTo` applied to `a (cosetShift g c hc)`. Its label is correct by `out_eq_mul_twist_inv`. `cosetTransport_left` gives its underlying arrow. `left_comp_cosetTransport_left` states that acting by `h ∈ K` and then going to the representative of `(g h)K = gK` is the same as going directly. `cosetTransport_out` states that the arrow from a representative to itself is the identity.

## Fixed sections and their coordinates

- `fixedSubmodule F a K` is the submodule of sections `s` over `U` with `ran.map (a h).unop.op s = s` for every `h ∈ H` whose image lies in `K`. `mem_fixedSubmodule_iff` states exactly this membership condition, and `fixedSubmodule_antitone` states that a larger `K` gives a smaller fixed submodule.
- `projection_eq_of_mem_fixedSubmodule` states the following for a fixed section `s`, any `h ∈ K` and any `g`: the coordinate of `s` at `g` is the coordinate at `g * (twist (a h))⁻¹`, restricted along `transportTo`. It is a direct consequence of `map_projection`. `projection_eq_cosetTransport` specializes it for a lift: the coordinate at `g` is the coordinate at the representative `c.out` of `gK`, restricted along `cosetTransport`.
- `fixedCoordinateMap K` is the linear map from `fixedSubmodule F a K` to `∀ c : G ⧸ K, objects F U c.out`, sending `s` to its coordinates at the chosen representatives `c.out` (`Quotient.out`). `fixedCoordinateMap_apply` records this formula.
- `fixedCoordinateMap_injective`: for a lift and `K ≤ H`, two fixed sections with the same representative coordinates are equal. Every coordinate is determined by a representative coordinate, and `section_ext` distinguishes sections by their coordinates.
- `spreadCoordinates` extends a family `u` of representative values to all labels `g`, by restricting `u (gK)` along `cosetTransport g`. `spreadCoordinates_eq` gives the same value for any proof that `gK = c`. `spreadSection` is the section with these coordinates, obtained from the inverse of `moduleCoordinates`. `projection_spreadSection` gives its coordinates.
- `spreadSection_mem`: for a lift, `spreadSection` is fixed by `K`. The proof uses `map_projection`, the coset identity `(g h)K = gK` for `h ∈ K`, and the composition law `left_comp_cosetTransport_left`.
- `fixedCoordinateMap_surjective`: `spreadSection` is a preimage, because `cosetTransport_out` makes its representative coordinates the given ones.
- **`fixedCoordinates ha hKH`**: for a lift `a` of `H` and `K ≤ H`, the `R`-linear equivalence
  `fixedSubmodule F a K ≃ₗ[R] ∀ c : G ⧸ K, objects F U c.out`
  between `K`-fixed sections of the induction and families of ordinary sections of `F` over the translates `c.out · U` of `U` by the chosen coset representatives. `fixedCoordinates_apply` states that it is the coordinate projection at `c.out`.

## Relation to discreteness and the locally discrete part

These results assume a topology on `G`, a local action system `L` on the twisted site, and a topology `J` on the twisted site with admissible refinements.

- `isDiscreteSection_iff_exists_mem_fixedSubmodule`: for `H` an open subgroup, a section is discrete for `a` (`IsDiscreteSection`) exactly when it lies in `fixedSubmodule F a K` for some open subgroup `K ≤ H`. This holds by definition.
- `fixedSubmodule_le_smoothSubmodule`: suppose `a` is admissible for `L` (`L.IsAdmissible U H a`) and `K ≤ H` is open. Then every `K`-fixed section lies in the existing locally discrete submodule `LocalActionSystem.smoothSubmodule L J (ran F) U`. Its discrete sieve contains the identity of `U`, so it is the maximal sieve and covers.

## Point products

Let `points : I → J.Point` be a family of points of a topology on `P.Over ⊤ X`, with `I : Type w`, and let `M : I → ModuleCat R`. The specialization uses `F = (PointProduct.productSheaf points (ModuleCat R) M).obj`.

- **`pointProductFixedCoordinates ha hKH`** composes `fixedCoordinates` with the existing section formula `PointProduct.sectionCoordinates` at each translate. This gives, for a lift `a` and `K ≤ H`, the `R`-linear equivalence
  `fixedSubmodule F a K ≃ₗ[R] ∀ (c : G ⧸ K) (i : I), (points i).fiber.obj ((translate P ρ c.out).obj U.obj) → M i`.
  The codomain is a product, over cosets and points, of arbitrary coefficient functions on the point fibers of the translated objects.
- `pointProductFixedCoordinates_apply` states that its value at `c`, `i` and `x` is `PointProduct.sectionCoordinate` at the point `x` of the translate by `c.out`, applied to the coordinate of `s` at `c.out`.

## Provenance and scope

The material is internal (derived): everything is proved from the current Library's Kan coordinates, transport formula, lift predicate, local action systems and point-product section formula, together with Mathlib's coset API (`QuotientGroup.eq`, `QuotientGroup.out_eq'`, `QuotientGroup.mk_mul_of_mem`). It is a helper for the local acyclicity of restricted smooth point products. Mathematically it is the standard description of invariants of an induced representation as a product over cosets (compare the induced equivariant sheaves in Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, 1995–1996 manuscript, §1.5; this is background only, not a cited definition). No literature definition is formalized here.

The results are exact algebraic identifications and say nothing analytic. They do not identify the full locally discrete part with a point product: they only show that `K`-fixed sections over an admissible lift are locally discrete. Comparing germs or stalks with filtered colimits over `K`, and any cohomological vanishing, are separate obligations.
