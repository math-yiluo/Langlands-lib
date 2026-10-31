# Proof: a unique rational fiber of a proper map has a finite neighborhood

This module proves
`Langlands.AlgebraicGeometry.UniqueRationalFiberFiniteNeighborhoodStatement` as the theorem
`Langlands.AlgebraicGeometry.uniqueRationalFiber_finiteNeighborhood`.

The setting is as in the statement. `K` is an algebraically closed field. `X` and `Y` are
locally of finite type over `K` through `p` and `q`. `f : X ⟶ Y` is proper with `f ≫ q = p`.
`x` is a rational point of `X` such that every rational point `x'` with `x' ≫ f = x ≫ f`
equals `x`. Write `z = x(closedPoint K)` and `y = f z`.

## Proof

1. **`z` and `y` are closed points.** `x ≫ p = 𝟙`, and `f ≫ q = p` gives
   `(x ≫ f) ≫ q = 𝟙`. So `x` and `x ≫ f` are rational points of `X` and `Y`. Mathlib's
   bijection `pointEquivClosedPoint` (in `Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`)
   sends each of them to a closed point, namely `z` and `f z = y`.
2. **The closed points of the fiber.** The fiber `F = f ⁻¹' {y}` is closed in `X`. Let `z'`
   be a point of `F` that is closed in `X`. Then `x' = pointOfClosedPoint p z'` is a rational
   point of `X` with `x'(closedPoint K) = z'` (`pointOfClosedPoint_comp`,
   `pointOfClosedPoint_apply`). The rational points `x' ≫ f` and `x ≫ f` of `Y` take the
   closed point of `Spec K` to `f z'` and to `f z`, which are equal. By
   `ext_of_apply_closedPoint_eq` for `q`, `x' ≫ f = x ≫ f`. The uniqueness hypothesis gives
   `x' = x`, so `z' = z`.
3. **The whole fiber is `{z}`.** `X` is a Jacobson space, because it is locally of finite
   type over a field (`LocallyOfFiniteType.jacobsonSpace p`). So the closed set `F` is the
   closure of `F ∩ closedPoints X` (`closure_inter_closedPoints`). By step 2 this
   intersection lies in the closed set `{z}`, so `F ⊆ {z}`. Also `z ∈ F`, so `F = {z}`. This
   is the first conclusion. It is a statement about underlying topological spaces only.
4. **Finite neighborhood.** The fiber `{z}` is finite, and `f` is proper. Mathlib's
   form of Zariski's main theorem,
   `exists_isFinite_morphismRestrict_of_finite_preimage_singleton` (Stacks 02UP, in
   `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`), gives an open `V ∋ y` such that
   `f ∣_ V : f⁻¹(V) ⟶ V` is finite. This is the second conclusion.

## Provenance

The statement and the route are by Worker 487. They are an internal supporting formulation of
the cited Mathlib results, not a transcription of an external theorem. The Lean proof follows
the suggested route in the statement task's context. Steps 1–3 use only closed-point and
Jacobson-space facts. Step 4 is the cited Mathlib lemma, applied without extra hypotheses.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
