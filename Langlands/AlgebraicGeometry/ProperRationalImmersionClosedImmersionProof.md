# The global closed-immersion criterion from the local criterion

Module `Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionProof`.

## Statements

```lean
theorem properRationalImmersion_isClosedImmersion_of
    (hLoc : ProperRationalImmersionLocalClosedImmersionStatement.{u}) :
    ProperRationalImmersionClosedImmersionStatement.{u}

theorem properRationalImmersion_isClosedImmersion :
    ProperRationalImmersionClosedImmersionStatement.{u}
```

The second theorem proves the target `ProperRationalImmersionClosedImmersionStatement`
unconditionally. It is the first theorem applied to the Library proof
`properRationalImmersion_localClosedImmersion` of the local criterion (module
`Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionProof`).

The local criterion `ProperRationalImmersionLocalClosedImmersionStatement` implies the global
criterion `ProperRationalImmersionClosedImmersionStatement`. Let `K` be an
algebraically closed field and `f : X ⟶ Y` a proper morphism of schemes locally of finite
type over `K` (structure maps `p` and `q`, `f ≫ q = p`). Suppose `f` is injective on
`K`-points and that every rational tangent vector killed by `f` is the constant one. Then
`f` is a closed immersion. In the first theorem the local criterion appears as the hypothesis
`hLoc`, and nothing else is assumed beyond the global statement's own hypotheses.

## Proof

This is the globalization step (step 4) of the route suggested in proof task
`b14fb360-bcf2-4516-93b8-71de33f0fba5`. It is derived from the end of the proof of Stacks
Project Lemma 33.23.1 (tag 0E8R, registered source
`stacks-very-ampleness-support-2026-10-29`). The Lean proof goes as follows.

1. *Jacobson spaces.* A field is a Jacobson ring, so `Spec K` is a Jacobson space. Since `X`
   and `Y` are locally of finite type over `K`, they are Jacobson spaces too
   (`LocallyOfFiniteType.jacobsonSpace`).
2. *Local neighbourhoods.* Let `x` be a rational point of `X`, that is, `x ≫ p = 𝟙`. The
   global hypotheses give the hypotheses of the local criterion at `x`:
   - any rational point `y` with `y ≫ f = x ≫ f` equals `x`;
   - any tangent vector at `x` that `f` maps to the constant tangent vector is the
     constant one.

   So `hLoc` gives an open `V x ⊆ Y` containing `f (x (closed point))` such that
   `f ∣_ V x` is a closed immersion. The proof chooses one such `V x` for every rational
   point.
3. *The image's complement.* A proper morphism is universally closed, so `Set.range f` is
   closed. Its complement `V₀` is open, and `f ⁻¹ᵁ V₀` is empty. A morphism with empty source
   is a closed immersion (Mathlib instance), so `f ∣_ V₀` is a closed immersion.
4. *The opens cover `Y`.* Let `W` be the family indexed by `Option` of rational points:
   `none ↦ V₀` and `some x ↦ V x`. Suppose its union were not all of `Y`. Its complement
   would then be a nonempty closed set. Since `Y` is Jacobson, the complement contains a
   closed point `y` (`nonempty_inter_closedPoints`).
   - If `y ∉ Set.range f`, then `y ∈ V₀`.
   - If `y = f x₀`, the fibre `f ⁻¹' {y}` is closed and nonempty. Since `X` is Jacobson,
     the fibre contains a closed point `x₁`. Because `K` is algebraically closed, Mathlib's
     `pointOfClosedPoint p x₁` is a rational point `r` with `r (closed point) = x₁`
     (`pointOfClosedPoint_comp`, `pointOfClosedPoint_apply`). Then `y = f x₁ ∈ V r`.

   Either way `y` lies in the union, a contradiction.
5. *Conclusion.* Being a closed immersion is local on the target
   (`IsZariskiLocalAtTarget.of_iSup_eq_top`). Every restriction `f ∣_ W o` is a closed
   immersion, so `f` is a closed immersion.
6. *The unconditional theorem.* `properRationalImmersion_isClosedImmersion` instantiates
   `hLoc` with `properRationalImmersion_localClosedImmersion`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.

## Authorship

Worker 898 wrote the conditional globalization `properRationalImmersion_isClosedImmersion_of`.
Worker 712 checked it and added the unconditional theorem.
