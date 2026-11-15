# Proof of the singular-ideal factorization lemma

This module proves
`Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationStatement`
(Stacks Project, *Smoothing ring maps*, Lemma 2.8, tag 07EU) as the theorem
`Langlands.CommutativeAlgebra.Popescu.singularIdealFactorization`.

**Statement.** Let `R → A → Λ` be ring maps, with `A` finitely presented over
`R` and `f : A →ₐ[R] Λ`. If the image of the singular ideal `H_{A/R}` generates
the unit ideal of `Λ`, then `f` factors as `A → B → Λ` with `B` smooth over `R`.

## Construction

Because `1 ∈ H_{A/R} Λ`, we can write `1 = ∑_{i<n} μᵢ f(aᵢ)` with `aᵢ ∈ H_{A/R}`
and `μᵢ ∈ Λ`. These come from `Submodule.mem_span_set'` applied to
`Ideal.map f H = span (f '' H)`. Set

`B = A[X₁, …, Xₙ] / (∑ aᵢ Xᵢ - 1)` (`SingularIdealFactorization.UnitHyp a`).

The factorization is `A → B` (structure map) followed by `B → Λ`, `Xᵢ ↦ μᵢ`. This
map is well defined because `∑ f(aᵢ) μᵢ - 1 = 0`. Here `Λ` is made an `A`-algebra
through `f`. This is the construction in Stacks.

## Smoothness of `B` over `R`

The Stacks proof uses the smooth algebras `A_{aᵢ}` and the cover by the
`D(aᵢ)`. The Lean proof follows the same route:

1. `formallySmooth_away_of_mem_singularIdeal`: if `a ∈ H_{A/R}`, then `D(a)` lies
   in the smooth locus. Every prime outside the smooth locus contains `a`, by the
   definition of `singularIdeal` as a vanishing ideal. Then
   `Algebra.basicOpen_subset_smoothLocus_iff` gives that `A_a` is formally smooth
   over `R`.
2. `formallySmooth_unitHyp`: `B` is formally smooth over `A`. This is proved
   directly from the lifting criterion. Take a square-zero ideal `J ⊆ C` and an
   `A`-algebra map `B → C/J`. Choose lifts `cᵢ` of the images of the `Xᵢ`, and put
   `e = ∑ aᵢ cᵢ - 1`. Then `e ∈ J`, so `e² = 0`. Sending `Xᵢ ↦ cᵢ (1 - e)` gives a
   lift, because `∑ aᵢ cᵢ (1 - e) = (1 + e)(1 - e) = 1`.
3. `formallySmooth_away_unitHyp`: for `bᵢ` the image of `aᵢ` in `B`, the ring
   `B_{bᵢ}` is formally smooth over `A_{aᵢ}`. This uses
   `Algebra.FormallySmooth.localization_map`, with the algebra structure
   `localizationAlgebra` and the identification
   `(powers aᵢ).map (A → B) = powers bᵢ` (`Submonoid.map_powers`). Since `A_{aᵢ}`
   is formally smooth over `R` by step 1, `B_{bᵢ}` is formally smooth over `R` by
   composition (`Algebra.FormallySmooth.comp`).
4. `finitePresentation_unitHyp`: `B` is finitely presented over `R`. It is the
   quotient of the finitely presented algebra `A[X₁, …, Xₙ]` by a principal ideal.
5. `smooth_unitHyp`: in `B` we have `∑ bᵢ Xᵢ = 1` (`sum_eq_one`), so every prime
   of `B` misses some `bᵢ`. By step 3 and `Algebra.basicOpen_subset_smoothLocus_iff`,
   each `D(bᵢ)` lies in the smooth locus. So the smooth locus is all of `Spec B`,
   and `Algebra.smoothLocus_eq_univ_iff` gives that `B` is formally smooth over `R`.
   Together with step 4, `B` is smooth over `R`.

## Assembly

The theorem `singularIdealFactorization` takes `g : A →ₐ[R] B` to be the
structure map `IsScalarTower.toAlgHom R A B` and `h` to be the `A`-algebra map
`B → Λ` from the construction with its scalars restricted to `R`. The identity
`h.comp g = f` is then the statement that `h` commutes with the `A`-algebra
structure maps, where `algebraMap A Λ = f`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in literature
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 2.8 (Tag 07EU, printed
page 4). The source proof gives the construction and says that `B_{fᵢ}` is
smooth over `A_{fᵢ}`, leaving the details out. Steps 2–5 above supply these
details.

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
