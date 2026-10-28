# Stable-generation comparisons for a supplied unitized action

This proof module proves the published aggregate
`Langlands.Algebra.UnitizationStableGeneration.UnitizationStableGenerationStatement`
in theorem `unitizationStableGeneration`. The three independent universes
are `uR`, `uA`, `uM`, in that order. The aggregate is the ordered conjunction
of the submodule, whole-module and Noetherian comparisons. The published
statement is imported and its pair is left unchanged.

Let `R` be a commutative ring, `A` a nonunital ring with an ordinary
`R`-module structure and scalar-bilinear multiplication, and `M` an additive
commutative group. The hypotheses supply actual ordinary `R`- and
`U = Unitization R A`-module structures on `M`, the scalar tower, a
nonunital algebra representation `ρ : A →ₙₐ[R] Module.End R M`, and the
coordinate action law `u • m = u.fst • m + ρ u.snd m`.
No general action constructor or lattice equivalence is introduced.

For an actual `U`-submodule `Q`, `fg_iff_stable_generators` compares `Q.FG`
with the explicit finite-generation universal property among actual
scalar-linear stable submodules of `M`. In the forward direction its proof
gives each stable `R`-submodule `P` a temporary `U`-submodule with the same
carrier. The coordinate law proves closure. Ordinary span minimality then
shows that containment of the finite generators implies containment of
`Q.restrictScalars R`. For the reverse direction take the restricted
ordinary `U`-span of the proposed finite set. Acting with `Unitization.inr a`
proves stability. The universal property and containment of the finite set
in `Q` give both span inclusions.

`finite_iff_stable_generators` applies this submodule comparison to the top
submodule, using `Module.finite_def`. Containment of the whole module forces
the stable submodule to be top, and conversely top contains the whole
module. `noetherian_iff_stable_generators` applies the submodule comparison
to each stable scalar submodule, giving it the temporary `U`-submodule
structure, and conversely restricts every actual `U`-submodule to `R`.
The three closed component theorems discharge all parameters of these
helpers. `unitizationStableGeneration` combines them in the target order.
The supplied action-law section ends before these closed theorems, so
the aggregate theorem has no extra section parameters.

This is derived internal algebra motivated by Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026: conventions printed page 6/PDF page 12; I.2.1, printed page
14/PDF page 20; A.I.3, printed pages 248–249/PDF pages 254–255; and the
final C.II proposition, printed page 279/PDF page 285. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact formulas are internal comparisons rather than numbered book
assertions. This proof uses ordinary unitized spans and the coordinate
law. It does not identify these predicates with the book's categorical
finite-type predicate or its nonunital Noetherian convention, compare
additive and scalar-linear generation, or prove the localization theorem.
The finite-generation property here retains the scalar contribution even
when the original action is zero. There is no field, finite-dimension,
countability, nontriviality, unit or commutativity assumption on `A`.

Worker 709 wrote this proof. Worker 877 checked it against the published
statement and submitted it.
