# Internal stable-generation comparisons for a supplied unitized action

This statement-only module gives three closed `Prop`-valued targets and their
conjunction. It proves none of them. The namespace is
`Langlands.Algebra.UnitizationStableGeneration`; the scalar ring, original
algebra and module carrier have independent universes, in the order
`uR`, `uA`, `uM`.

These are derived internal algebraic comparisons motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026: I.2.1, printed page 14/PDF page 20; A.I.3, printed pages
248–249/PDF pages 254–255; and the final C.II proposition, printed page
279/PDF page 285. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These exact Mathlib formulations are internal targets rather than numbered
assertions quoted from the book.

Renard's global conventions (Notations et conventions, printed page 6/PDF
page 12) permit nonunital rings and, even over a unital ring, modules on
which the unit need not act as the identity. I.2.1 extends compatible
complex-linear actions to a unitization. The finite-type module example in
A.I.3 explicitly works in the category `M(A)` of modules over a unital ring
`A` on which the unit acts as the identity. C.II motivates a comparison with finite and Noetherian ordinary
unitized modules. This module specifies the stable-generation condition
directly. It does not identify the condition with the book's categorical
finite-type predicate or define the book's nonunital Noetherian convention.

All three propositions bind their carriers and structures internally.
They quantify over a commutative ring `R`, a nonunital ring `A`, an
`R`-module structure on `A`, and
`IsScalarTower R A A` and `SMulCommClass R A A`, which express the
compatibility of scalar multiplication with multiplication in `A`.
They also quantify over an additive commutative group `M`, an `R`-module
structure on `M`, an actual ordinary module structure over
`U = Unitization R A`, and the actual tower `IsScalarTower R U M`.
Finally they supply a nonunital algebra homomorphism
`ρ : A →ₙₐ[R] Module.End R M` and assume the elementwise action formula

```text
u • m = u.fst • m + ρ u.snd m.
```

The formula relates the supplied actions. It assumes no finite generation,
Noetherianity, submodule comparison or span universal property. This module
constructs no action or general lattice equivalence.

An actual `R`-submodule `P` is called stable in this description when
`∀ a m, m ∈ P → ρ a m ∈ P`. The Lean propositions spell this condition
out at each occurrence.

`SubmoduleGenerationStatement` says that, for every actual `U`-submodule
`Q`, its ordinary finite generation `Q.FG` is equivalent to the existence
of a finite set `S` in `Q` with the following property: every stable
`R`-submodule `P` containing `S` contains `Q.restrictScalars R`.
Thus the generators are taken among scalar-linear stable submodules of
the ambient module. It does not assert that `Q` is finite over `R`.

`ModuleGenerationStatement` says that ordinary `Module.Finite U M` is
equivalent to the existence of a finite set `S` such that every stable `R`-submodule
containing `S` equals the whole module.

`NoetherianGenerationStatement` says that ordinary `IsNoetherian U M`
is equivalent to the following explicit property: for every stable
`R`-submodule `P`, a finite set `S` lies in `P` and every stable
`R`-submodule `Q` containing `S` contains `P`.
The containment is in the ambient `M`; no inherited action or abstract
subobject predicate replaces it.

`UnitizationStableGenerationStatement` is the conjunction of the preceding
three closed propositions, in that order. A proof successor can use the
ordinary unitized span and the temporary unitized submodule with the carrier
of a stable `P`. The action formula gives its closure; action by
`Unitization.inr a` gives stability in the reverse direction. This is a
rationale for the targets, not a proof claim in the statement-only module.

There is no field, finite-dimension, countability, nontriviality, unit or
commutativity assumption on `A`. Zero original actions are permitted.
Over a zero original action these formulas retain the scalar contribution
to generation. Worker 6's separate general stable-subspace and
unitization/action/Hom/lattice constructions remain separate. The regular
algebra/scalar-kernel equivalence, source-convention comparisons, categorical
comparisons and the actual final localization theorem also remain separate.
