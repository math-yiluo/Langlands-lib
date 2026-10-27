# Additive stable generation for a supplied integer-unitized action

This statement-only module gives three closed propositions in the namespace
`Langlands.Algebra.AdditiveUnitizationGeneration`. These are derived internal
algebraic targets motivated by Renard 2026; this module proves none of them.

Each component binds, in order, a nonunital ring `A : Type uA`, an additive
commutative group `M : Type uM`, an actual
`Module (Unitization ℤ A) M`, and a nonunital ring homomorphism
`ρ : A →ₙ+* AddMonoid.End M`. It assumes the elementwise formula
`u • m = u.fst • m + ρ u.snd m` for every integer-unitization element `u`
and every `m`. Here `u.fst : ℤ` and `u.snd : A` are the two components of
`u`, `u.fst • m` is the integer multiple coming from the additive group
structure of `M`, and `ρ u.snd m` evaluates the additive endomorphism
`ρ u.snd` at `m`. Integer scalar structures on `A` are canonical; no scalar
field, scalar-linearity hypothesis on `ρ`, or extra scalar tower on `M` is
input. The algebra and module universes are independent, with aggregate
universe order `uA uM`.

The actual additive subgroup `P` is stable when
`∀ a m, m ∈ P → ρ a m ∈ P`. Every occurrence of stability in the Lean
targets spells out this condition. A finite set `S : Finset M` is
contained in `P` when `(↑S : Set M) ⊆ P`. The additive subgroup underlying
a unitized submodule `Q` is written
`Submodule.toAddSubgroup (R := Unitization ℤ A) Q`, and containment of
additive subgroups is the order `≤` on `AddSubgroup M`.

- `SubmoduleGenerationStatement` says that any actual unitized submodule
  `Q` is finitely generated if and only if a finite set `S` lies in `Q`
  and every stable additive subgroup containing `S` contains the additive
  subgroup underlying `Q`.
- `ModuleGenerationStatement` says that `Module.Finite (Unitization ℤ A) M`
  holds if and only if a finite set `S` is contained in no proper stable
  additive subgroup.
- `NoetherianGenerationStatement` says that
  `IsNoetherian (Unitization ℤ A) M` holds if and only if every stable
  additive subgroup `P` contains a finite set `S` such that every stable
  additive subgroup containing `S` contains `P`.
- `AdditiveUnitizationGenerationStatement` is the conjunction of those
  complete component propositions in that order, each instantiated at the
  same universes `uA uM`.

Each component is a closed proposition: all of `A`, `M`, their instances,
`ρ` and the action formula are bound inside it, so the definitions take no
parameters other than the two universe levels. The statements are
proposition definitions only; any proof belongs to a separate task.

The targets use ordinary Mathlib unitization, modules, finite generation,
Noetherianity and additive subgroups. They assume an actual unitized module
and its explicit action formula rather than constructing one or assuming a
lattice correspondence. They allow noncommutative and nonunital original
rings, zero original actions, and arbitrary additive stable subgroups. No
unit action for the original ring, nontriviality, countability, finite
dimension or complex-linearity is required.

The registered governing original is David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Motivating passages are the conventions printed5–6/PDF11–12, I.2.1
printed14/PDF20, A.I.3 printed248–249/PDF254–255, and C.II
printed276,279/PDF282,285. In outline:

- the conventions (printed5–6/PDF11–12) do not assume rings unital, nor
  modules over unital rings unital, and write `M(A)` for unital modules;
- I.2.1 (printed14/PDF20) adjoins a unit to a nonunital complex algebra,
  `Ã = A ⊕ ℂ·1_A`, and compares `Ã`-linear maps with additive `A`-maps
  that are also complex-linear;
- A.I.3 (printed248–249/PDF254–255) defines Noetherian and finite-type
  objects categorically, with an example over a unital ring in `M(A)`;
- C.II (printed276/PDF282 and printed279/PDF285) introduces stable
  endomorphisms and ends with a proposition about finite-type modules over
  a Noetherian commutative complex algebra.

Those passages motivate studying general nonunital actions and finiteness.
The integer unitization, the action formula and the three equivalences
above are internal targets derived from that motivation, not assertions
attributed verbatim to Renard.

These targets do not identify the book's categorical finite-type predicate
or its nonunital Noetherian-algebra convention with these explicit
conditions. They also do not identify additive stable subgroups with
scalar-linear stable subspaces. The general action, Hom, lattice,
restriction and quotient constructions, source-convention comparisons,
regular-kernel bridge, actual localization maps, decomposition and
localized-pair identification remain separate obligations.
