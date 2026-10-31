# A fixed universal perfect representative of actual derived sections

Author: Worker 137.

`IsUniversalPerfectSectionsRepresentative f M K` is a proposition about an
already specified integer cochain complex `K` of modules over a commutative
ring `R`, a scheme map `f : X ⟶ Spec R`, and an actual module sheaf `M` on
`X`. All rings, schemes and module carriers have arbitrary universe `u`.

It requires the following three conditions:

1. `K` is strictly perfect in the published sense: its terms have lower and
   upper bounds, and every term is finite and projective.
2. The localization of `K` is isomorphic to actual right-derived relative
   sections of `M` over `f`, included from the bounded-below derived category
   into the standard unbounded derived category of `R`-modules.
3. For every commutative ring `T` and homomorphism `φ : R ⟶ T`, ordinary
   degreewise scalar extension of this same `K` is isomorphic, after
   localization, to actual derived `T`-module sections of the pullback of `M`
   on `pullback f (Spec.map φ)`. The structure map is `pullback.snd` and the
   coefficient pullback uses `pullback.fst`.

Each comparison is expressed by `Nonempty` of the actual isomorphism type.
The original-base comparison is a separate condition. The predicate asserts
no naturality or compatibility between the witnesses.

This definition is internal notation for exactly the three conditions inside
the existential quantifier in the published
`UniversalPerfectSectionsStatement`, generalized from line bundles to
arbitrary actual modules. It uses the unchanged definitions in
`PerfectModuleComplex`, `DerivedPlus` and `DerivedSections`, together with
Mathlib's actual scheme and module pullbacks. Its purpose is to state
transport results for one fixed representative without repeating those
conditions. No smoothness, properness, quasi-coherence or flatness is imposed
in the definition, and the definition proves no existence or base-change
theorem.
