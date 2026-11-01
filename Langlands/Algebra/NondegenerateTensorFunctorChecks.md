# Complete interfaces and boundary checks for the actual tensor functors

This internal companion checks `NondegenerateTensorFunctor`. Its declarations
are derived interface checks and examples for the construction module, whose
mathematical source is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Chapter I conventions and I.1.2
(printed pp.5–7 / PDF pp.11–13) and I.2.2–I.2.3 (printed pp.15–18 / PDF
pp.21–24). The examples below are internal tests, not additional assertions
attributed to Renard. The construction module explains the passage from the
source's complex algebras to the arbitrary-ring additive setting and its
remaining coefficient comparisons.

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source audit also read `renard-2010-corrections-complements`, PDF pp.1–2
and pp.18–19. Those supplementary passages affect later adjunction directions
and warn that a corner's right action can be degenerate. They supply no
comparison or adjunction theorem here.

The interface examples assign each entire unapplied declaration, using `@`,
to its expected telescope. They check the ambient functor and its additive
instance, intrinsic output nondegeneracy, the nondegenerate functor and its
additivity, its entire composition equality with the ambient inclusion, and
the restricted functor and its additivity. The unbundled map, additive Hom
map, whole underlying additive-map formula, identity law and composition law
retain independent source, intermediate and target carrier universes. The
nondegenerate and restricted morphism checks identify the full-subcategory
morphism's entire original ambient Hom.

The same tests run at arbitrary independent universes and at both assignments
`(uS,uR,uX,v,w,z) = (0,1,1,0,1,0)` and `(1,0,0,1,0,1)`.
The target carrier universe is exactly `max uX v`; no ring universe is
identified with a variable carrier universe. Separate complete telescopes check
`F`, `P`, their additive instances, restriction and inclusion equalities,
carrier/group/action formulas and whole morphism formulas. They also check
`regularF`, `regularP`, their additivity and restriction equalities, both
intrinsic regular-action nondegeneracy laws, and the adapter from two-sided
to left nondegeneracy. These source tests use independent `uA,uB,v` and the
two assignments `(0,1,0)` and `(1,0,1)`.

The structure-selection section activates competing ring structures on `S`
and `R`, competing additive groups on `X` and `M`, competing original actions,
and a competing additive group and action on the actual tensor carrier. It
first verifies which alternatives instance search sees, then explicitly
selects the named original structures. The ambient and nondegenerate functor
objects still have exactly the original quotient carrier, its published
additive group and `NonUnitalBimoduleTensor.leftModule`. The complete original
Hom and its additive-map projection retain those choices. Separate source
checks keep precisely `NonUnitalModule.rightRegular B` in `regularF` and
`NonUnitalModule.regular B` in `regularP` while alternative original actions
are available.

The boundary examples exercise the actual constructions:

- A subsingleton first factor gives a nondegenerate, subsingleton tensor
  object using the intrinsic law. A subsingleton second factor gives a
  nondegenerate tensor even with an arbitrary first left action: the tensor
  identity map is zero by pure-tensor extensionality, and the zero idempotent
  fixes every tensor. Zero scalar rings in unrelated universes are also
  admitted by the ambient functor.
- All integer actions may be zero. Integer multiplication is a balanced
  biadditive pairing because both balancing actions vanish, and its induced
  map sends the actual pure tensor `1 ⊗ 1` to `1`. The ambient tensor object
  is therefore nonzero, every residual scalar endomorphism is zero, and its
  unit-action law and nondegeneracy both fail. This verifies that the ambient
  construction permits a unital ring acting by zero on a nonzero group.
- The first integer factor may instead have its regular left action and
  zero right action, while the second factor still has zero left action.
  Both balancing actions are degenerate, and multiplication again detects
  the nonzero pure tensor `1 ⊗ 1`. The intrinsic construction puts this actual
  nonzero tensor in the nondegenerate codomain and gives its regular left
  integer action. The examples explicitly disprove nondegeneracy of the
  second factor and of the first factor's right action.
- With regular integer actions on both factors, the nondegenerate functor
  gives the actual tensor object, the scalar formula `2 • (1 ⊗ 1) = 2 ⊗ 1`
  and the identity-map formula. The multiplication pairing again detects
  `1 ⊗ 1` as nonzero.

The pairing arguments are only nonzero-witness checks. They establish no
regular-tensor isomorphism or scalar-restriction comparison. Coefficient and
unitization bridges, tensor comparison theorems, Hom-based functors,
adjunctions and exactness remain separate obligations as in the construction
module. Worker 185 authored this companion and its source audit; Worker 1193
authored the construction module.
