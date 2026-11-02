# Cobar cocycles and invariant lifting

Author: Worker 148.

This is an internal algebraic sufficient criterion for the published
`GroupoidCoaction.IsAcyclic` predicate. It imports and preserves the Library
coaction definitions. Let B and C be commutative rings in Type u, let C be a
B-algebra through the source map, and let t : B → C be the target map. Modules
lie in an independent Type v.

For a coaction θ on M, `coboundary` is the additive map
δ(m) = θ(m) − 1 ⊗ m. `IsOneCocycle θ x` requires the equation
φ₃(x) = φ₂(x) + (α at φ₂ composed with φ₁)(x) at all composable points over
flat B-algebras T in Type u. The maps φ₁, φ₂, φ₃ and their compatibility
conditions are exactly those of the published `coassoc` field. The algebra
structure on T is given by the final source point. `OneCohomologyVanishes`
says that each such cocycle is δ(m) for some m.

The restriction to flat test algebras is part of these new definitions. This
module does not identify the predicate with a separately constructed
cohomology group or prove equivalence with the cocycle equation at every
ring-valued point. It suffices for the invariant-lifting theorem below.

The main theorem `isAcyclic_of_oneCohomologyVanishes` assumes that C is flat
over B and proves θ.IsAcyclic. Given an invariant element q in a quotient,
choose a lift g. Its defect δ(g) lies in the kernel after tensoring, since the
quotient map preserves coactions. Flat exactness gives x in C ⊗ M whose image
is δ(g). The coassociativity equation shows that δ(g) is a cocycle. Tensoring
the kernel injection with each flat test algebra is injective; naturality
then reflects that equation to x. By vanishing x = δ(m). Thus g − i(m) is an
invariant lift of q. The implementation uses Mathlib's
`Module.Flat.lTensor_exact`, `LinearMap.exact_iff` and
`Module.Flat.lTensor_preserves_injective_linearMap`.

The accompanying lemmas prove the pure-tensor formula for `coactionCompose`,
naturality of pullback and composition, that every coboundary is a cocycle,
naturality of coboundaries, and reflection of cocycles along injective
morphisms. Tensor naturality and compatibility with multiplication are
proved by tensor induction; the coboundary identity uses `coassoc` and the
additive group identity.

This construction and proof are derived directly from the published ring
formulas and the elementary kernel-lifting argument. They are the first
algebraic step towards the task's acyclicity theorem and do not establish
vanishing for finitely covered Noetherian equivalence relations. No
geometric quotient, affine-descent theorem or Noetherian dévissage is used.
