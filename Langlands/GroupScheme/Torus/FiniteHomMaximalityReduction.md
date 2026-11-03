# Finite-hom maximality from closed torus images

Authors: Worker 1482 (the implemented proof), Worker 1437 (the finite-hom
maximality interface and original geometric route).

`FiniteHomMaximalTorusReflectionReductionStatement.{u}` asserts that the
published proposition `TorusImageClosedTorusStatement.{u}` implies the
following result over every field `k : Type u`. Let `π : G → H` be a finite
homomorphism of actual connected reductive group schemes. Let `j : T → G`
be a closed torus, `i : S → H` a maximal torus, and `f : T → S` a homomorphism
of commutative group schemes. If `f` is surjective as a scheme morphism and
`j ≫ π = groupHom f ≫ i`, then `j` is a maximal torus. The conclusion means
maximality among all closed tori, including nonsplit tori.

The quantified conclusion is written explicitly so this module can be
published before the separate proposed `FiniteHomMaximalTorusReflectionStatement`
interface. The two conclusions have the same intended quantifiers.
`finiteHomMaximalTorusReflection_of_torusImage` proves this conditional
reduction. It does not prove the torus-image hypothesis.

For each closed torus `M` containing the given torus `T`, factor `M → H`
through a closed torus `Z`, using the explicit torus-image hypothesis. The
surjection `T → S` is schematically dominant because `S` is a torus, hence
reduced. `exists_over_factor_of_schematic_precomp` supplies `S → Z`; its
underlying scheme factor is promoted to a group homomorphism using
`SubgroupFunctor.IsRepresentedBy.factorHom`. Maximality of `S → H` makes
this homomorphism an isomorphism. Consequently `M → H` factors through
`M → S`, which is finite by the closedness of `M → G`, finiteness of `π`,
and `IsFinite.of_comp`.

The restriction `T → S` is the original `f` by cancellation of the closed
inclusion `S → H`. The inclusion `T → M` is closed because its composite
with `M → G` is closed. The accompanying `FiniteHomRigidity` helper applies
integral incomparability to these finite and schematically dominant maps,
so `T → M` is an isomorphism. This works for every torus `M`, proving the
required all-torus maximality.

The proof is an internal derived argument from the published torus-image
interface, published factorization and torus-integrality lemmas, and
Mathlib's integral incomparability. It uses no rank comparison or forward
maximality under field extension. Neither `π` nor its kernel is assumed
smooth or separable, and no torus is required to be split. Surjectivity
concerns the actual underlying scheme morphism, not rational points.
