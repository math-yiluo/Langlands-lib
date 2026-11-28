# Transport of the ℓ-adic predicates on finite-dimensional representations

Module `Langlands.Correspondence.HenniartLadicTransport` treats Laumon's two conditions on
finite-dimensional representations over `E = PadicAlgCl ℓ`, an algebraic closure of `ℚ_ℓ`
(Laumon 1987, (2.1.2), p. 152). In `Langlands.Correspondence.HenniartLadicClasses`,
`Langlands.Henniart.LocalNumerical.IsLadicContinuous` requires continuity into the endomorphisms
with their module topology. `Langlands.Henniart.LocalNumerical.IsLadicDefinedOverFiniteExtension`
requires a basis in which all matrix entries lie in a single finite extension of `ℚ_ℓ`.

## Matrix coefficients

- `ofCoefficients ℓ b` is the `E`-linear map sending a family `c : Fin n → Fin n → E` to the
  endomorphism `∑ i j, c i j • (b.coord j).smulRight (b i)`, whose matrix in the basis `b` is `c`.
  `ofCoefficients_repr` recovers an endomorphism from its matrix entries `b.repr (f (b j)) i`.
- `continuous_moduleTopology_iff` characterizes continuity of a map `ρ` from a topological
  space to `Module.End E V`, with `V` finite-dimensional. For the module topology on
  `Module.End E V`, continuity holds exactly when
  every coefficient `x ↦ φ (ρ x v)` (`φ` a linear form, `v` a vector) is continuous. One
  direction composes with the linear map `f ↦ φ (f v)`, continuous on the module topology
  (Mathlib's `IsModuleTopology.continuous_of_linearMap`). For the other, `ρ` is `ofCoefficients`
  applied to its matrix entries in `Module.finBasis`. The entries are coefficients, and
  `ofCoefficients` is a linear map from a finite product of copies of `E`, which carries the
  module topology (Mathlib's `IsModuleTopology.instPi`).
- `isLadicContinuous_iff` is this criterion for `IsLadicContinuous`.

## Invariance under equivalences

- `IsLadicContinuous.of_equiv` transports continuity along a representation equivalence
  `e : FiniteRepresentation.Equiv A B` between carriers in arbitrary universes.
  The coefficient `g ↦ φ (B g w)` is the coefficient
  `g ↦ (φ ∘ e) (A g (e⁻¹ w))`.
- For `IsLadicDefinedOverFiniteExtension.of_equiv`, the image under `e` of a good basis of `A`,
  reindexed along `Module.finrank E A = Module.finrank E B`, is a good basis of `B` with the same
  matrix entries and the same finite extension.
- `isIrreducible_of_equiv` transports irreducibility by weil-conjectures's
  `Representation.Equiv.isIrreducible_iff`.

## Finite models and change of universe

- `IsLadicContinuous.isLadicDefinedOverFiniteExtension` gives a finite extension of `ℚ_ℓ` over
  which a continuous finite-dimensional representation of a compact topological group is defined.
  Its matrices in `Module.finBasis` form a homomorphism to matrices with continuous entries, and
  weil-conjectures's `PadicAlgCl.exists_finiteDimensional_forall_mem` (a Baire category argument
  in `WeilConjectures.RepresentationTheory.IntegralModel`) puts all entries in one finite
  extension.
- `exists_finiteRepresentation_equiv` gives every `A : FiniteRepresentation.{0, uG, uV} E G` an
  equivalent representation `B : FiniteRepresentation.{0, uG, uW} E G` in any prescribed carrier
  universe `uW`. `B` is the transported representation on `ULift (Fin n → E)`, `n` the rank, and
  the equivalence is a basis isomorphism followed by `ULift.moduleEquiv`.

All declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
