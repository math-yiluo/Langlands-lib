# Galois lattices and their continuous Galois representations

This internal construction passes from Galois actions on finite free
modules over a coefficient ring `O` to the continuous Galois
representations `Langlands.GaloisRepresentation.Objects`. Let `O → L` be an
algebra from a commutative ring to a topological field. Let `V` be an action
of `Gal(K̄/K)` on a finite free `O`-module, a Galois lattice. Extending
scalars gives a Galois action on the finite-dimensional `L`-vector space
`L ⊗[O] V`. If the matrix coefficients `g ↦ f(g · x)` of the lattice are
continuous with values in `L`, this action is continuous for the module
topology on its endomorphisms. It is then an object of `Objects K L`. At a
finite place of a number field `K` where the lattice is unramified, its
Euler polynomial is the image in `L[X]` of the Frobenius Euler polynomial of
the lattice. The declarations are in namespace
`Langlands.Shimura.LatticeGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5 on printed p. 313, considers `λ`-adic representations of the
Galois group, with local factors (5.6) built from Frobenius eigenvalues.
Such representations arise by inverting the residue characteristic in an
integral `λ`-adic cohomology module, a Galois lattice. This module provides
the passage from a lattice to a continuous representation over a field,
together with the comparison of Euler polynomials.

Continuity of the matrix coefficients, freeness and finiteness of the
lattice, and unramifiedness are hypotheses. The module proves no continuity
of any particular lattice. It does not compare different lattices in the
same representation, and no statement of Harris is formalized.

## Inputs

- From the published `Langlands.GaloisRepresentation`
  (`Langlands/Galois/CoefficientRepresentation.lean` and
  `CompatibleFamily.lean`): `IsContinuous` (continuity for the module
  topology on `Module.End L A`), `Objects K L`, `HasEulerPolynomialAt` and
  `hasEulerPolynomialAt_iff`, `chosenClosureEmbedding` and
  `geometricFrobeniusLift`.
- From `Langlands.Shimura.ContinuousGaloisAction` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `finiteRepresentation M`, the action as a finite-dimensional
  representation. From `Langlands.Shimura.FrobeniusPolynomial` (same
  candidate): `frobeniusEulerPolynomial` and
  `frobeniusEulerPolynomial_eq_along`.
- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `IsUnramifiedAt`, `IsUnramifiedAlong`, `localRestriction`.
- From Mathlib: `LinearMap.baseChange` (with `baseChange_id`,
  `baseChange_comp`, `baseChange_tmul`), `Algebra.TensorProduct.basis`
  (with `basis_apply`, `basis_repr_tmul`), `LinearMap.toMatrix`,
  `LinearMap.charpoly_baseChange`, `LinearMap.charpoly_monic`,
  `Polynomial.reflect_map`, `Module.finrank_baseChange`, and the module
  topology API (`moduleTopology`, `IsModuleTopology`,
  `IsModuleTopology.continuous_of_linearMap`).

## Continuous finite-dimensional Galois actions

Let `K` and `L` be fields, `L` with a topology, and
`M : Action (ModuleCat L) (Field.absoluteGaloisGroup K)` with `M.V`
finite-dimensional.

- `ofContinuous M hM`: for a proof `hM` that `finiteRepresentation M` is
  continuous, the object `⟨finiteRepresentation M, hM⟩` of `Objects K L`
  (`ofContinuous_val`). Unlike `ContinuousGaloisAction.toObjects`, it does
  not require smoothness.
- `hasEulerPolynomialAt_ofContinuous_iff`: for a number field `K` and a
  finite place `v`, `ofContinuous M hM` has Euler polynomial `P` at `v` if
  and only if `M` is unramified at `v` and its
  `FrobeniusPolynomial.frobeniusEulerPolynomial v` is `P`.

## Extension of scalars of a Galois lattice

Let `O` be a commutative ring with an `O`-algebra `L`, and
`V : Action (ModuleCat O) (Field.absoluteGaloisGroup K)`.

- `baseChangeAction V : Action (ModuleCat L) (Field.absoluteGaloisGroup K)`
  has space `L ⊗[O] V`, and `g` acts by `(V.ρ g).hom.baseChange L`
  (`baseChangeAction_ρ_hom`). Instances record that it is finite or free
  over `L` when `V` is finite or free over `O`.
- `IsLatticeContinuous V`: for a topology on `L`, every map
  `g ↦ algebraMap O L (f ((V.ρ g).hom x))`, for an `O`-linear form `f` and a
  vector `x` of `V`, is continuous.
- `isUnramifiedAlong_baseChange V hu`: if `V` is unramified at `v` along `ι`,
  so is `baseChangeAction V`.
- `frobeniusEulerPolynomial_baseChange V v`: for `V` finite free, the
  Frobenius Euler polynomial of `baseChangeAction V` at `v` is the image
  under `algebraMap O L` of that of `V`.

Assume now that `L` is a topological ring and `V` is finite free over `O`.

- `isContinuous_baseChange V hV`: if `IsLatticeContinuous V`, then
  `finiteRepresentation (baseChangeAction V)` is continuous.
- `latticeObjects V hV : Objects K L` is `ofContinuous` of
  `baseChangeAction V`.
- `latticeObjects_rank`: for nontrivial `O`, its rank is
  `Module.finrank O V.V`.
- `hasEulerPolynomialAt_latticeObjects V hV v hu`: if `V` is unramified at
  `v`, `latticeObjects V hV` has as Euler polynomial at `v` the image under
  `algebraMap O L` of `FrobeniusPolynomial.frobeniusEulerPolynomial v V`.

## Proof outline

The group laws of `baseChangeAction` are `baseChange_id` and
`baseChange_comp`. For continuity, choose a basis `b` of `V` and the induced
basis `1 ⊗ b` of `L ⊗[O] V`. The matrix of the action of `g` in this basis
has entries `algebraMap O L (b.coord i (g · b_j))`, which are continuous by
hypothesis. On the endomorphisms with their module topology, the inverse of
`LinearMap.toMatrix` is a linear map from a space of matrices with its
product topology, which is a module topology, hence it is continuous. The
action is the composite of these two maps. For the Euler polynomial, the
geometric Frobenius endomorphism of the extension of scalars is the
extension of scalars of that of `V`. Its characteristic polynomial is the
image of that of `V` (`charpoly_baseChange`). Reversal commutes with the map
because the characteristic polynomial is monic, so its degree is preserved.
Unramifiedness passes because the extension of scalars of the identity is
the identity.

## Provenance

This is an internal construction connecting Galois actions on modules with
the published continuous Galois representations of
`Langlands.GaloisRepresentation`, using Mathlib's extension of scalars,
matrices and module topologies. Harris (1999), §5 and formula (5.6) on
printed p. 313, is motivation only.
