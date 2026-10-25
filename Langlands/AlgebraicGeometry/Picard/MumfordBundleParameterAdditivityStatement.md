# Parameter additivity of the actual relative Mumford family

`Langlands.AbelianScheme.MumfordBundleParameterAdditivityStatement`
states the relative theorem-of-the-cube consequence for the existing
parameter-first normalized Mumford family. It is a `Prop`-valued
definition. Its proof is a separate obligation.

## Exact identity and inputs

The statement quantifies, in every universe `u`:

- `preservation : pullbackTensorComparisonIsIsoStatement.{u}`;
- a scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S`;
- an actual abelian scheme `A/S`;
- `L : RigidifiedLineBundle (unitSection A)`;
- an ordinary inverse `M : LineBundle A.X.left` and an actual evaluation
  `tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left`.

Here `preservation` asserts invertibility of the canonical
pullback-tensor comparison maps. The inverse and evaluation remain
explicit inputs. The existing construction supplies the rigidifications.

Let `Λ = mumfordBundle A preservation L M evaluation`, let `q` be its
class in `RigidifiedClasses A A.X`, and put `T = A.X ⊗ A.X` in `Over S`.
The asserted equality in `RigidifiedClasses A T` is

`classesPullback μ[A.X] q =
  classesTensor preservation T
    (classesPullback π1 q) (classesPullback π2 q)`,

with the common arguments `A.X.hom`, `unitSection A` and
`unitSection_comp A` supplied explicitly in Lean.
The maps are the actual multiplication `μ[A.X]` and projections
`CartesianMonoidalCategory.fst A.X A.X` and
`CartesianMonoidalCategory.snd A.X A.X`.
The tensor product here is the chosen cartesian monoidal product in
`Over S`; the family construction itself uses the chosen scheme
pullback defining `mumfordProduct A`. The existing relative pullback
construction handles these choices.

`classesPullback` is induced by the actual functor
`RigidifiedLineBundle.relativePullback`, and `classesTensor` is induced
by the actual rigidified tensor product. The quotient identifies two
families precisely when there exists an isomorphism respecting their
rigidifications. Equivalently, the identity asks for a compatible
isomorphism between the multiplication pullback of `Λ` and the tensor
of its two projection pullbacks over `T`.

The equation is imposed on the full families over `T`. Pullback along
any test-scheme morphism into `T` retains this equality, including for
nonreduced test schemes and infinitesimal parameters.
Picard-zero membership, representability, a chosen dual scheme and
geometric rigidity are not premises of this statement. Any use of those
results in a later proof must establish the needed hypotheses.

## Normalization and the cube interpretation

The fixed family is over the first factor of `A ×_S A`, with section
`(id,e)`. Its underlying line bundle is

`(m*L tensor p1*M) tensor p2*M`.

On the threefold product, write `x,y` for the two parameters and `z`
for the family coordinate. The left side restricts this expression
along `(x,y,z) ↦ (x+y,z)`. The right side tensors its restrictions
along `(x,y,z) ↦ (x,z)` and `(x,y,z) ↦ (y,z)`.
Using the supplied inverse evaluation, their difference is the usual
alternating cube expression for `L`. The rigidification of `L` along
the unit removes the constant unit-restriction factor. This explains
the relative theorem-of-the-cube provenance of the requested identity.
A proof must also obtain compatibility with the specified
rigidifications; an ordinary isomorphism alone does not directly
give an isomorphism in the quotient used here.

## Original source and derived provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The following original passages were read:

- Construction 1.3.2.7, printed p.75/PDF p.103, defines
  `D₂(L) = m*L tensor pr1*L⁻¹ tensor pr2*L⁻¹`, rigidifies it
  along `(e,id)` with the second factor as parameter, and obtains a
  unit-preserving classifying morphism `λ_L : A → A∨`. It states
  that this morphism is a homomorphism by Corollary 1.3.1.6.
- Corollary 1.3.1.6 and its proof, printed pp.70–71/PDF pp.98–99,
  give the homomorphism property for a unit-preserving morphism from
  an abelian scheme to a separated group scheme of finite presentation.
- Theorem 1.3.2.3, printed p.74/PDF p.102, represents the rigidified
  Picard functor and its fibrewise algebraically trivial subfunctor;
  the latter is represented by the dual abelian scheme. Its identity
  corresponds to the trivial invertible sheaf.
- The convention on printed p.xxvi/PDF p.26 takes schemes to be
  quasi-separated preschemes. The Lean statement retains the
  quasi-separated base hypothesis.

The statement here is a derived family formulation of this source
route. By universal classification, the equation
`λ_L(x+y) = λ_L(x) + λ_L(y)` gives the displayed equality of
rigidified classes, since addition on the represented Picard functor
is tensor product. This reasoning applies at the parameter scheme
`T = A.X ⊗ A.X`, so it retains the full family information.
Lan does not state this exact compatible-isomorphism quotient equation
or present a direct relative cube proof in the cited construction.
No separate relative cube theorem is being attributed to that passage.

There are two comparisons to make in a proof using Lan's route.
First, the Library takes the first factor as parameter. Exchanging
the two factors in Lan's family preserves addition by commutativity
of the abelian scheme and interchanges the two inverse factors,
which tensor symmetry reorders. The supplied `M` and evaluation
identify those factors with the source's inverse bundles. The
specified rigidifications must be compared as well.
Second, a proof through dual classification must justify membership
of this family in the represented Picard-zero functor and obtain
the separatedness and finite presentation needed for the rigidity
corollary. Lan uses fibrewise algebraic equivalence to zero; a proof
using the Library's geometric translation-invariance interface must
justify that comparison. These are proof obligations, not implicit
inputs to this proposition.

The author's March 14, 2021 errata are registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`.
PDF pp.1 and 8–9 were checked. They replace the separated-scheme
convention by quasi-separatedness, restrict the separatedness
assumption in Proposition 1.3.1.4 to its target morphism, and add
openness of its source morphism. The revised text is used here.
This statement module supplies no proof of those geometric results
or of the asserted family identity.
