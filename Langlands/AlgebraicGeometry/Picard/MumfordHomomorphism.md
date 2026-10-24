# The Mumford morphism as a homomorphism of abelian schemes

`Langlands.AbelianScheme.mumfordHom` constructs the homomorphism
associated to a rigidified line bundle from an abelian scheme `A`
to `dualAbelianSchemeFromEvaluation A ...`. Its underlying scheme
morphism is the existing `mumfordSchemeMap`, which classifies the
actual rigidified Mumford family. The map itself is not supplied
as an input.

## Explicit inputs and scope

The construction works over any `S : Scheme.{u}`. It retains:

- the seven propositions used by the constructed dual group scheme:
  canonical pullback-tensor comparison invertibility, composition,
  two unit coherences, associativity, left-unitor comparison, symmetry,
  and Picard-zero stability under parameter pullback;
- the proposition `MumfordBundlePicardZeroStatement`;
- an abelian scheme `A`, a line bundle `L` rigidified at the unit,
  an ordinary inverse `M`, and evaluation `L tensor M ≅ O_A`;
- `hA : HasDualScheme A`, asserting actual universal-family existence;
- a proof of `MumfordSchemeMapHomomorphism` for these exact data;
- an ordinary inverse `MA` for the actual Poincare family and its
  evaluation;
- `geometryA : DualSchemeGeometry A hA`, asserting smoothness,
  properness, and geometrically connected fibres of the actual
  chosen parameter scheme.

The fixed homomorphism predicate contains the unit and multiplication
equations of the previously constructed map. It supplies no arbitrary
scheme morphism or group operation. Its universal validity over
quasi-separated bases is the separate proposition
`RelativeMumfordSchemeMapHomomorphismStatement`. This module consumes
a proof of the fixed predicate and does not prove that proposition.
The geometry proof likewise concerns the already chosen representing
scheme; the group operations are the ones constructed from trivial,
tensor, and inverse-family classification.

The supplied inverses and evaluations, representability, geometric
Picard-zero theorem, homomorphism equations, and dual geometry remain
explicit inputs. None of their existence theorems is proved here.
For an ordinary unrigidified bundle, the separate `LineBundle.normalize`
construction must first be applied with its own inverse and evaluation.
There is no ampleness, polarization, or isogeny assertion in this module.

## Construction and implemented properties

`mumfordCommGroupSchemeHom` first constructs a homomorphism
`A.toCommGroupScheme ⟶ dualCommGroupSchemeFromEvaluation A ...`.
It applies `Grp.homMk''` to the actual Mumford scheme morphism.
The unit obligation is precisely the first supplied equation because
the constructed target unit is the distinguished origin after the
canonical terminal comparison.

For multiplication, the target multiplication is tensor classification
after the comparison from its cartesian monoidal product to the
categorical product. The second supplied equation reduces the proof
to functoriality of product pairing and the two projection equations
for `tensorHom`. Thus the implementation checks the actual
group-object compatibility and uses no replacement multiplication.
`mumfordCommGroupSchemeHom_hom` proves by reflexivity that its
underlying map is `mumfordSchemeMap`.

`mumfordHom` reuses this group-scheme homomorphism with the source
and target abelian-scheme structures. `mumfordHom_hom` proves by
reflexivity that its underlying morphism of schemes is unchanged.

`mumfordHomPullbackIso` reuses the existing classifying isomorphism
to exhibit an actual isomorphism of rigidified line bundles between
Poincare pullback and the Mumford family.

`mumfordHom_unique` proves that any homomorphism to this constructed
dual with such a rigidified pullback isomorphism equals `mumfordHom`.
The proof uses injectivity of the additive wrapper, extensionality
of group-object homomorphisms, and the existing uniqueness of the
classifying scheme morphism. It asserts uniqueness of the
homomorphism, not uniqueness of isomorphism witnesses.

`mumfordHom_points` proves the classifying formula for every test
scheme `T/S` and every point `a : T ⟶ A.X`, including nonreduced
tests. The action of the bundled group homomorphism is definitionally
postcomposition with `mumfordSchemeMap`, so its proof is the
previously established parameter-pullback formula.

## Source and derived provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision dated March 14, 2021, Construction 1.3.2.7, printed
p.75 (PDF p.103), constructs the homomorphism associated to a
rigidified line bundle using the Mumford family and the dual universal
property. It cites Corollary 1.3.1.6, printed pp.70–71 (PDF pp.98–99),
for the homomorphism property after showing preservation of the unit.
Registered source: `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
These pages were read in the original PDF; the author's March 14, 2021
errata, registered `lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9 in this development.

This contribution is the derived formal bundling step. It keeps the
Library's parameter-first convention and the previously constructed
positive-translation classifying morphism. Its proof uses the explicit
unit and multiplication equations, not the source's rigidity proof.
No relative geometry theorem is extended beyond the source's
quasi-separatedness convention: over any other base the construction
still requires the fixed equation and geometry proofs as explicit inputs.
