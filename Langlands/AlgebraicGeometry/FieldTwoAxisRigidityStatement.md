# Two-axis rigidity for smooth proper pointed products over fields

Worker 149 implemented this statement and checked the original sources.
Worker 337 specified the general scheme-map interface for the cube argument;
Worker 334 supplied the shared square-and-descent route.

`Langlands.AlgebraicGeometry.FieldTwoAxisRigidityStatement.{u}` is a
`Prop`-valued definition. This module states a derived rigidity result and
supplies no proof.

## Exact interface

For every field `K : Type u`, set `S = Spec (CommRingCat.of K)` and take
`Y Z P : Over S`. Each of `Y.hom` and `Z.hom` is assumed smooth, proper,
and geometrically connected. The target hypotheses are
`IsSeparated P.hom` and `LocallyOfFiniteType P.hom`. All are Mathlib's
actual scheme-morphism properties.

The pointed data are actual morphisms

```text
y₀ : Over.mk (𝟙 S) ⟶ Y
z₀ : Over.mk (𝟙 S) ⟶ Z
p₀ : Over.mk (𝟙 S) ⟶ P.
```

The defining commutativity condition in `Over` says that their underlying
scheme morphisms are sections of the respective structure morphisms.
For `T : Over S`, write `!T = Over.mkIdTerminal.from T`. Its target is
`Over.mk (𝟙 S)`, and its underlying morphism is the structure map of `T`.
Thus `!T ≫ p₀` is the constant `S`-morphism with value `p₀`.

The product `Y ⨯ Z` is the categorical product in `Over S`, hence a
scheme fibre product over `S`. With `g : Y ⨯ Z ⟶ P`, the two hypotheses are

```text
prod.lift (!Z ≫ y₀) (𝟙 Z) ≫ g = !Z ≫ p₀
prod.lift (𝟙 Y) (!Y ≫ z₀) ≫ g = !Y ≫ p₀.
```

The first lift has coordinates `(y₀,z)` and the second `(y,z₀)`.
The conclusion is `g = !(Y ⨯ Z) ≫ p₀`, an equality in `Over S`,
including the full morphisms of schemes and their structure-sheaf maps.
The field, schemes, properties, sections, map and equations are all
quantified inside the proposition; its only external parameter is `u`.

There is no group structure or assumption that the factors coincide.
There is no projectivity, perfectness, algebraic closedness or
characteristic restriction, and no properness or quasi-compactness
hypothesis on `P`. Neither geometric integrality, a global-functions
comparison, a rigidity theorem nor a descent theorem is supplied as an
additional hypothesis. Those are proof obligations.

## Original rigidity sources

The exact all-field statement here is a derived specialization, rather
than a verbatim theorem from any of these sources.

* Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
  2008 thesis, revision of March 14, 2021, Proposition 1.3.1.4,
  printed pp.69–70 (PDF pp.97–98). For locally noetherian schemes,
  connected base `B`, an open and closed `p : X → B` with a section,
  separated `q : T → B`, and canonical `O_B ≅ p_* O_X`, a `B`-map
  `f : X → T` that contracts one fibre factors through `p`.
  Corollaries 1.3.1.5–6, printed pp.70–71 (PDF pp.98–99), give
  group-scheme applications. The geometric proposition itself does not
  require a group structure.
* Lan's March 14, 2021 errata, p.8, requires openness of `p` explicitly
  and places the separatedness assumption on `q`. Flatness alone does
  not justify openness without further conditions. The revision above
  includes these corrections.
* Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third
  edition (1994), Chapter 6, Proposition 6.1, printed pp.115–116
  (PDF pp.128–129). Its proper case assumes connected base, flat `p`
  and `H⁰(X_b,O) = κ(b)` on every fibre. The chapter works with
  locally noetherian separated schemes. Corollaries 6.2–6.4,
  printed pp.116–117 (PDF pp.129–130), concern group-scheme uses;
  they are not premises of this statement.
* Edixhoven, van der Geer and Moonen, *Abelian Varieties*, retained
  preliminary draft built February 8, 2012: convention (0.4), printed
  p.1 (PDF p.5), and Chapter I, rigidity lemma (1.12), printed pp.12–13
  (PDF pp.16–17). Their varieties are separated, finite type and
  geometrically integral. The lemma treats a map `X × Y → Z` with
  complete `X` which contracts one fibre, and concludes factorization
  through `Y`. The proof uses an affine neighborhood, properness,
  and equality on a dense open subset of the integral product.
  In this retained version (1.13) defines a group homomorphism and
  (1.14) applies rigidity to a map constant on both axes. The supplied
  task's locator “printed pp.17–19” does not locate this passage in this
  version: those pages belong to Chapter II on line bundles.
  Because our `P` need not be a variety in their sense, the scheme-level
  Lan/GIT formulations supply the direct source for its permitted scope.

No project `notes/errata` file for these sources was present in the
Library used here. The author's Lan errata was read directly.

## Derivation and all-field descent

Here is the mathematical justification for the specialization. It is
not a Lean proof furnished by the statement module.

Pass from `K` to an algebraic closure `L`. The hypotheses, sections and
axis equations pull back, with the canonical product comparison
isomorphisms. Smoothness implies geometric regularity; a smooth
geometrically connected scheme over a field is geometrically integral.
Indeed, after any field extension it is locally noetherian and regular,
hence normal, and its irreducible components are disjoint open subsets;
nonempty connectedness leaves one component. This is the independent
Library statement `Langlands.AbelianScheme.SmoothGeometricIntegrality`.
It applies to both factors without a perfectness assumption on `K`.

In particular `Z_L` is proper integral over the algebraically closed
field `L`. Its ring of global functions is a finite-dimensional integral
`L`-algebra, hence a finite field extension, hence `L`. Flat base change
for global sections of this quasi-compact separated scheme gives
`O_(Y_L) ≅ p_* O_(Y_L ×_L Z_L)`, where `p` is the first projection.
It also gives `H⁰((Z_L)_{κ(y)},O) = κ(y)` for each `y ∈ Y_L`.

Apply corrected Lan Proposition 1.3.1.4 to base `B = Y_L`,
source `X = Y_L ×_L Z_L`, target `T = Y_L ×_L P_L`, and
`f = (pr₁,g_L)`. Both structure maps to `B` are first projections.
The base is connected. The map `p` is proper and smooth by base change,
so it is closed and open; it has section `e = (id,z₀)`.
The target projection `q` is separated by base change.
The source, base and target are locally noetherian since their structure
maps to the field are locally of finite type; the source and base are
in fact of finite type. Their separatedness also meets GIT's standing
scheme convention. Thus GIT Proposition 6.1 is an alternative source
for this same application, with the fibrewise global-functions
condition established above. No properness of `P_L` is needed.

The first axis equation contracts the fibre over the rational point
y₀ to `(y₀,p₀)`. Rigidity gives `f = (f ∘ e) ∘ p`, and the second
axis equation identifies `f ∘ e = (id,p₀)`. The second component yields
`g_L = p₀ ∘ (Y_L ×_L Z_L → Spec L)`.
Finally `Spec L → Spec K` is faithfully flat and quasi-compact.
Faithfulness of this base-change functor on actual scheme morphisms
reflects this equality, giving the required equality over `K`.
This descent does not assume that a field extension is separable.

## Reuse route and separate proof boundary

A formal proof may instead reuse the published proposition
`Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidity`, once its
independent exact-target proof is published. Over `L`, set
`A = Y_L ×_L Z_L`, `a = (y₀,z₀)` and `H = P_L`, and define

```text
h : A ×_L A → P_L,     h((y₁,z₁),(y₂,z₂)) = g_L(y₁,z₂).
```

Products of the smooth proper geometrically connected factors are
smooth, proper and geometrically connected. Geometric integrality
therefore makes `A ×_L A` integral. The two original axis equations
make `h` constant with value `p₀` on both axes through `a`.
The algebraically closed square theorem makes `h` constant everywhere.
Precomposing with `(y,z) ↦ ((y,z₀),(y₀,z))` recovers `g_L`, and
faithful base change descends that equality as above.
The square interface uses cartesian monoidal products, whereas this
one uses `Limits.prod`; canonical product and terminal isomorphisms
must be handled explicitly in a Lean implementation.

All those geometry, product, integrality and descent steps remain
obligations of the separate exact-target proof. This module imports
only Mathlib and neither assumes nor proves those results. Proof
assembly must use accepted published prerequisites and must not use
field or arbitrary-base pointed-group-morphism rigidity circularly.
Unreviewed assembly drafts provide guidance only.

## Retained source identifiers

* `lan-2008-pel-thesis-revision-2021`, SHA256
  `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
  PDF pp.97–99.
* `lan-2008-pel-thesis-errata-2021`, SHA256
  `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
  p.8.
* `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  GIT Chapter 6, PDF pp.128–130.
* `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
  PDF pp.5 and 16–17. PDF pp.21–23 were also checked to resolve the
  locator discrepancy.
