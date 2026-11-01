# Bijectivity of the irreducible exact finite-length realization: statement

Author: Worker 981.

This module states, as proposition definitions, that the published canonical
integer-linear map from integral combinations of genuine irreducible smooth
classes to the exact Grothendieck group of finite-length smooth representations
is bijective. It proves no bijectivity, injectivity or surjectivity. It chooses
no inverse and introduces no multiplicity function. Its only direct import is the
published `Langlands.Representation.Smooth.IrreducibleRealization`. That module,
the exact-K0 module `Langlands.Representation.Smooth.FiniteLengthGrothendieck`,
the canonical category, and the integral lattice are used unchanged through
their published interfaces.

## The generic proposition

Let `k : Type uR` have `[Field k]` and let `G : Type uG` have `[Group G]` and an
arbitrary `[TopologicalSpace G]`. The declaration has the explicit universe
binders `.{uR, uG, uV}` in this order:

```
def Langlands.SmoothRep.IrreducibleGrothendieckStatement.{uR, uG, uV}
    (k : Type uR) [Field k] (G : Type uG) [Group G] [TopologicalSpace G] : Prop :=
  Function.Bijective (realizeIrreducibles.{uR, uG, uV} k G)
```

Its content is exactly that

```
SmoothRep.realizeIrreducibles.{uR, uG, uV} k G :
  SmoothRep.IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ]
    SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uV} k G
```

is injective and surjective. Here `Function.Bijective` is applied to the
underlying function of the published linear map. Nothing is restated or rebuilt.

- The domain is the free integral module on
  `SmoothRep.IrreducibleIsoClass.{uR, uG, uV} k G`. This is the genuine quotient
  of actual irreducible objects of `SmoothRep.{uR, uG, uV} k G` by existence of
  an actual categorical isomorphism. No representative is chosen and the label
  type is not resized.
- The map sends the generator of a label to the class, in the exact quotient, of
  any irreducible representative. It is the published `realizeIrreducibles`.
  For an actual irreducible `A` it agrees with
  `FiniteLengthGrothendieckGroup.ofRepresentation A hLength` for every
  finite-length proof `hLength`.
- The codomain is the published exact quotient. It is the free integral module
  on genuine isomorphism classes of actual smooth representations of finite
  group-algebra length, divided by the span of `[B] - [A] - [C]` for **every**
  actual short exact sequence `0 → A → B → C → 0` of finite-length smooth
  representations with carriers in `Type uV`. Exactness is the published
  `SmoothRep.IsShortExact`: injectivity, surjectivity and equality of range and
  kernel for actual intertwining maps. Nonsplit sequences are included, and no
  splitting or semisimplicity is assumed. The codomain is therefore not the
  split (direct-sum) quotient.

No hypothesis beyond the instances above is imposed. In particular there is no
admissibility premise on any representation, and no finite-dimensionality,
countability, smallness, resizing, central-character or topological-group
assumption. The topology on `G` is an arbitrary topological space structure;
smoothness of the objects is the existing condition that every vector is fixed
by an open subgroup.
Irreducible representations have finite group-algebra length automatically,
which the published `hasFiniteLength_of_isIrreducible` proves, so no length
premise is needed for the generators. All three universes are independent.
The carrier universe `uV` is quantified separately from `uR` and `uG`, and the
statement compares only labels and classes with carriers in the same
`Type uV`. Domain and codomain lie in `Type (max uR uG (uV + 1))`.

## Actual `GL_n` and product-Levi specializations

Let `F : Type uF` have `[Field F]` and `[TopologicalSpace F]`, let `n : ℕ` be
arbitrary, including `n = 0`, and let `B : GeneralLinear.BlockShape n`. The
module defines two light proposition definitions. Each has the explicit
universe binders `.{uV, uF}`, the order of the existing adapters:

```
def Langlands.GeneralLinear.IrreducibleGrothendieckStatement.{uV, uF}
    (n : ℕ) (F : Type uF) [Field F] [TopologicalSpace F] : Prop :=
  Function.Bijective (realizeIrreducibles.{uV, uF} n F)

def Langlands.GeneralLinear.BlockShape.IrreducibleGrothendieckStatement.{uV, uF}
    {n : ℕ} (F : Type uF) [Field F] [TopologicalSpace F] (B : BlockShape n) : Prop :=
  Function.Bijective (B.realizeIrreducibles.{uV, uF} F)
```

They apply `Function.Bijective` to the existing actual adapters
`GeneralLinear.realizeIrreducibles.{uV, uF} n F` and
`BlockShape.realizeIrreducibles.{uV, uF} F` of `IrreducibleRealization`. Both
use complex coefficients and carriers in `Type (max uF uV)`. They use the existing
topologies of the actual groups: the matrix-unit topology on
`GeneralLinear n F` and the product topology on `B.Levi F`. The universes `uF`
and `uV` are independent. An irreducible object of the product Levi is an
arbitrary irreducible smooth representation of the product group. No
tensor factorization of irreducibles into block factors is assumed.

The relation to the generic proposition is exposed by two proved theorems in
each namespace. Neither asserts that any of these propositions is true.

- `GeneralLinear.irreducibleGrothendieckStatement_iff n F` proves
  `IrreducibleGrothendieckStatement.{uV, uF} n F ↔
  SmoothRep.IrreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (GeneralLinear n F)`.
  `GeneralLinear.IrreducibleGrothendieckStatement.of_smoothRep` is its direct
  specialization direction: the generic proposition at `ℂ` and
  `GeneralLinear n F` implies the `GL_n` proposition.
- `GeneralLinear.BlockShape.irreducibleGrothendieckStatement_iff F B` and
  `GeneralLinear.BlockShape.IrreducibleGrothendieckStatement.of_smoothRep` are
  the same two facts for `B.Levi F`.

Both proofs are definitional (`Iff.rfl`, respectively the hypothesis itself).
The adapters are abbreviations of the generic map at
`SmoothRep.{0, uF, max uF uV} ℂ` of the actual group.

## The intended theorem and its internal Jordan–Hölder provenance

The proposition expresses the ordinary comparison between the exact
Grothendieck group of a length category and the free abelian group on its
simple objects. The following three sentences describe the intended theorem.
They are not a proof implemented, assumed or used by this statement unit.

- **Generation.** Every finite-length smooth representation has a composition
  series whose graded quotients are irreducible smooth representations.
  Short exact additivity then writes its exact class as the sum of the classes
  of those factors, which gives surjectivity.
- **Well-defined multiplicities.** By the Jordan–Hölder theorem, the number of
  factors isomorphic to a given irreducible is independent of the chosen series.
- **Descent.** Multiplicities are additive along actual short exact sequences.
  They therefore descend through the exact relations to a left inverse of the
  realization, which gives injectivity.

This identification is **derived/internal**. The published generic input
`Langlands.Representation.Filtration.MultiplicityAdditivityProof` (Worker 430)
supplies witness-based composition-series existence, independence, transport and
short exact multiplicity additivity for actual representations. It is a potential
input to a later proof. It is not imported here and does not by itself compare
the smooth exact quotient with the irreducible lattice. This focused target
does not demand a total multiplicity function, a chosen inverse or a coefficient
theorem. The proof is a separate successor task.

## Source correspondence

In the original finite-length smooth context, Anne-Marie Aubert, *Dualité dans
le groupe de Grothendieck de la catégorie des représentations lisses de longueur
finie d'un groupe réductif p-adique*, Trans. Amer. Math. Soc. **347** (1995),
2179–2189, printed p. 2180 (PDF p. 2), writes: "Soient … Irr(G) l'ensemble des
classes d'équivalence de G-modules irréductibles et R(G) le groupe de
Grothendieck des G-modules de longueur finie; R(G) est un groupe abélien libre
de base Irr(G)." There G is a p-adic reductive group and the G-modules are smooth
representations on complex vector spaces. Aubert gives this assertion without
proof. The present proposition is its formulation for the published objects:
`Irr(G)` is the genuine label type `IrreducibleIsoClass`, `R(G)` is the exact
quotient `FiniteLengthGrothendieckGroup`, and "free abelian with basis `Irr(G)`"
is bijectivity of the canonical map from the free integral lattice.

- Literature ID: `aubert-1995-duality`.
- Original SHA-256: `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`
  (verified for this unit).

The arbitrary coefficient field, arbitrary group and topology, independent
carrier universe and the actual `GL_n` and Levi specializations are internal
generality. This statement does not use the irreducibility and duality claims
of Aubert's later sections, whose proofs have the issues recorded in the
literature index and in `notes/henniart/aubert-duality-route.md`.

## Dependency and independence audit

The only direct import is `Langlands.Representation.Smooth.IrreducibleRealization`.
Its project import closure, checked from the actual import lines, is

- `Langlands.Representation.Smooth.FiniteLengthGrothendieck`;
- `Langlands.Representation.Category.Basic`, which imports
  `Langlands.Representation.Smooth.Definitions` and Mathlib;
- `Langlands.Representation.Smooth.Definitions`, which imports only Mathlib;
- `Langlands.VirtualRepresentation.Integral`, which imports only Mathlib;
- `Langlands.Group.GL.Blocks`, which imports `Langlands.Group.GL.Basic` and
  Mathlib;
- `Langlands.Group.GL.Basic`, which imports only Mathlib.

No filtration, Jordan–Hölder, parabolic induction, Jacquet, Aubert-operator or
analytic module is imported. No module or result from the excluded tasks, their
proof successors or their dependencies is imported or used. These are analytic
segment classification `aca8805b-054f-4d56-8045-12db7f623404`, special-head
multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered
strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`. The existing realization, category,
exact-K0, lattice and filtration pairs are not modified.

## Development validation

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
module with no errors or warnings (diagnostic
`07005bef-1a15-4473-badd-f133b7623597`). It reported
`SmoothRep.IrreducibleGrothendieckStatement` as a `Prop`-valued definition with
level parameters `uR, uG, uV`. Separate inspections reported the `GL_n` and
product-Levi propositions as `Prop`-valued definitions with level parameters
`uV, uF` (diagnostics `c03582ee-88ce-41b7-864d-a1d88adf846e` and
`226b0858-6741-4c67-a25a-b76eea7e9335`). Only `propext`, `Classical.choice` and
`Quot.sound` were reported as assumptions. These are development checks.
Independent semantic acceptance and Library publication are separate.
