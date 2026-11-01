# Irreducible smooth classes and their exact finite-length realization

Worker 981 defines genuine isomorphism classes of actual irreducible smooth
representations, the free integral lattice on them, and the canonical
integer-linear map

```
Langlands.SmoothRep.realizeIrreducibles k G :
  SmoothRep.IrreducibleLattice k G →ₗ[ℤ] SmoothRep.FiniteLengthGrothendieckGroup k G
```

into the published exact Grothendieck group of finite-length smooth
representations. The module imports only
`Langlands.Representation.Smooth.FiniteLengthGrothendieck` (Worker 503) and uses
its exact quotient, the free integral lattice of
`Langlands.VirtualRepresentation.Integral` (Worker 24), and the canonical smooth
category of `Langlands.Representation.Category.Basic` through their published
interfaces.

## Setting

Throughout, `k : Type uR` is a field, and `G : Type uG` is a group with an
arbitrary `TopologicalSpace G`. Representation carriers lie in an independent
universe `uV`. An actual irreducible object is an object `A` of
`SmoothRep.{uR, uG, uV} k G` together with a proof of the existing predicate
`A.IsIrreducible`. That predicate is Mathlib's `Representation.IsIrreducible` of
the underlying action: the lattice of invariant subspaces is a simple order, so
in particular `A` is nonzero. Neither admissibility nor finite dimension of the
carrier is assumed anywhere in this module. The existing `SmoothDualClass`,
which includes admissibility, is not used.

## Automatic finite length

`SmoothRep.hasFiniteLength_of_isIrreducible` proves `A.HasFiniteLength` from
`A.IsIrreducible`. The existing finite-length predicate is
`IsFiniteLength k[G] A.representation.asModule`. Mathlib's
`Representation.irreducible_iff_isSimpleModule_asModule` turns irreducibility
into simplicity of this group-algebra module. A simple module is Noetherian and
Artinian, and Mathlib's `isFiniteLength_iff_isNoetherian_isArtinian` then gives
finite length. No representation-theoretic finiteness theorem is used. The lemma
is exported for reuse.

Irreducibility is invariant under actual isomorphism.
`isIrreducible_of_equiv` transports it along an equivariant linear equivalence
`A.representation.Equiv B.representation`. It applies
`LinearMap.isSimpleModule_iff_of_bijective` to the bijective group-algebra
linear map that Mathlib's `IntertwiningMap.equivLinearMapAsModule` attaches to the
equivalence. `isIrreducible_of_iso` does the same for a categorical isomorphism
`A ≅ B` by way of the published `equivOfIso`.

## Labels

`SmoothRep.IrreducibleObject k G` is the subtype
`{A : SmoothRep.{uR, uG, uV} k G // A.IsIrreducible}` of actual irreducible
objects. `irreducibleIsoSetoid k G` relates two of these when there is an actual
categorical isomorphism `A.val ≅ B.val`. Reflexivity, symmetry and transitivity
come from the identity, the inverse and the composite isomorphism.

```
SmoothRep.IrreducibleIsoClass k G : Type (max uR uG (uV + 1))
```

is the quotient by this setoid. It is the genuine quotient construction allowed
by the task. It mirrors the published `FiniteLengthIsoClass`, which is the
quotient of `FiniteLengthObject` by the same isomorphism relation. The label of
an actual irreducible object is `irreducibleIsoClass A hA`. No representative is
chosen and no smallness or resizing is used: the label type lives in the
universe of the objects themselves, the same universe as
`FiniteLengthIsoClass k G`.

The following equality criteria are proved:

- `irreducibleIsoClass_eq_iff hA hB` says the two labels are equal if and only
  if `Nonempty (A ≅ B)` for the actual smooth objects. This is `Quotient.eq`.
- `irreducibleIsoClass_eq_iff_nonempty_equiv hA hB` states the same criterion
  with `Nonempty (A.representation.Equiv B.representation)`. It is proved with
  the published `equivOfIso` and `mkIso`.
- `irreducibleIsoClass_eq_of_iso` and `irreducibleIsoClass_eq_of_equiv` are the
  one-directional forms.

`IrreducibleIsoClass.exists_eq` proves that every label is the class of an
actual irreducible representative. `IrreducibleIsoClass.inductionOn` is the
matching induction principle for propositions.

## The forgetful map to finite-length labels

```
IrreducibleIsoClass.toFiniteLengthIsoClass :
  IrreducibleIsoClass k G → FiniteLengthIsoClass k G
```

is defined by `Quotient.lift`. It sends a representative `A` to
`finiteLengthIsoClass ⟨A, hasFiniteLength_of_isIrreducible hA⟩`. It is well
defined because `finiteLengthIsoClass_eq_iff` turns an actual isomorphism into
equality of finite-length classes. Its relationship to the existing labels is as
follows.

- `toFiniteLengthIsoClass_irreducibleIsoClass A hA hLength` says that the value
  on `irreducibleIsoClass A hA` is the existing class
  `finiteLengthIsoClass ⟨A, hLength⟩` for *any* supplied finite-length proof
  `hLength`. This holds by `rfl`, since `HasFiniteLength` is a proposition.
- `toFiniteLengthIsoClass_injective` proves injectivity. On representatives,
  equality of the finite-length classes gives an actual isomorphism by
  `finiteLengthIsoClass_eq_iff`, and `Quotient.sound` then identifies the
  irreducible labels. `toFiniteLengthIsoClass_inj` is the `iff` form.
- `exists_toFiniteLengthIsoClass_eq_iff A` describes the image: a finite-length
  label `finiteLengthIsoClass A` comes from an irreducible label exactly when
  `A.val.IsIrreducible`. This does not depend on the representative, because
  irreducibility is transported along the isomorphism given by the equality.

So `IrreducibleIsoClass k G` is identified, through an injective map with
explicitly described image, with the finite-length labels that have an
irreducible representative. It introduces no competing label system.

## The lattice and the realization

```
SmoothRep.IrreducibleLattice k G := VirtualRepresentation.IntegralLattice (IrreducibleIsoClass k G)
```

is the free integral module `IrreducibleIsoClass k G →₀ ℤ`.
`SmoothRep.realizeIrreducibles k G` is the published `extend` of the
genuine-class map

```
c ↦ FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass
```

so it is the integer-linear combination map
`Finsupp.linearCombination ℤ`. Its codomain is the published quotient
`SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uV} k G` of the free module on
finite-length classes by all actual short exact sequences, including nonsplit
ones. The following facts are proved.

- `realizeIrreducibles_generator c`: for an arbitrary label, the generator maps
  to the `ofClass` value of its forgetful finite-length label.
  `realizeIrreducibles_integralBasis` gives the same formula for the published
  `integralBasis`.
- `realizeIrreducibles_generator_irreducibleIsoClass A hA hLength`: on the
  generator indexed by an actual irreducible `A`, the value is exactly
  `FiniteLengthGrothendieckGroup.ofRepresentation A hLength`, for any
  `hLength : A.HasFiniteLength`. It holds definitionally from the arbitrary-label
  formula, because `ofRepresentation A hLength` is `ofObject ⟨A, hLength⟩`, which
  is the `ofClass` value of `finiteLengthIsoClass ⟨A, hLength⟩`.
- `realizeIrreducibles_apply` gives the finite-sum formula
  `v.sum (fun c n => n • ofClass k G c.toFiniteLengthIsoClass)`.
  `realizeIrreducibles_zero`, `_add`, `_neg`, `_sub` and `_smul` (integer
  scalars) are the elementary linear-map rules.
- `eq_realizeIrreducibles` proves uniqueness: an integer-linear map with these
  generator values on all labels equals `realizeIrreducibles`. The proof applies
  `Finsupp.lhom_ext` and writes `Finsupp.single c n` as `n • generator c`.
  `eq_realizeIrreducibles_of_irreducible` checks the hypothesis only on actual
  irreducible representatives, using `inductionOn`.
  `existsUnique_realizeIrreducibles` packages existence and uniqueness.

Neither injectivity nor surjectivity of `realizeIrreducibles` is stated or
proved here. Nor are unique Jordan–Hölder expansion, an irreducible basis of the
exact Grothendieck group, or any Aubert or analytic classification theorem. Those
belong to later statement and proof units. The injectivity proved here is only
that of the forgetful map between the two genuine isomorphism-class types.

## Universe accounting

The generic declarations have explicit universe order `.{uR, uG, uV}`.
`IrreducibleObject k G`, `IrreducibleIsoClass k G`, `IrreducibleLattice k G`
and the codomain `FiniteLengthGrothendieckGroup k G` all lie in
`Type (max uR uG (uV + 1))`. The three universes are independent and no level is
identified with another. Labels at one carrier universe are not compared with
labels at another.

## Actual GL and product-Levi specializations

Let `F : Type uF` have `[Field F]` and `[TopologicalSpace F]`, let `n : ℕ` be
arbitrary (including `0`), and let `B : GeneralLinear.BlockShape n`. The module
defines the following abbreviations. They use complex coefficients, carriers in
`Type (max uF uV)`, and the topologies supplied by the existing actual groups,
namely the matrix-unit topology on `GeneralLinear n F` and the product topology
on `B.Levi F`.

| Actual group | Labels and class | Lattice | Realization |
| --- | --- | --- | --- |
| `GeneralLinear n F` | `GeneralLinear.IrreducibleIsoClass n F`, `GeneralLinear.irreducibleIsoClass n F A hA` | `GeneralLinear.IrreducibleLattice n F` | `GeneralLinear.realizeIrreducibles n F` into `GeneralLinear.FiniteLengthGrothendieckGroup n F` |
| `B.Levi F` | `B.IrreducibleIsoClass F`, `B.irreducibleIsoClass F A hA` | `B.IrreducibleLattice F` | `B.realizeIrreducibles F` into `B.FiniteLengthGrothendieckGroup F` |

Each specialization is the generic construction at
`SmoothRep.{0, uF, max uF uV} ℂ` of the corresponding group. The codomains are
the existing `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF}` and
`BlockShape.FiniteLengthGrothendieckGroup.{uV, uF}`. Their explicit universe
order is `.{uV, uF}`, matching the existing specializations. The actual-irreducible
generator formulas
`GeneralLinear.realizeIrreducibles_generator_irreducibleIsoClass` and
`BlockShape.realizeIrreducibles_generator_irreducibleIsoClass` state that the
generator of an actual irreducible `A` maps to the existing
`finiteLengthClass n F A hLength`, respectively `B.finiteLengthClass F A hLength`,
for any finite-length proof. An irreducible product-Levi object is an arbitrary
irreducible smooth representation of the product group. No tensor-factorization
premise is imposed.

## Provenance

This construction is **derived/internal**. It does not transcribe a numbered
definition from the literature, and no literature source is cited for it. The
published exact-K0 module cites Aubert 1995 for the original finite-length smooth
context. That module records that Aubert's assertion of an irreducible basis is
not formalized, and this module neither formalizes nor uses it either. Every
definition and lemma above follows from three published or Mathlib interfaces:

1. the published exact quotient `FiniteLengthGrothendieckGroup`, its
   finite-length labels and their equality criterion;
2. the free integral lattice `IntegralLattice`, `generator`, `integralBasis` and
   `extend`;
3. Mathlib's equivalence between irreducibility and simplicity over the group
   algebra, together with its finite-length criterion for Noetherian and
   Artinian modules.

The proofs use no analytic, parabolic, Jacquet, Jordan–Hölder or classification
theorem. Admissibility is absent, and the arbitrary coefficient field, group
topology and independent universes are internal generality.

## Dependency and independence audit

The only direct project import is
`Langlands.Representation.Smooth.FiniteLengthGrothendieck`. Its import closure,
checked from the actual import lines, is

- `Langlands.Representation.Category.Basic`, which imports
  `Langlands.Representation.Smooth.Definitions` and Mathlib;
- `Langlands.Representation.Smooth.Definitions`, which imports only Mathlib;
- `Langlands.VirtualRepresentation.Integral`, which imports only Mathlib;
- `Langlands.Group.GL.Blocks`, which imports `Langlands.Group.GL.Basic` and
  Mathlib;
- `Langlands.Group.GL.Basic`, which imports only Mathlib.

No module from the excluded analytic classification, multisegment, strong-head,
quotient-coverage, tempered, square-integrable or regular-exhaustion tasks, and
none of their dependencies, is imported or used. This module does not modify the
existing exact-K0, category or lattice pairs.
