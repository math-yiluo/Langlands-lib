# Smooth-family universal pairs from universal Picard-zero families

Author: Worker 3233.

Module `Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal`.
Written for the finite-type existence task `90a7704e-771a-4107-a91a-c67873dd035e`
(Task 3233), whose exact target is
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`.
This module is part of that target's final assembly. It proves two conditional
theorems over an arbitrary base scheme and adds no axioms. It does not prove the
target, any existence of a dual, or the smooth-family comparison.

## Declarations

All declarations are in namespace `Langlands.AbelianScheme`, for
`S : Scheme.{u}` and `A : AbelianScheme S`.

### `isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero`

```lean
theorem isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u}) {P : Over S}
    {L : RigidifiedFamily A P} (hL : IsUniversalPicardZero A L) :
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L
```

The hypothesis `comparison` is the published aggregate
`SmoothFamilyPicardZeroComparisonStatement`. It is an explicit premise here, not
an axiom. This module imports only the statement. The Library proves it as
`smoothFamilyPicardZeroComparison` (module
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof`), and
the finite-type assembly supplies that proof. The hypothesis `hL` is the published all-test universal property
`IsUniversalPicardZero A L` of an actual rigidified family `L` on an arbitrary
parameter `P : Over S`.

Proof. The first conjunct of the target predicate is
`IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`; it is obtained from the
first conjunct `IsPicardZeroFamily A L` of `hL` by the family lift of the
comparison (its third conjunct, used right to left). For the second conjunct,
let `T : Over S` be a quasi-separated test and `q` a rigidified class on `T`
satisfying `IsAlgebraicallyTrivialClassViaSmoothFamily`. The class lift of the
comparison (its fourth conjunct, used left to right) shows that `q.val` is a
geometric Picard-zero class, so `⟨q.val, _⟩ : PicardZeroClasses A T`. The
second conjunct of `hL`, which holds on every test scheme and in particular on
the quasi-separated `T`, gives exactly one slice morphism `h : T ⟶ P` whose
actual rigidified pullback class `RigidifiedLineBundle.classifyingMap ... L T h`
equals `q.val`. This is literally the required unique existence. Uniqueness is
inherited unchanged; quasi-separatedness of `T` is not used.

### `exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme`

```lean
theorem exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u})
    (hA : HasDualScheme A) (geometry : DualSchemeGeometry A hA) :
    ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L
```

Besides `comparison`, the premises are the published existence predicate
`HasDualScheme A` (an actual parameter with an actual universal geometric
Picard-zero family) and the published geometry predicate
`DualSchemeGeometry A hA` (smoothness, properness and geometric connectedness
of the chosen parameter `dualScheme A hA`). Neither is asserted to hold.

Proof. The Library line bundle `LineBundle.exists_tensorObj_iso_structureSheaf`
supplies an actual line bundle `M` on `dualScheme A hA ×_S A` with a tensor
evaluation isomorphism from the carrier of the chosen Poincaré family
`poincareFamily A hA` and `M` to the structure sheaf. With it, the existing
construction `dualAbelianSchemeFromEvaluation` gives an actual
`B : AbelianScheme S` whose underlying object is definitionally
`dualScheme A hA`, whose commutative group structure is the published one
constructed from Poincaré classification, and whose smoothness, properness and
geometric connectedness are the three components of `geometry`. The remaining
inputs of that construction are the published unconditional theorems
`pullbackTensorComparisonIsIso`, `picardZeroPullback`,
`pullbackTensorComposition`, `pullbackTensorUnitCoherence`,
`explicitPullbackTensorAssociativity`, `tensorMonoidalLeftUnitorComparison`
and `pullbackTensorSymmetry`. The family is `L := poincareFamily A hA`, an
actual rigidified family on `B.X`. Its universal property
`poincareFamily_universal A hA` and the first theorem give
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`.

## Role in the finite-type assembly

The exact target of task `90a7704e-771a-4107-a91a-c67873dd035e` quantifies over
commutative rings `R` of finite type over `ℤ` and abelian schemes over
`Spec R`. By the second theorem, that target follows from the published
comparison proof `smoothFamilyPicardZeroComparison` together with, for each
such `A`, a proof `hA` of `HasDualScheme A` and a proof of
`DualSchemeGeometry A hA`. Those two inputs over finite-type bases are the
remaining existence and geometry obligations of the task. They are not proved
here. The companion module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly`
derives them from the premises `FiniteTypeAbelianPicardSheafSchemeStatement`
and `FiniteTypeDualSchemeGeometryStatement`. The relative statements
`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement` are not used, because their current
proof routes depend on the general-base representer, which consumes this task.

The Library's smooth-family condition is an explicit geometric-fibre witness
condition; its relation to translation invariance is exactly the premise
`comparison`, and its relation to the sources' algebraic equivalence on
ordinary fibres is not asserted.
