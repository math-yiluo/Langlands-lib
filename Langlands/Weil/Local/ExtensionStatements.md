# Restriction and induction statements along an extension of p-adic fields

Author: Worker 25. This is a statement contribution: every declaration is a
`Prop`-valued definition, and nothing here is proved. Proofs belong to separate
tasks.

Fix a prime `p` and p-adic fields `F : PadicField.{u} p` and `E : PadicField.{v} p`.
Fix also an algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`, the
abstract form of a finite extension `E/F`. Write `ι = extensionWeilMap F E f`
for Worker 53's published map `W_E → W_F` of actual local Weil groups. It is an
injective open embedding whose image has index `[E : F]`. It satisfies
`localDegreeInt F (ι w) = f_{E/F} · localDegreeInt E w`, where
`f_{E/F} = extensionResidueDegree F E f` is the residue degree, and
`localNormCharacter F ∘ ι = localNormCharacter E`.

The restriction and induction constructors are Worker 17's published
`Langlands.Weil.Local.ExtensionParameters`:
- `extensionRestrict F E f`: restriction of representations from `W_F` to `W_E`.
- `extensionWDRestrict F E f`: restriction of pairs, with the same carrier and
  monodromy and the norm restated as that of `E`.
- `extensionInduce F E f`: induction of representations from `W_E` to `W_F`,
  along the range of `ι`.
- `extensionWDInduce F E f`: induction of pairs, with weighted monodromy
  `N(φ)(g) = ‖g‖ N(φ(g))`.

That module proves the rank formulas and some preservation results. This file
states the remaining compatibilities, including the reflection directions.
Proved directions are kept so that each clause is a complete equivalence; they
are listed under "Already proved directions" below.

`Langlands.Weil.Local.LocalExtensionStatements.{u,v,w,w'}` quantifies over
every prime, both fields and every embedding `f`. The field universes `u`, `v`
and the two carrier universes `w`, `w'` are independent.

## Declaration and source map

Every declaration is in the namespace `Langlands.Weil.Local`. Each `For` target
takes the actual `F`, `E` and `f`.

| Declaration | Exact content | Source and derivation |
| --- | --- | --- |
| `LocalExtensionRestrictionFor` | For every `A : LocalWeilRepresentation.{u,w} F`, restriction to `W_E` preserves and reflects four properties: usual continuity (`IsContinuous`); open kernel on actual inertia (`localInertia E` against `localInertia F`); finite image; and semisimplicity. | Tate (2.1): `res_{E/F}` with `W_E` a closed subgroup of finite index. Derived. Continuity is reflected because `ι` is an open embedding, so `A` is continuous on an open subgroup and hence everywhere. Open inertia kernel is reflected because `ι` is open and `localInertia E = ι⁻¹(localInertia F)`. Finite image is reflected because the index is finite. Semisimplicity in both directions is the characteristic-zero finite-index averaging argument, as in the generic `RepresentationInductionFiniteness`. |
| `LocalExtensionInductionFor` | For every `B : LocalWeilRepresentation.{v,w} E`, induction to `W_F` preserves and reflects the same four properties, each with its own inertia. | Tate (2.1): `ind_{E/F}`. Derived. Reflection uses the unit embedding of `B` into the restriction of its induction, as an invariant subspace. Preservation of finite image uses the normal core of the image of `ker B`. Semisimplicity is as in `RepresentationInductionFiniteness`. The continuity clause is the local form of `RepresentationInductionTopology`. |
| `LocalExtensionParameterFor` | Restriction and induction of pairs preserve and reflect `IsLocalFrobeniusSemisimpleParameter`: open inertia kernel together with semisimplicity of every element of nonzero geometric degree, on each side with its own inertia and degree. Monodromy is arbitrary. | Tate 4.1.2–4.1.3, with the degrees related by `f_{E/F}`. Derived. Reflection under restriction: some power `g^k` lies in the image of `ι` with nonzero `E`-degree, and over `ℂ` an invertible operator with a semisimple power is semisimple. Induction: the same power argument on the normal core, where the induced operator is block diagonal with conjugate blocks. The converse uses the unit summand. |
| `LocalExtensionSemisimplificationFor` | If `A'` is an actual Frobenius semisimplification of `A` for `localDegree F` (`Frobenius.IsSemisimplification`), then the restriction of `A'` is one of the restriction of `A` for `localDegree E`. If `B'` is one of `B` for `localDegree E`, then the induction of `B'` is one of the induction of `B` for `localDegree F`. Carrier universes may differ. | Tate 4.1.3 and Deligne 8.5–8.6. Derived. For restriction, the correction of the restricted pair is `u^{f_{E/F}}`. For induction, the correction is the pointwise action of the unipotent `f_{E/F}`-th root of the correction of `B`. The identification sends `[g ⊗ x]` to `[g ⊗ v^{deg g} x]`. This is the actual-field form of the generic `RestrictionSemisimplificationCompatibility`, `InductionSemisimplificationCompatibility` and `SemisimplificationDegreeRescaling`. |
| `LocalExtensionReciprocityFor` | For every `B`, there is an actual intertwiner `η : B → Res(Ind B)` such that every intertwiner `B → Res A` factors uniquely as `Φ ∘ η` with `Φ : Ind B → A`. There is also an actual intertwiner `ε : Res(Ind B) → B` such that every intertwiner `Res A → B` factors uniquely as `ε ∘ Φ` with `Φ : A → Ind B`. This holds for every `A : LocalWeilRepresentation.{u,w'} F`. | Tate (2.1) ("the usual Frobenius reciprocity"). For finite index, induction is both left and right adjoint to restriction. The unit is `x ↦ [1 ⊗ x]`, as in the generic `RepresentationInductionReciprocity`. The counit is projection onto the identity coset. |
| `LocalExtensionOperationsFor` | Induction commutes with direct sums (`sum`) and with full duals (`dual`). It carries the twist by `χ ∘ ι` to the twist by `χ`, for every character `χ` of `W_F`. It satisfies the projection formula `Ind(B ⊗ Res A) ≅ Ind B ⊗ A`. Each is a genuine `FiniteRepresentation.Equiv`. | Derived finite-index facts. Actual-field form of the generic `RepresentationInductionCompatibility`. |
| `LocalExtensionStatements` | Conjunction of all preceding families for every prime, both fields and every `f`, at universes `u v w w'`. | Complete interface. No conjunct is an assumed construction field. |

### Already proved directions

These are published theorems or constructors in the Library and are restated
only as one direction of an equivalence:
- `isContinuous_extensionRestrict`: restriction preserves continuity.
- `extensionOpenInertiaRestrict`, through `hasOpenInertiaKernel_restrict` in
  `WeilDeligne.ParameterRestriction`: restriction preserves open inertia kernel.
- `extensionOpenInertiaInduce`, through `hasOpenInertiaKernel_induceAlong`:
  induction preserves open inertia kernel.
- `isLocalFrobeniusSemisimpleParameter_extensionWDRestrict`: restriction
  preserves Frobenius-semisimple parameters.

The rank formulas `rank_extensionInduce` and `rank_extensionWDInduce` and the
unramified-character formula `localUnramifiedCharacter_extensionWeilMap` are
proved and are not restated.

## Not stated here

- **Transitivity in towers** `F ⊂ E ⊂ K` is not stated. The published
  `extensionWeilMap` of a composite embedding is not identified with the
  composite of the two maps. Such an identification holds at best up to
  conjugation in the absolute Galois group, so the comparison needs a separate
  construction.
- **The determinant of an induced representation** is not stated. Its
  transfer formula needs the reciprocity map.
- **The Mackey irreducibility criterion** is not stated.

## Original sources

The originals were read by Worker 25, and the locators were verified on 2026-10-20.

- `tate-1979-number-theoretic-background`: J. Tate, *Number theoretic
  background*, Proc. Sympos. Pure Math. 33, Part II (1979), retained Corvallis
  `Part II.pdf`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`; printed
  page `p` is PDF page `p+9`. The relevant parts are:
  - (2.1), printed pages 9–10 (PDF 18–19): for a finite separable `E/F`, the
    canonical `res_{E/F}` and `ind_{E/F}` "satisfying the usual Frobenius
    reciprocity, for we can identify `W_E` with a closed subgroup of finite
    index in `W_F`".
  - (1.4.6), printed page 7 (PDF 16): the norm.
  - 4.1.2–4.1.3, printed page 20 (PDF 29): pairs with open inertia kernel and
    Φ-semisimplicity, where `exp(aN) ρ(w) u^{-v(w)}` is semisimple for all `a`
    and all `w` with `v(w) ≠ 0`.
- `deligne-1973-local-constants`: P. Deligne, *Les constantes des équations
  fonctionnelles des fonctions L* (1973), retained PDF SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  8.5–8.6, internal/PDF page 70: the unipotent part of Frobenius and
  F-semisimplification.

Neither source states the conjunction verbatim. The reflection directions,
the residue-degree rescaling of the correction and the explicit unit and counit
are derived, as recorded in the table.

## Lean dependency map

All imports are Lean modules of the current Library (commit
`c4076e8f9e0c741ca14fc16ba1cd82671b9de609`); no artifact identity is imported.
The direct imports are `Langlands.Weil.Local.ExtensionParameters`,
`Langlands.Weil.Representation.{Dual,SumsTensor,Twist}` and
`Langlands.WeilDeligne.FrobeniusStatements`.

| Module | Declarations used here | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.Weil.Local.ExtensionParameters` | `extensionRestrict`, `extensionInduce`, `extensionWDRestrict`, `extensionWDInduce` | `00f661576a88cfee9dc69305a1ad3d1aec40cd51dd8fedbca65517571613c4c4` |
| `Langlands.Weil.Local.ExtensionWeilRange` | (the finite-index instance for the range of `ι`, through `ExtensionParameters`) | `ed2420519f971449788ec50aa659a0f8c99da606ec202904967cbe1fb70bacf5` |
| `Langlands.Weil.Local.ExtensionWeil` | `extensionWeilMap` | `0babc1f2cf7705b43397334a1f16686c6c449d8b5f646e0abd4334d31adde56e` |
| `Langlands.Weil.Local.Parameters` | `LocalWeilRepresentation`, `LocalWeilDeligneRepresentation`, `IsLocalFrobeniusSemisimpleParameter` | `411478f2fd50ec77e62978dbc2352f5d3511bdb4d9d8cfc99e040c73fca8b551` |
| `Langlands.Weil.Local.Assembly` | `localWeilGroup`, `localInertia`, `localDegree` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` |
| `Langlands.Weil.Representation.Predicates` | `IsContinuous`, `HasOpenInertiaKernel`, `HasFiniteImage`, `IsSemisimple` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.Weil.Representation.Basic` | `FiniteRepresentation.Equiv`, `representation` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Weil.Representation.Dual` | `FiniteRepresentation.dual` | `38cafaca417661df1fd2462cb71fcb880341c4fc561de35797c8b713229a8f74` |
| `Langlands.Weil.Representation.SumsTensor` | `FiniteRepresentation.sum`, `FiniteRepresentation.tensor` | `d5ce49ecda33a85b025d201c0cb114a98bbed8c65d36050aa6fc1b55cf42275b` |
| `Langlands.Weil.Representation.Twist` | `FiniteRepresentation.twist` | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `Frobenius.IsSemisimplification` only | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |
| `Langlands.WeilDeligne.InductionAlong` | (pair induction along `ι`, through `ExtensionParameters`) | `06e1ced26e07b39c1105c8aa763591a2ef1bdc392c3ba3d1971f9dd2b8644ac3` |
| `Langlands.LocalField.Definitions` | `PadicField` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` |

`ExtensionParameters` and `InductionAlong` are Worker 17's construction modules,
and `ExtensionWeil`, `ExtensionWeilRange`, `Parameters` and `Assembly` are
Worker 53's. They belong to the parameter-definition companion task
`650de61a-84c3-40d1-b791-0544af5824e1`, which recreates the task
`503968de-16f8-4f63-ba13-b5e167e11dce` named in this task's contract. `FrobeniusStatements` is Worker 1's
statement family; only its relation `IsSemisimplification` is used, and none
of its targets is assumed. Mathlib is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`. `Representation.IntertwiningMap`,
with its `Module ℂ` structure and `toLinearMap`, comes from Mathlib.
