# Restriction and induction of actual Weil–Deligne pairs

Worker 25 formalizes the Weil–Deligne restriction/induction statement family of
task `f32f0f21-11a9-4bfd-9daa-e7541926d3be`. The entry proposition is
`Langlands.WeilDeligneRepresentation.RestrictionInductionStatements`, the
conjunction of the thirteen targets below. It uses Worker 17's actual
`WeilDeligneRepresentation` pairs (finite-dimensional complex carriers,
nilpotent monodromy, covariance `r(g) N r(g)⁻¹ = ν(g) N`) and their separate
parameter predicates. It defines relations on actual pairs, not a replacement
WD record or an assumed classification. The model relations are bound to the
companion's concrete `restrict` and `induce` constructors; the latter uses
actual equivariant functions and norm-weighted monodromy. Operation comparisons
use the companion's actual sums, tensors, duals, twists and kernels. These are
proposition definitions; no proof is claimed.

`IsRestrictionModel φ ν A B e` says that the actual linear equivalence
from the restricted Weil action to `B` commutes with monodromy.
`RestrictionModelsExistUniquely` asserts existence and uniqueness up to
actual pair isomorphism. The witness is a conclusion and keeps the original
carrier universe. Comparisons allow independent carrier universes.
`RestrictionConstructorCompatibility` identifies the actual `restrict φ A`
as a model using the identity equivalence on its unchanged carrier.

`IsInductionModel S ν A B e` requires an actual representation equivalence
from Mathlib's coinvariant induced carrier to `B`, and imposes the formula

```
N_B(e([g ⊗ v])) = ν(g) * e([g ⊗ N_A(v)]).
```

This formula is essential: simply applying `N_A` on the vector factor does
not descend through the diagonal coinvariant relation when the norm on
`S` is nontrivial. Mathlib's group action is
`x.[g ⊗ v] = [g*x⁻¹ ⊗ v]`. Therefore the displayed formula gives
`r(x) N = ν(x) N r(x)`, exactly the companion's covariance convention.
In the equivalent coinduced-function model the operator is
`(Nf)(g) = ν(g) N_A(f(g))`. Its covariance and subgroup-equivariance
give the same sign. All norm values are units.

`InductionModelsExistUniquely` quantifies an actual finite-dimensional
pair and an actual equivalence to `IndV`; it does not assume that `IndV`
is finite-dimensional or that a canonical induced pair has already been
selected. The finite-index hypothesis makes that conclusion valid.
Uniqueness compares any two such pairs by an actual WD isomorphism.
The expected carrier universe is `max uG uV`. Group and carrier universes
remain independent. `InductionConstructorCompatibility` asserts an actual
representation equivalence from the coinvariant construction to the
companion's specified function-model pair, satisfying this monodromy formula.
The comparison is an existential conclusion; it is not an input certificate.

`RestrictionModelConsequences` states rank and determinant restriction,
equality of dimensions of every monodromy-power kernel and image,
reflection of zero monodromy, preservation of F-semisimplicity for the
pulled-back degree, ordinary continuity under a continuous group map,
and the parameter condition under the explicit inertia inclusion.

`InductionModelConsequences` states that rank and every monodromy-power
kernel/image dimension are multiplied by `[G:S]`. On a coset model,
monodromy is a direct sum of nonzero scalar multiples of the original
operator. It also reflects zero monodromy, compares F-semisimplicity with
the pulled-back degree, and compares ordinary continuity and open inertia
kernel when `S` is open and inertia is normal. The F-semisimplicity
comparison uses a positive power that fixes the finite coset set and
the characteristic-zero fact that an invertible operator is semisimple
if and only if a positive power is semisimple. It does not equate
F-semisimplicity with zero monodromy.

`InductionModelReciprocity` gives a unique actual WD morphism extending
each subgroup intertwiner which commutes with monodromy. Its value on
`e([1 ⊗ v])` is prescribed. The unique Weil-intertwiner sends
`e([g ⊗ v])` to `r_C(g⁻¹)f(v)`; the norm factor in the induction
model is precisely what makes it commute with monodromy.

## Compatibility with actual operations

`RestrictionOperationCompatibility` compares actual restrictions of sums,
tensors, negative-transpose duals and character twists with the corresponding
operations on restrictions. It also identifies the actual kernel representation
of a restricted pair with restriction of its kernel, and compares restriction
of `zeroMonodromy` with zero monodromy on the restricted Weil representation.
All comparisons are actual linear WD or Weil equivalences. No classification,
semisimplicity or topology hypothesis is needed for these algebraic identities.

`InductionOperationCompatibility` asserts actual WD equivalences for sums,
duals and character twists, and the projection formula

```
Ind_S^G(A tensor Res_S^G C) ≅ (Ind_S^G A) tensor C.
```

It also identifies the actual kernel representation of `induce S A` with
Weil induction of `kernelRepresentation A`, identifies induction of a
zero-monodromy pair with zero monodromy on Weil induction, and preserves
actual input isomorphisms even between different carrier universes.
These statements use the companion constructors themselves, not arbitrary
objects named as their outputs. They allow nonzero monodromy and rank zero.

The formulas can be checked directly on the function model. The projection
map from `(Ind A) tensor C` sends `f tensor c` to the function
`g ↦ f(g) tensor r_C(g)c`. The equality `r_C(g)N_C=nu(g)N_Cr_C(g)`
gives its monodromy square. For twists the map sends `f` to
`g ↦ chi(g)f(g)`. For duals, finite coset summation pairs the two induced
functions. Subgroup equivariance makes the pairing independent of coset
representatives, and the two terms involving `nu(g)N` cancel because the
dual has monodromy `-transpose N`. The kernel comparison uses
`nu(g) ≠ 0`, so pointwise `nu(g)N f(g)=0` is equivalent to `N f(g)=0`.
These observations explain the derived statements; this module supplies
no proof of them.

`InductionTransitivity` compares induction through an actual subgroup tower
`S ≤ T ≤ G` with direct induction from `S`. The subgroup `S.subgroupOf T`
is identified with `S` by Mathlib's actual `subgroupOfEquivOfLe`; the
source pair is restricted along that identification before the two actual
induction constructors are applied. In the iterated function model the
comparison evaluates `F(g)(1)`. Weighted monodromy contributes `nu(g)`
at the outer step and `nu(1)=1` at the inner step. Thus transitivity
respects the same monodromy and norm convention. Both subgroup indices
are explicitly finite.

## Semisimplification and residue-degree normalization

The last three targets reuse Worker 1's exact
`Frobenius.IsSemisimplification` relation. That relation quantifies a linear
carrier identification, a unipotent correction commuting with the Weil action
and N, and the corrected action. No theorem from Worker 1's statement family
is assumed as a hypothesis.

`RestrictionSemisimplificationCompatibility` transports any actual related
pair to the actual restricted pairs, with pulled-back degree. The same
correction and carrier identification work on the subgroup. The statement
asserts preservation of this relation; it does not postulate a selected
semisimplification or require surjectivity of the pulled-back degree.

`InductionSemisimplificationCompatibility` similarly relates the two actual
induced pairs. Apply the source correction pointwise on equivariant functions.
It commutes with right translation and the weighted monodromy, and remains
unipotent. For any nonzero-degree group element, a positive power fixes all
finite cosets. On each coordinate its corrected exponential action becomes
one of the semisimple operators already required by the source correction
predicate. An invertible complex operator is semisimple if and only if a
positive power is semisimple. This gives the derived compatibility without
adding a finite-inertia, topology or surjectivity premise to a relation that
already supplies the required correction properties.

`SemisimplificationDegreeRescaling` states that replacing a degree `d` by
`d^n`, for a positive natural `n`, does not change the relation. On additive
integer values this multiplies degree by `n`. To keep the same corrected
action when passing from `d` to `n*d`, replace a unipotent correction by its
unipotent nth root; in the reverse direction take its nth power. Such roots
exist uniquely over the complex numbers and are polynomials in the nilpotent
part, so all commutation conditions are retained. The final corrected action
and its exponential semisimplicity condition are identical. This is a
separate linear-algebra proposition, not an assumed root construction.
For a residue-degree `f`, the actual arithmetic relation
`d_F restricted to W_E = f*d_E` therefore permits comparison using the
normalized degree of each field. The arithmetic identity and the actual
residue cardinalities must still come from the construction tasks.

## Source-to-declaration map

The base pair and covariance are Tate 4.1.2, printed page 20/PDF29, and
Deligne 8.4.1, internal/PDF68. Tate 2.1, printed pages 9–10/PDF18–19,
supplies restriction, finite-index induction and Frobenius reciprocity.
Tate 4.1.3–4.1.5, printed page 20/PDF29, and Deligne 8.5–8.6,
internal/PDF70, fix F-semisimplicity as an operator condition without
forcing monodromy to vanish. The model formulas, uniqueness and numerical
consequences are derived linear-algebra formulations of those constructions;
they are not attributed as literal numbered statements in the sources.

| Declaration | Exact source input and derived step |
| --- | --- |
| `IsRestrictionModel`, `RestrictionModelsExistUniquely` | Tate2.1 and4.1.2/Deligne8.4.1: pull back the action and norm, retain the same operator, compare via actual linear equivalences. |
| `RestrictionConstructorCompatibility` | The same construction, bound to the exact companion `restrict` implementation; no new restriction operation is introduced. |
| `IsInductionModel`, `InductionModelsExistUniquely`, `InductionConstructorCompatibility` | Tate2.1 and4.1.2/Deligne8.4.1: finite coset induction with the explicitly derived norm-scaled monodromy. |
| `RestrictionModelConsequences` | Same covariance and operator condition; invariants follow by conjugacy and composition. |
| `InductionModelConsequences` | Tate2.1/4.1.2–4.1.5, Deligne8.5–8.6: finite coset direct sums and the nonzero-degree positive-power argument. |
| `InductionModelReciprocity` | Tate2.1 reciprocity and4.1.2 covariance, with the actual generator condition and its monodromy compatibility derived explicitly. |
| `RestrictionOperationCompatibility` | Tate2.1 and4.1.2/4.1.5: precomposition of the actual operations and the stable monodromy kernel. |
| `InductionOperationCompatibility` | Tate2.1 and2.3.1, printed pages9–11/PDF18–20, give finite-index induction and explicitly use the character projection formula;4.1.2/4.1.5 give the monodromy operations. The general tensor projection formula is a derived identity, verified by the displayed function map. The function formulas above derive the WD comparisons, including the negative dual sign. |
| `InductionTransitivity` | Tate2.1/2.3.1 and4.1.2: actual subgroup-tower induction, with the weighted monodromy calculation above. |
| `SemisimplificationDegreeRescaling` | Derived from Deligne8.5–8.6/Tate4.1.3 and the characteristic-zero power/root calculus for unipotent operators, using the same corrected action. |
| `RestrictionSemisimplificationCompatibility`, `InductionSemisimplificationCompatibility` | Tate2.1/4.1.2–4.1.3 and Deligne8.5–8.6; the correction, finite-coset and positive-power derivations are given above. |

Original sources, read by Worker 25 for this family (locators re-verified on
2026-10-20):

- `tate-1979-number-theoretic-background`, retained Corvallis `Part II.pdf`,
  SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Section 2.1, printed pages 9–10 (PDF 18–19): restriction and induction along
  the closed finite-index subgroup `W_E ⊂ W_F`, "satisfying the usual Frobenius
  reciprocity". Section 2.3.1, printed page 11 (PDF 20): the formula
  `Ind(ρ ⊗ Res χ) = (Ind ρ) ⊗ χ` and transitivity of induction. Sections
  4.1.2–4.1.5, printed page 20 (PDF 29): the pair `(ρ, N)`, its covariance,
  Φ-semisimplification, and the tensor monodromy `N ⊗ 1 + 1 ⊗ N₁`.
- `deligne-1973-local-constants`, retained original PDF,
  SHA-256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  Definition 8.4.1 (internal/PDF page 68) and 8.5–8.6 (internal/PDF page 70):
  pairs, the unipotent part of a Frobenius, and F-semisimplification.
  Formulas were checked visually.

## Lean dependency map

All imports are Lean modules of the current Library; no artifact identity is
imported. Direct project imports and their transitive project closure:

| Module | Declarations used here | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.WeilDeligne.Basic` | `WeilDeligneRepresentation`, `representation`, `monodromy`, `rank`, `Hom`, `Equiv`, `zeroMonodromy`, `IsFrobeniusSemisimple` | `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf` |
| `Langlands.WeilDeligne.Parameters` | `IsParameter`, `IsContinuous` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` |
| `Langlands.WeilDeligne.Restriction` | `restrict` | `ef8109768e49b5a29d6610d401fdf2262039ab4e312a34e423c7ec20b1f412af` |
| `Langlands.WeilDeligne.Kernels` | `kernelRepresentation` | `fc80f9ec895d5bfbc1ae4b397c799aa657eac45b2a4154be30a0fc8f5d560da6` |
| `Langlands.WeilDeligne.SumsTensor` | `sum`, `tensor` | `b022cece208c2429280b3485628442f05da9e0097cb1fb558448a36bc6e0c06d` |
| `Langlands.WeilDeligne.Dual` | `dual` (negative-transpose monodromy) | `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9` |
| `Langlands.WeilDeligne.Twist` | `twist` | `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0` |
| `Langlands.WeilDeligne.Induction` | `induce` (requires `[S.FiniteIndex]`; source norm `ν.comp S.subtype`) | `526a935f20cf87b790c05325df6dd202c981c08b2591e2931750b96b2391d034` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `Frobenius.IsSemisimplification` only | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |
| `Langlands.Weil.Representation.Basic` | `FiniteRepresentation`, `FiniteRepresentation.Equiv` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Weil.Representation.Predicates` | (through `Parameters`) | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.Weil.Representation.Restriction` | `FiniteRepresentation.restrict` | `78b87eff0d236365bbcd8618a9b25ae1885a7010a5385f01118ca006890166eb` |
| `Langlands.Weil.Representation.Induction` | `FiniteRepresentation.induce` | `fa1540edbc06939ba55d083129de81117d290bf5eb5ef2e4e97a832402ba6bee` |
| `Langlands.Weil.Representation.SumsTensor` | (through WD `SumsTensor`) | `d5ce49ecda33a85b025d201c0cb114a98bbed8c65d36050aa6fc1b55cf42275b` |
| `Langlands.Weil.Representation.Dual` | (through WD `Dual`) | `38cafaca417661df1fd2462cb71fcb880341c4fc561de35797c8b713229a8f74` |
| `Langlands.Weil.Representation.Twist` | (through WD `Twist`) | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` |
| `Langlands.Weil.Representation.Invariants` | (through WD `Kernels`) | `6b8ce494e92094357b8035f0a2c782cd67be997a7eb420f01a0ae0b7e78bd87f` |
| `Langlands.Representation.Dual.Definitions` | (generic algebraic dual, through `Dual`) | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` |
| `Langlands.Representation.Twist.Definitions` | (scalar character twist, through `Twist`) | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` |

The WD construction modules are authored by Worker 17 (construction companion
task `650de61a-84c3-40d1-b791-0544af5824e1`); `FrobeniusStatements` is Worker 1's
statement family (task `4bcfd048-60a1-4be4-a737-2fb8c48efc46`), of which only the
relation `Frobenius.IsSemisimplification` is used; none of its proposition targets
is assumed. Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435`;
`Mathlib.RepresentationTheory.FiniteIndex` and Mathlib's
`Representation.ind`/`Representation.IndV` supply the coinvariant induction model.

The generic statements do not supply actual local Weil inclusions. Local
specialization must use the arithmetic constructions, with geometric
Frobenius degree `+1`, norm `q⁻¹`, and the residue-degree scaling of integer
degrees under field restriction. No arithmetic L/epsilon/gamma formula
or LLC assertion is included.
