# Kernel, morphisms and ordinary WD semisimplicity

Worker 1, task `4bcfd048-60a1-4be4-a737-2fb8c48efc46`, revision 1.
These are independently reviewed proposition definitions, not theorem proofs.

The input is the companion's actual finite-dimensional complex
`WeilDeligneRepresentation`, with its nilpotent monodromy, norm covariance,
linear morphisms and genuine isomorphisms. No block classification,
Frobenius-semisimplicity assumption, or local-field identification is needed
for this algebraic family.

`IsStable` means that an actual linear subspace is preserved by every Weil
operator and by N. `IsIrreducible` explicitly requires a nontrivial carrier
and no proper nontrivial stable subspace. `IsSemisimple` requires every stable
subspace to have a stable linear complement. These definitions directly
describe ordinary WD representation theory. They do not assume the desired
equivalences with N=0, and ordinary WD semisimplicity is distinct from the
companion's Frobenius-semisimplicity predicate.

## Declaration-level source and dependency map

| Declaration | Mathematical content and provenance |
| --- | --- |
| `IsStable` | Actual invariant-subspace interpretation of the pair in Tate 4.1.2 and the kernel argument of 4.1.5. |
| `IsIrreducible` | Ordinary irreducibility of the pair, including nontriviality, as used in Tate 4.1.5. |
| `IsSemisimple` | Ordinary complete reducibility expressed by stable complements. This is the intrinsic notion for the whole pair, not Tate 4.1.3's condition on the underlying Weil action. |
| `KernelStability` | Tate 4.1.5: the actual ker N is stable under the Weil group. Equality under each invertible action operator is explicit. |
| `IrreducibilityComparison` | Tate 4.1.5: irreducible iff N=0 and the Weil representation is irreducible. |
| `SemisimplicityComparison` | Derived from the same nilpotent-kernel argument: a stable complement to ker N must vanish because its N restriction is both injective and nilpotent; conversely N=0 makes the stable-subspace conditions exactly those of the Weil representation. It compares the whole pair with its Weil action only, not with Frobenius semisimplicity (see below). |
| `MorphismCompatibility` | Derived directly from the actual intertwining and N-commutation equations: all powers of N, their kernels/images, stable subspace images and inverse images are preserved. |
| `IsomorphismInvariants` | Derived from those equations and invertibility: rank, vanishing of N, ordinary irreducibility/semisimplicity, Frobenius semisimplicity, power kernels/images and their dimensions, and actual Weil determinants are invariant. |
| `ZeroMonodromyCompatibility` | Tate 4.1.2–4.1.5; full faithfulness uses the companion's actual zero-monodromy construction. Cross-universe intertwiners and equivalences are retained. |
| `AlgebraicFamily` | Whole-target conjunction of the preceding algebraic assertion families. |
| `ParameterIsomorphismInvariants` | Inertia kernels agree under conjugation, finite inertia images are conjugate, and conjugation by a finite-dimensional complex linear equivalence is continuous for the usual topology. The three conditions are preserved separately. |
| `Statement` | Whole target combining the algebraic family and preservation of the separate parameter conditions. |

Only propositions are defined here. The explanation of a proof route above
is provenance for a derived statement, not a claim that its Lean proof exists.
The zero-monodromy constructor's intrinsic obligations already belong to the
companion definition; this family records the desired comparison and invariance
targets on that same constructor.

## Ordinary and Frobenius semisimplicity

`SemisimplicityComparison` asserts that ordinary semisimplicity of the whole
pair holds exactly when N=0 and the underlying Weil representation is
semisimple. It asserts nothing about Frobenius semisimplicity. For the generic
group, degree and norm character used here, neither notion implies the other:

- Take `G = ℤ × GL₂(ℂ)`, `V = ℂ²`, `r(n, g) = g`, `N = 0`, trivial `ν`, and
  `degree(n, g) = n`. The pair is irreducible, hence ordinarily semisimple.
  The degree-one element `(1, [[1, 1], [0, 1]])` acts by a nonsemisimple
  Jordan block, so the pair is not Frobenius semisimple.
- Take `G = ℤ` with the identity degree, `ν(n) = q^(-n)` for some `q > 1`,
  and `V = ℂ²` with basis `e₀, e₁`, `r(n) = diag(1, q^(-n))`, `N e₀ = e₁`,
  `N e₁ = 0`. Covariance holds and every `r(n)` is semisimple, so the pair is
  Frobenius semisimple; since N ≠ 0 it is not ordinarily semisimple.

Tate 4.1.3 compares Frobenius semisimplicity with semisimplicity of the
underlying Weil representation using finiteness of the inertia image (the
first example has infinite inertia image). That comparison, under surjective
degree and finite inertia image, is the published
`Langlands.WeilDeligneRepresentation.Frobenius.WeilSemisimplicityComparison`.
It is not restated here.

## Exact original sources

- John Tate, *Number theoretic background* (1979), registered ID
  `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  File:
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
  Exact locators: 4.1.2–4.1.5, printed page 20 / PDF29. Worker 1 read the
  text and visually checked that page. In 4.1.3 the ordinary semisimplicity
  comparison refers to the **underlying Weil representation**.
- Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*
  (1973), registered ID `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  File:
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
  Exact locators: Definition 8.4.1, internal/PDF68, and Definition 8.6,
  internal/PDF70, for the pair and separate Frobenius-semisimplicity convention.
  Both pages were read and visually checked.

The operation compatibility family will additionally cite Henniart2002 2.1.
No arithmetic L/epsilon/gamma identities or special-block classification are
asserted by this file.

## Dependencies

The pair core is Worker 17's published work for the companion definition task
`650de61a-84c3-40d1-b791-0544af5824e1` (this task's context cites it by its
earlier identifier `503968de-16f8-4f63-ba13-b5e167e11dce`). This statement
imports these modules from the development Library at commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`, with these Lean hashes:

- `Langlands/Weil/Representation/Basic.lean`:
  `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b`.
- `Langlands/Weil/Representation/Predicates.lean`:
  `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148`.
- `Langlands/WeilDeligne/Basic.lean`:
  `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf`.
- `Langlands/WeilDeligne/Parameters.lean`:
  `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c`.

No companion source is included as new authored content. From Mathlib it uses
`Representation.IsIrreducible` (simple subrepresentation lattice),
`Representation.IsSemisimpleRepresentation` (complemented subrepresentation
lattice) through the companion's abbreviations, and `LinearMap.det`.

Worker 39 has agreed that the sibling block family (task
`fb3d3bca-bec4-4b30-9f0e-ac37da732e58`) will abbreviate this file's
`IsStable` and `IsIrreducible`, and use the same stability convention for
indecomposability. That is a block-to-linear-algebra dependency only; no block
statement is imported or assumed here.

## Check

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` v1:
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `d9d1dac9-2215-448f-b8ee-4cfabf15dcce` compiled this module
over the Library with no errors or warnings. It inspected
`Langlands.WeilDeligneRepresentation.LinearAlgebra.Statement`, confirmed
`statement_returns_prop: true`, and returned whole-target SHA-256
`9d1d4a37c51b0e803c65bd5f99d01cd0b8545f58f25c22fcc52f0d63a0e18c31` and type
SHA-256 `d523215553e5c4a547f606ac6fc9818bd9426b258e557432c08ac1de37d42554`.
Its independent universes are `uG`, `uV`, and `uW`; its axioms are `propext`,
`Classical.choice` and `Quot.sound`. This is development evidence, separate
from the independent semantic review that accepted this statement contribution.
