# Smooth real homomorphisms factor through the actual valuation image

Author: Worker 723.

This module states Renard V.3.19 for the rational points of an actual
connected reductive group with the canonical rational-point topology. It
contains one proposition definition and proves nothing.

## Statement

`Langlands.Plancherel.RationalSmoothRealDescentStatement.{u}` is a closed
`Prop`. It quantifies over:

- every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
  `IsNonarchimedeanLocalField F`, in equal or mixed characteristic;
- every actual group scheme `M : GroupScheme (Spec (CommRingCat.of F))`;
- every `hM : Langlands.GroupScheme.IsConnectedReductive M`.

The point group is `GroupScheme.rationalPoints M`, with exactly the topology
`rationalPointTopology F M.X`. This topology needs `IsAffine M.X.left`. The
statement derives that certificate from `hM`: `hM.isAffineHom` makes the
structure morphism affine, and `isAffine_of_isAffineHom` applies over the
affine base `Spec F`. No embedding into `GL_N`, splitness, characteristic, rank
or finite-type premise is added. Stating the target does not need a
finite-type certificate. A proof can take one from `hM.smooth`.

Then, for every group homomorphism
`f : GroupScheme.rationalPoints M →* Multiplicative ℝ` whose kernel is open in
that topology, the statement asserts both of the following:

1. `rationalCommonNormKernel M ≤ f.ker`.
2. There is a unique `phi : rationalImageRealFunctionals M` such that, for every
   `g : GroupScheme.rationalPoints M`,
   `phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd`.

`Multiplicative ℝ` is the additive group of real numbers written
multiplicatively. So `f.ker` consists of the points with real value zero, and
`(f g).toAdd` is the real value of `f` at `g`. A homomorphism to `ℝ` is
smooth (locally constant) exactly when its kernel is open, so the open-kernel
premise is the book's smoothness. It is the only hypothesis on `f`.

Both clauses are conclusions. The statement assumes no norm-kernel
annihilation, factorization, compact generation, abelianization of the point
group, cocompactness, finite index or representation-theoretic result.

The statement does not include the converse direction, that every `phi`
composed with the projection has open kernel.

## Existing constructions used

All objects are imported by Lean name. This module introduces no group, torus,
lattice or valuation of its own.

- `Langlands.Plancherel.rationalCommonNormKernel M` (module
  `RationalCharacterValuation`) is the intersection, over all rational
  characters `χ : GroupScheme.rationalCharacters M`, of the kernels of the
  normalized absolute values `g ↦ |χ(g)|_F`.
- `Langlands.Plancherel.rationalValuationImageProjection M` (module
  `RationalImageCharacters`) is the actual valuation
  `g ↦ (χ ↦ v_F(χ(g)))` into `Multiplicative (rationalCharacters M →+ ℤ)`,
  with its codomain restricted to the image `rationalDiscreteValuationImage M`.
  The published theorems `rationalValuationImageProjection_surjective` and
  `rationalValuationImageProjection_ker` state that it is onto that image and
  that its kernel is `rationalCommonNormKernel M`.
- `Langlands.Plancherel.rationalImageRealFunctionals M` (module
  `RationalImageRealPart`) is the abbreviation
  `Additive (rationalDiscreteValuationImage M) →+ ℝ`.

`GroupScheme.rationalCharacters M` consists of the group-scheme homomorphisms
from `M` to `𝔾_m` over `Spec F`, that is, the characters defined over `F`.

## Source correspondence

Source: Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The governing passage is V.3.19, printed p.115 / PDF p.121. Its notation comes
from V.2.1, printed p.104 / PDF p.110; V.2.2–V.2.3, printed pp.105–106 / PDF
pp.111–112; and V.2.6, printed pp.107–108 / PDF pp.113–114.

V.3.19 writes, for a Levi factor `M` of a parabolic `P = MN`,

`𝔞* = Hom_Z(Λ(M), R) = {φ ∈ Hom_Z(M, R) | φ|_{⁰M} ≡ 0} = Hom_{Z,lisse}(M, R)`,

and says that the last equality remains to be justified by showing that every
smooth homomorphism from `M` to `R` is trivial on `⁰M`. Here `M` denotes the
group of `F`-points. The source warns that `Λ(M)` is written additively and `M`
multiplicatively.

| Renard | Lean |
| --- | --- |
| nonarchimedean local field `F` (V.2.1) | `F` with the four instances above |
| `M`, points of a connected reductive `F`-group | `GroupScheme.rationalPoints M` with `hM` |
| topology induced from an embedding in `GL_N(F)` (V.2.1) | `rationalPointTopology F M.X` |
| rational characters `X*(M)` (V.2.2) | `GroupScheme.rationalCharacters M` |
| `H_M`, `⟨χ, H_M(g)⟩ = v_F(χ(g))` (V.2.3.1) | `rationalValuationImageProjection M` |
| `Λ(M)`, the image of `H_M` (V.2.3) | `rationalDiscreteValuationImage M` |
| `⁰M = ⋂ ker abs(χ)_F`, equivalently `ker H_M` (V.2.3) | `rationalCommonNormKernel M` |
| `Hom_Z(Λ(M), R)` | `rationalImageRealFunctionals M` |
| `Hom_{Z,lisse}(M, R)` | `f : rationalPoints M →* Multiplicative ℝ` with open kernel |

Clause 1 is the assertion the source sets out to justify. Clause 2 is the
explicit content of the identification `Hom_Z(Λ(M), R) = Hom_{Z,lisse}(M, R)`
in the direction from smooth maps: every smooth map is `phi ∘ H_M` for exactly
one additive map `phi` on `Λ(M)`. The Lean statement quantifies over every
connected reductive group rather than only Levi factors. The source argument
uses only connected reductivity of `M`, and V.2.3 and V.2.6 are stated for any
connected reductive group. The other identifications in the V.3.19 display,
`𝔞 = X_*(A) ⊗ R = Λ(M) ⊗ R = X_*(M) ⊗ R` and `𝔞* = Hom_R(Λ(M) ⊗ R, R)`, are
not part of this target. Neither is the final remark that `ln abs(χ) ∈ 𝔞*`.

The source fixes the topology through an embedding in `GL_N(F)` and notes that
it does not depend on the embedding. The Lean statement uses the published
canonical evaluation topology instead. Comparing the two topologies is not part
of this target.

### Normalization

The target concerns additive real maps, so it has no residue-cardinality
scalar. `H_M` uses the integer valuation `v_F`, and the published projection
uses the same positive valuation. The defining equation
`phi (H_M g) = f g` has no factor of `q` or `log q` and no sign change. The
negative-exponent normalized logarithm of `rationalImageRealPart` is not used.
The separate split-torus real-part task `8f4fd374` keeps its own discrepancy
between the normalized `λ` and the raw logarithm. No such convention changes
the kernel or evaluation equality here.

## Proof boundary

This section describes the source argument and its gaps. It does not claim an
audited proof. V.3.19 argues as follows.

1. `R(M)𝒟M` is cocompact in `M`, and `𝒟M ⊂ ⁰M` (V.2.3, Proposition).
2. Hence `(R(M) ∩ ⁰M)𝒟M` is cocompact in `⁰M`.
3. `R(M) ∩ ⁰M` is compact, as shown in the proof of V.2.6, Proposition. So every
   smooth real homomorphism is trivial on it, by the V.2.3 lemma: the only
   compact subgroup of the positive reals is trivial.
4. Every homomorphism to the abelian group `R` is trivial on commutators.
5. So a smooth real homomorphism is trivial on a finite-index subgroup of `⁰M`.
   Since `R` has no nonzero torsion, it is trivial on `⁰M`.

The sentence in step 5 says "tout morphisme", but the preceding steps use
smoothness. Without it clause 1 fails. Take `M = 𝔾_m` and `F = ℚ_p` with `p`
odd. Then `⁰M = ℤ_p^×` contains `1 + pℤ_p ≅ ℤ_p`, and a nonzero `ℚ`-linear map
`ℚ_p → ℝ` gives a homomorphism `ℚ_p^× → ℝ` that does not vanish on `⁰M`. So the
Lean statement keeps the open-kernel hypothesis, matching `Hom_{Z,lisse}`.

The source steps leave the following points to be established in a formal
proof. They are not hypotheses of this statement.

- **Cocompactness on rational points.** `M = R(M)𝒟M` as algebraic groups does
  not make `R(M)(F)𝒟M(F)` cocompact in `M(F)`. The multiplication map is a
  central isogeny. Scheme-level epimorphy gives neither surjectivity nor
  finite index on `F`-points. In positive characteristic, an inseparable
  isogeny can have an image of infinite index on rational points. The 2026 text
  already says cocompact, not finite index. Cocompactness, and its transfer to
  the intersection with `⁰M` in step 2, are local-point structural theorems.
- **Compactness of `R(M) ∩ ⁰M`.** The V.2.6 argument uses the anisotropic part of
  the radical and the split component. It also needs compactness of the points
  of anisotropic tori and another cocompactness on rational points.
- **Derived points versus abstract commutators.** In the source, `𝒟M` means the
  `F`-points of the algebraic derived group. Step 4 kills only the abstract
  commutator subgroup `[M(F), M(F)]`, which can be strictly smaller. For
  `M = PGL_2`, the derived group is all of `PGL_2`. But the commutator subgroup
  of `PGL_2(F)` is the image of `SL_2(F)`, with quotient `F^×/(F^×)^2`
  through the determinant. So annihilation of the actual derived points by
  smooth real homomorphisms is a separate statement. It does not follow from
  triviality on commutators, and it is not a definitional equality.

These obligations are already stated as targets in the published module
`Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement`, by Workers
118 and 6. That module states `CentralNormKernelCompactness` (the scheme center
meets the norm kernel in a compact set), `CentralDerivedNormKernelCocompactness`
(a compact point-group quotient of the norm kernel), and
`DerivedSmoothRealAnnihilation` (smooth real homomorphisms kill the actual
derived points), together with their conjunction
`SmoothRealStructureStatement`. That module explicitly leaves the present
declaration to this task. This module does not import it and does not assume
its targets.

A proof from those targets would continue as follows. Smooth real
homomorphisms are trivial on compact subgroups and on the actual derived points.
The open kernel meets the norm kernel in an open subgroup containing the
cocompact subgroup, so the remaining quotient is finite. Its image in the
torsion-free reals is then trivial. Clause 2 follows from clause 1 using the
published `rationalValuationImageProjection_surjective` and
`rationalValuationImageProjection_ker`, with uniqueness from surjectivity. The
published `rationalNormKernelQuotientContinuousEquiv` only provides the
quotient descent after clause 1 is known. It does not prove clause 1.
