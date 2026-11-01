# Actual normalized source-Phi tensor quotient

Author: Worker 499.

This module constructs `leftPhiSourceQuotient` in
`Langlands.Derivative.MirabolicProductMinus`. It is the actual identity
on the GL factor tensored with the source Phi-minus quotient, regarded
as an intertwiner from the normalized higher section coefficient to
the normalized lower inducing coefficient. It is surjective, its kernel
is exactly the actual identity-orbit radical relation span, and it is
natural in both inputs, including independent carrier universes.
This is a lower coefficient construction for BZ77 §4.13(b). The
compact-induction comparison, identification with the actual localized
section representation, and six-part host theorem remain separate
obligations.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
positive-character localization with inverse-half normalization of the
normalizing action. Sections 3.1–3.2, printed pp.450–451 (PDF pages
11–12), specify the mirabolic groups, positive last-coordinate
character and minus functors. Section 4.12(II), printed pp.456–457
(PDF pages 17–18), specifies the upper-block left mixed product;
§4.13(b), printed p.458 (PDF page 19), states its functorial comparison.
Section 7.2, printed p.471 (PDF page 32), gives the identity and cycle
representatives. These passages and relevant page images were read
during this task. The bounded supplied-source and public-note errata
search found no applicable BZ77 entry; no global absence is asserted.

The present coefficient representations, tensor quotient and naturality
proof are internal derived content. Their inputs are the published
actual coefficient localization, explicit determinant-character identity,
normalized source Phi-minus action, quotient maps and external tensor
maps. The proof does not assume the source's representation comparison.
The module imports neither the section-action comparison nor a Haar
calculation or generic character-stages comparison. Worker 499 wrote
this construction; no peer draft supplies a proof body.

## Parameters and ranks

The declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}` and supplied `T : F.TopologicalData`.
Every required topology on `F.Carrier` is `T.topology`; it is installed
in the parameter types, exported types and definition bodies. The
character `ψ : UnitaryAdditiveCharacter F.Carrier` uses this topology;
its bundle supplies continuity and nontriviality. No canonical topology
is chosen and no extra local-compactness premise is added.

For every `k,r : ℕ`, including zero, the inputs are

```text
ρ : Representation ℂ GL_(k+1)(F) V,
B : SmoothRep ℂ P_(r+2)(F).
```

The first representation is arbitrary and need not be smooth. Its
carrier universe `uV`, the smooth carrier universe `uW` of `B`, and the
field universe `uF` are independent. The naturality declarations also
allow independent `uV'` and `uW'` for the target inputs. No finite
dimension, admissibility, irreducibility, finite length, genericity,
nonzero vector or universe saturation is assumed. Zero objects are
included.

Here `mirabolic (r+1) F.Carrier` denotes `P_(r+2)(F)` and
`phiMinus T ψ r` is the actual functor from `P_(r+2)` to `P_(r+1)`.
The higher left mixed product has group `P_(k+r+3)` and the output
of ambient Phi-minus has group `P_(k+r+2)`. The actual lower subgroup
in this module is

```text
H = leftSubgroup (k+1) r F.Carrier ≤ P_(k+r+2)(F).
```

For `h ∈ H`, write `(a,q) = leftProjection h`, so
`a ∈ GL_(k+1)(F)` and `q ∈ P_(r+1)(F)`. The higher coefficient
pair is exactly `(a, successor q)`, with `successor q ∈ P_(r+2)`.
All matrices and coefficient projections are the published actual ones.
The GL input has positive rank for every `k`, including `k=0`.
No `P_0` is introduced and Phi-minus is never applied to `P_1`.

Write

```text
Q_B = Coinvariants B.representation (radical (r+1) F.Carrier)
        (Mirabolic.theta ψ r),
q_B = Mirabolic.phiMinusQuotient T ψ r B : B →ₗ[ℂ] Q_B.
```

The actual carrier of `(phiMinus T ψ r).obj B` is definitionally
`Q_B`; normalization changes its action, not its carrier or quotient
map. The character in the relation
`[B(u)w] = (theta ψ r u : ℂ) • [w]` is positive.

## The two actual normalized actions

Set `K=k+1`, `λ_(K,r)=T.leftLeviCharacter K r`,
`α_r=Mirabolic.phiMinusCharacter T r`, and
`χ=leftPhiSectionCharacter T K r`. The published equality of complete
unit-valued homomorphisms is

```text
χ(h) = λ_(K,r)(a,q) α_r(q).
```

The definition of `χ` includes the ambient inverse-half determinant
character and the higher positive-half covariance character evaluated
at `(a, successor q)`. The equality retains the supplied determinant
norm and every block, and leaves no residual twist.

`leftPhiHigherSectionRepresentation` is the twist by `χ` of
`leftInducingRepresentation ρ (B.representation.comp successor)`.
Its carrier is `V ⊗[ℂ] B`, and its action is

```text
h • (v ⊗ w) = (χ(h) : ℂ) • (ρ(a)v ⊗ B(successor q)w).
```

`leftPhiSourceCoefficient` is the twist by the actual lower character
`(T.leftCharacter K r).toMonoidHom` of
`leftInducingRepresentation ρ ((phiMinus T ψ r).obj B).representation`.
Its carrier is the entire `V ⊗[ℂ] Q_B`. It is precisely the inducing
coefficient used by the lower left mixed product with the actual
normalized source Phi-minus object. This statement identifies the
coefficient definition, not the induced representation.

`leftPhiSourceCoefficient_tmul_quotient` proves

```text
h • (v ⊗ q_B(w))
  = (χ(h) : ℂ) • (ρ(a)v ⊗ q_B(B(successor q)w)).
```

The proof expands the actual lower twist and applies
`Mirabolic.phiMinus_action`, which contributes `α_r(q)` inside the
second tensor factor. `TensorProduct.tmul_smul` moves it outside that
factor and `smul_smul` combines the two scalars. Evaluation of
`leftPhiSectionCharacter_eq` gives the displayed result. The equality
is proved with the actual normalized action and has no scalar premise.

## Quotient, factorization and exact kernel

`leftPhiSourceQuotient` has underlying linear map

```text
id_V ⊗ q_B : V ⊗[ℂ] B →ₗ[ℂ] V ⊗[ℂ] Q_B.
```

Its intertwining law follows by tensor extensionality, the displayed
source action formula and linearity with respect to the scalar `χ(h)`.
`leftPhiSourceQuotient_tmul` records `v ⊗ w ↦ v ⊗ q_B(w)`.

The published `leftPhiCoefficientMk ... 1` is the quotient by every
relation of the actual identity-orbit radical intersection; the top
subgroup in its definition is inside that intersection. The published
`leftPhiTensorEquiv` identifies that quotient with `V ⊗ Q_B`.
`leftPhiSourceQuotient_factor` proves equality of linear maps

```text
id_V ⊗ q_B
  = leftPhiTensorEquiv.toLinearMap ∘ₗ leftPhiCoefficientMk ... 1.
```

Tensor extensionality reduces this to the two published representative
formulas. Thus the map uses the entire actual orbit quotient, rather
than a selected collection of pure tensor relations.

`leftPhiSourceQuotient_surjective` composes surjectivity of the canonical
orbit quotient with surjectivity of the published linear equivalence.
It is onto the full target tensor module, with no basis or nonzero
carrier assumption. `ker_leftPhiSourceQuotient` then proves

```text
ker (id_V ⊗ q_B)
  = relations (leftPhiOrbitRepresentation k r ρ B.representation 1)
      ⊤ (leftPhiOrbitCharacter k r ψ 1).
```

After the factorization, injectivity of `leftPhiTensorEquiv` reduces
vanishing to vanishing of the canonical quotient class;
`Jacquet.Localization.mk_eq_zero` identifies this with membership in
the actual relation span. No exactness theorem or representation-level
comparison is assumed.

## Naturality with independent carriers

For arbitrary intertwiners `f : ρ.IntertwiningMap ρ'` and
`g : B.representation.IntertwiningMap B'.representation`,
`leftPhiHigherSectionMap` pulls back `g` along `successor`, tensors it
with `f`, pulls the result back along `leftProjection`, and twists by
the same `χ`. Its underlying linear map is `f ⊗ g`.

`leftPhiSourceQuotient_naturality` proves, for every `x ∈ V ⊗ B`,

```text
q'(higherMap(f,g)(x))
  = TensorProduct.map f.toLinearMap (mapLinear radical theta g) (q(x)).
```

Here `q` and `q'` are the two tensor quotient maps. The proof first
identifies the composed linear maps using tensor extensionality and
the quotient map's representative formula, then evaluates that equality
at `x`. The map `mapLinear radical theta g` is the actual map induced
by `g` on the source relation quotient. All four carrier universes
are independent, so this statement is stronger than its ordinary
same-universe categorical specialization.

`leftPhiSourceCoefficientMap` equips the right-side tensor map with the
actual lower intertwining law. For an arbitrary vector in the source lower coefficient, the
surjectivity just proved supplies a preimage under `q`. Naturality and
the higher input map's intertwining law move the action through this
preimage, and the two quotient intertwiners move it back to the lower
actions. The Lean proof uses successive equality transitivity so that
the definitionally equal normalized and raw quotient carriers have
explicit expected types. No transparency or heartbeat option is changed.
Finally `leftPhiSourceQuotient_natural` records the same naturality
square with both maps packaged as actual intertwiners.

## Import and mathematical dependency audit

The only direct imports are
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient`
and
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization`.
Their complete project import closure contains 79 modules, listed below.
All 158 imported Lean/Markdown files are byte-for-byte identical to the
published Library at commit `b222ad9033fe539984cca2d240ff2c1ba76dee21`,
with hashes checked against its manifest. Every imported module has a
nonempty Markdown companion. The new module is excluded from that count.

The actual mathematical inputs are the published identity-orbit tensor
equivalence and quotient representative formulas, canonical localization
surjectivity and kernel relation span, actual normalized source
Phi-minus action, the full determinant-character identity, and elementary
external tensor, pullback and twist intertwiners. Naturality uses the
relation-induced linear map and descent along a proved surjection.
Transitively, the coefficient and scalar units use actual matrix
radicals, coefficient maps, positive character relations, block
determinants and real-power arithmetic. The imported induction and
smoothness definitions supply no comparison or exactness conclusion.
Whittaker modules in the closure provide elementary group and character
infrastructure, with no finiteness result used.

The following audit covers every inherited exclusion directly and
transitively.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent from the closure. No mixed-minus comparison or boundary conclusion is used or proved by this coefficient unit. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The successor and actual radical subgroup are elementary matrix constructions. |
| General Leibniz and derivative formulas | No Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. The actual minus functor's definition and action formula are published. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, its successor, or its downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. |
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire tensor factors are retained. There is no finite dimension, admissibility, irreducibility, finite length, genericity, chosen vector, universe saturation, canonical topology or theorem-valued premise. The inverse-half source scalar is included exactly. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending generic proofs and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | The unit constructs a source coefficient quotient; it does not duplicate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |

A code scan of this module and its complete project closure finds no
occurrence of any of the host's 38 excluded task identifiers or 24 named
consumer declarations, and no proof holes, new axioms or unsafe evaluation
commands. Names in explanatory Markdown are audit prose. Declaration
inspection of `leftPhiSourceCoefficientMap` reports independent universe
parameters `uF,uV,uW,uV',uW'` and only `propext`, `Classical.choice` and
`Quot.sound` as axioms. Compilation and inspection are development
evidence; independent review and publication remain necessary.

## Complete project import closure

The following list contains every direct and transitive project import;
it excludes this new entry module. Mathlib imports resolve through the
supplied pinned environment.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
