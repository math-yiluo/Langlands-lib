# Finite operator span of unnormalized Jacquet block scalars: proof

Author: Worker 267.

The theorem `Langlands.Parabolic.jacquetCenterSpan` has the complete
unapplied type `Langlands.Parabolic.JacquetCenterSpanStatement.{uF,uV}`,
with independent field universe `uF` and carrier universe `uV`. It proves
the published statement in
`Langlands.Representation.Parabolic.JacquetCenterSpanStatement` and adds
no hypotheses.

## What is proved

For every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData` (whose `T.topology` is installed), every rank `m`,
every `B : GeneralLinear.BlockShape m`, and every complex representation
`ρ` of `GeneralLinear m F.Carrier` on `V : Type uV` that is admissible and
finitely generated over `MonoidAlgebra ℂ (GeneralLinear m F.Carrier)`, let

```text
ρP = ρ.comp (B.parabolic F.Carrier).subtype
σ  = leviCoinvariants B ρP.
```

Then the complex span of the operators `σ (B.blockScalarLevi F.Carrier a)`,
for all `a : Fin B.length → F.Carrierˣ`, is finite dimensional inside
`Module.End ℂ (LeviCoinvariants B ρP)`. Here `σ` is the actual unnormalized
action on the actual radical coinvariant quotient. Every shape is covered,
including the empty shape at rank zero and one-block shapes, as well as the
zero carrier and reducible input. No irreducibility, central character,
finite-dimensional carrier or finite expansion is assumed.

## Implemented proof

The module reuses the published normalization equality, proves finite
generation of the unnormalized action, imports the center-valued
block-scalar map, and combines the published finiteness results.

### 1. Normalized action as a twist of the unnormalized action

The published `Langlands.Parabolic.twist_inverseHalfCharacter_leviCoinvariants`
in `Langlands.Representation.Exponents.JacquetEigenvectorProof` gives, for
every `ρ`, the equality of representations of `B.Levi F.Carrier`.
Used in the reverse direction, it reads

```text
T.normalizedJacquet B ρ =
  twist (Jacquet.inverseHalfCharacter (T.leviModulus B)) σ.
```

Both sides act on the same type. `B.JacquetModule ρ` and
`LeviCoinvariants B ρP` both unfold, through the published abbreviations,
to the coinvariants of `ρP` restricted to `B.unipotentRadical F.Carrier`.
The published proof is by extensionality in the Levi element `l` and the quotient
class. By `B.jacquetMk_surjective`, each class is `B.jacquetMk ρ v`.
On the left, `PadicField.TopologicalData.normalizedJacquet_mk` gives

```text
(√δ_P(l))⁻¹ • [ρ(B.leviEmbedding F.Carrier l) v],   δ_P = T.leviModulus B.
```

On the right, the published `twist` multiplies by the unit
`Jacquet.inverseHalfCharacter (T.leviModulus B) l`. Its complex value is
`(√δ_P(l))⁻¹` by `Jacquet.inverseHalfCharacter_apply`. The representative
formula `leviCoinvariants_mk` gives
`σ(l)[v] = [ρP(B.leviInParabolic F.Carrier l) v]`.
The underlying matrix of `B.leviInParabolic F.Carrier l` is
`B.leviEmbedding F.Carrier l` by definition (the published
`leviInParabolic_val` holds by `rfl`), so both sides agree by `rfl`. Thus the
normalization is the actual inverse half-modulus, and the comparison is
proved rather than assumed.

### 2. Finite generation of the unnormalized action

`finite_leviCoinvariants` proves, under `T.topology`, that smoothness and
finite generation of `ρ` over the ambient complex group algebra imply

```text
Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier)) σ.asModule.
```

The published `normalizedJacquetFiniteGeneration` (in
`Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`) gives
finite generation of `(T.normalizedJacquet B ρ).asModule`. Rewriting with
step 1 turns this into finite generation of the twist of `σ`. Then
`Langlands.finite_asModule_twist_iff` (in
`Langlands.Representation.RankinSelberg.WhittakerTypeTwist`) removes the
twist.

### 3. Block scalars in the center of the product Levi

`blockScalarCenter B`, now imported from
[BlockScalarCenter](../../Group/GL/BlockScalarCenter.md) with its original
declaration and namespace unchanged, is the homomorphism

```text
(Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier)
```

obtained from `B.blockScalarLevi F.Carrier` by `MonoidHom.codRestrict`.
Its center membership comes from `Subgroup.mem_center_iff` and
`GeneralLinear.BlockShape.blockScalarLevi_commute`. The coercion of
`blockScalarCenter B a` to `B.Levi F.Carrier` is `B.blockScalarLevi F.Carrier a`
by definition.

### 4. Assembly

`jacquetCenterSpan` introduces the quantifiers, installs `T.topology`, and
applies `Langlands.centralActionSpan_finite` (in
`Langlands.Representation.Smooth.CentralOperatorExpansionProof`) to `σ`
and `blockScalarCenter B`, with:

- admissibility of `σ` from
  `Langlands.Parabolic.isAdmissible_leviCoinvariants` (in
  `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`),
  applied to the admissibility hypothesis of `ρ`;
- finite generation of `σ` from step 2, applied to the smoothness part
  of that admissibility hypothesis and to the finite-generation hypothesis.

The helper concludes that the complex span of `σ (blockScalarCenter B a)`
for all `a` is a finite module over `ℂ`. Its operators are definitionally
the target's operators `σ (B.blockScalarLevi F.Carrier a)`. The goal
`FiniteDimensional ℂ` is the same as `Module.Finite ℂ`. The helper takes no
continuity hypothesis on the center-valued map. The proof works directly on
the actual product-Levi quotient, so it does not pass through the
ambient-subgroup presentation or `jacquetModuleEquiv_leviCoinvariants`.

The check with declaration inspection reports the axioms `propext`,
`Classical.choice` and `Quot.sound`. There is no `sorry` and no new axiom.

## Relation to the literature

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212
(`jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`).
I read Proposition (2.2), its proof, Lemma (2.2.1) and Remark (2.2.5) on
printed pp.181–183 (one-based PDF pages 14–16). No source-specific errata
file for this paper was present in the project or Library notes.

In the application on pp.182–183, the authors take the parabolic `P_i` of
type `(i, r-i)` with radical `V_i`. They cite [7, (3.3.1)] or [2, (3.14)]
to say that the algebra spanned by the action of a central torus `H_i` on
the Jacquet quotient `W/W_i` is finite dimensional. The present theorem is
the corresponding internal statement for the actual unnormalized Jacquet
action, for every block shape and all block-scalar tuples together. It is
not a verbatim theorem of JPS. The Lean proof follows the reason given in
the statement's companion: the Jacquet quotient of admissible finite-type
input is again admissible and finitely generated, so its central operators
lie in a finite-dimensional space of self-intertwiners (this last step is
inside the published `centralActionSpan_finite`). As in Remark (2.2.5),
irreducibility is not used.
