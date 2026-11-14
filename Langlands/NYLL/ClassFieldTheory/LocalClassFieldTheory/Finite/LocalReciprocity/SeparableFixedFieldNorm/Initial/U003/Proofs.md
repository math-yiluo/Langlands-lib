# NYLL M165.003: the coset restriction map to embeddings is surjective

`Langlands.NYLL.PortInternal.M165.d003` proves exactly
`Langlands.NYLL.PortInternal.M165.d003Statement K Ω E`. Its binders are those
of the target, in the same order and with the same binder kinds: explicit
`(K Ω : Type)`, instance-implicit `[Field K] [Field Ω] [Algebra K Ω]
[IsGalois K Ω] [IsSepClosed Ω]`, explicit `(E : IntermediateField K Ω)`, and
instance-implicit `[FiniteDimensional K E] [Algebra.IsSeparable K E]`.

The target says that the published map
`Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom K Ω E` is
surjective. That map sends the left coset `σ · Gal(Ω / E)` of an element `σ` of
the subgroup `(closedFixingSubgroup K Ω ⊥).toSubgroup` of `Gal(Ω / K)` to the
`K`-algebra map `σ|_E : E →ₐ[K] Ω`. So every `K`-embedding of the finite
separable intermediate field `E` into the separably closed Galois extension
`Ω` is the restriction of an automorphism of `Ω / K`.

## Implemented proof

The proof is the source proof, unchanged.

1. Fix `f : E →ₐ[K] Ω`. Since `Ω / K` is separable (part of `IsGalois`),
   `Algebra.isSeparable_tower_top_of_isSeparable K E Ω` shows that `Ω / E` is
   separable.
2. `IsSepClosed.surjective_domRestrict_of_isSeparable` with `L := E`,
   `M := Ω` and `E := Ω` uses that `Ω` is separably closed and `Ω / E` is
   separable. It gives `φ : Ω →ₐ[K] Ω` with `φ.domRestrict E = f`.
3. `Ω / K` is normal, hence algebraic (`Normal.toIsAlgebraic`).
   `Algebra.IsAlgebraic.algHom_bijective₂ φ (AlgHom.id K Ω)` shows `φ` is
   bijective, and `AlgEquiv.ofBijective` turns it into `σ : Ω ≃ₐ[K] Ω`.
4. Membership of `σ` in `(closedFixingSubgroup K Ω ⊥).toSubgroup` reduces by
   `change` to membership in `(⊥ : IntermediateField K Ω).fixingSubgroup`.
   That subgroup is `⊤` by `IntermediateField.fixingSubgroup_bot`, and
   `Subgroup.mem_top` concludes.
5. The coset `QuotientGroup.mk ⟨σ, hσ⟩` is the preimage. By `AlgHom.ext`, it
   suffices that `φ x = f x` for every `x : E`. Both sides of this are
   reached by `change` from the defining `Quotient.liftOn'` of
   `baseFixingCosetToAlgHom` and from `φ.domRestrict E = f` evaluated at `x`.

The theorem depends only on the target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Statements`
(and through it the published `Definitions` module) and on Mathlib:
`Algebra.isSeparable_tower_top_of_isSeparable`,
`IsSepClosed.surjective_domRestrict_of_isSeparable`,
`Normal.toIsAlgebraic`, `Algebra.IsAlgebraic.algHom_bijective₂`,
`AlgEquiv.ofBijective`, `IntermediateField.fixingSubgroup_bot`,
`Subgroup.mem_top`, `QuotientGroup.mk` and `AlgHom.ext`. No other Library
result and no helper declaration is used.

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) the module compiled with
zero errors and zero warnings. Inspection of the theorem reports no level
parameters and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not acceptance.

## Source correspondence and modification record

Adapted by Worker 368 on 14 November 2026 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`
(SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`):
the private theorem `LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective`
at lines 91–117 (statement at lines 91–93), with the section variables at
lines 36–37 and 41. The
registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective` (M165.003) | `Langlands.NYLL.PortInternal.M165.d003` (this proof) |

Modifications:

- the private theorem is published under the name reserved by the port plan,
  `Langlands.NYLL.PortInternal.M165.d003`, declared with `_root_` inside
  `namespace Langlands.NYLL.LocalClassFieldTheory` so that
  `baseFixingCosetToAlgHom` and `closedFixingSubgroup` (through
  `open RamificationTheory`) resolve to the published definitions;
- the section variables that the source theorem takes are written as explicit
  binders, and its conclusion is expressed as the published target
  `d003Statement K Ω E`, which unfolds to the source conclusion
  `Function.Surjective (baseFixingCosetToAlgHom K Ω E)`, so `intro f` applies
  directly;
- the NYLL imports are replaced by the published target module; the source's
  `open LocalFieldTheory`, `ClassFormation`, `KummerTheory` and
  `BigOperators` are dropped, keeping `open RamificationTheory
  CyclicCohomology` as in the published `Definitions` module;
- a docstring is added; the tactic proof is unchanged.

The original copyright and author header is retained. The file remains under
Apache-2.0; the license and notice are the published `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`),
reused unchanged. This support proof discharges no host class-formation,
cohomology or reciprocity target.
