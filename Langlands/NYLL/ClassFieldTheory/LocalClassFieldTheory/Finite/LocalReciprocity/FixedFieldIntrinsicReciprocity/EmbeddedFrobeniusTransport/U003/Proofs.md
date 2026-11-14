# Continuity of the embedded intrinsic-to-ambient base equivalence

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuousStatement`
(source row M281.003) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its imports are
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U002.Statements`
(the statement) and
`Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Proofs`
(the published theorem
`Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongr`, source row
M001.001). These published modules and everything they import stay unchanged.

## Target

Write `Ω := SeparableClosure K`. For fields `K F : Type` with
`[Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]`, a
`K`-algebra embedding `i : F →ₐ[K] Ω` (making `Ω` an `F`-algebra by
`i.toRingHom.toAlgebra`) and an `F`-algebra equivalence
`e : SeparableClosure F ≃ₐ[F] Ω`, the statement asserts

```lean
Continuous (intrinsicBaseEquivAmbientEmbeddedField K F i e)
```

for the subspace topologies on `(intrinsicAbstractBase F).toSubgroup` and on
`(closedFixingSubgroup K Ω i.fieldRange).toSubgroup` induced by the Krull
topologies on `Gal(SeparableClosure F / F)` and `Gal(Ω / K)`.

## Implemented proof

```lean
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e
  have : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  have : Algebra.IsAlgebraic F (SeparableClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) F
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  refine Continuous.congr
    ((continuous_restrictScalarsHom K F (SeparableClosure K)).comp
      ((AlgebraicNumberTheory.continuous_algEquiv_autCongr e).comp
        continuous_subtype_val)) ?_
  intro tau
  apply AlgEquiv.ext
  intro x
  -- local copies of H₀, F₀, FiniteDimensional K F₀, the separability and
  -- IsSepClosure instances, the F₀-algebra on SeparableClosure F₀ and e₀
  ...
  show e (tau.1 (e.symm x)) =
    e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x))))))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
```

1. After introducing the binders, the `F`-algebra structure on `Ω` induced
   by `i` is installed as in the statement. Because `i` is a `K`-algebra
   map, `algebraMap K Ω = i ∘ algebraMap K F`, which gives the tower
   `IsScalarTower K F Ω`; and `Ω` is algebraic over `K`, hence over `F`
   (Mathlib's `Algebra.IsAlgebraic.tower_top`).
2. As for M281.002, `Topology.IsInducing.subtypeVal.continuous_iff` reduces
   the goal to continuity of the underlying automorphisms in `Gal(Ω / K)`, and
   the candidate continuous map is the composite of `Subtype.val`,
   `AlgEquiv.autCongr e : Gal(SeparableClosure F / F) ≃* Gal(Ω / F)` and
   `AlgEquiv.restrictScalarsHom K` for the tower of step 1. It is continuous
   by `continuous_subtype_val`, the published
   `Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongr` and the
   private helper below. `Continuous.congr` leaves the pointwise equality.
3. For each `tau`, `AlgEquiv.ext` reduces this to values at `x : Ω`. The
   composite gives `e (tau.1 (e.symm x))` by definition.
   The proof rebuilds, as local `let` bindings, the data that the body of
   `intrinsicBaseEquivAmbientEmbeddedField` (published in
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`) constructs:
   `H₀ := closedFixingSubgroup K Ω i.fieldRange`, its fixed field
   `F₀ := abstractFixedField K Ω H₀`, the instance `FiniteDimensional K F₀`
   (proved exactly as in that definition body, by transporting along
   `AlgEquiv.ofInjectiveField i` and the equality
   `InfiniteGalois.fixedField_fixingSubgroup i.fieldRange`), the separability of
   `Ω` over `F₀`, the `IsSepClosure F₀ Ω` instance, the standard `F₀`-algebra
   structure on `SeparableClosure F₀` and
   `e₀ := IsSepClosure.equiv F₀ (SeparableClosure F₀) Ω`.
   Unfolding the definitions, the value of
   `intrinsicBaseEquivAmbientEmbeddedField K F i e tau` at `x : Ω` is
   definitionally `e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x))))))`:
   `intrinsicAbstractBaseEquivAbsolute F` sends `tau` to `tau.1`; the
   conjugation `theta` of the definition body, through
   `c := e` followed by `e₀⁻¹`, sends it to `y ↦ e₀⁻¹ (e (tau.1 (e⁻¹ (e₀ y))))`;
   `(intrinsicAbstractBaseEquivAbsolute F₀).symm` only wraps this automorphism
   in a subtype; and `intrinsicBaseEquivAmbientFixedField K H e₀` conjugates by
   `e₀` (via `AlgEquiv.autCongr e₀`) and then applies
   `(abstractSubgroupEquivGaloisGroup K Ω H₀).symm`, which does not change the
   underlying function.
   The `show` step checks both identifications by definitional unfolding.
4. Two rewrites with Mathlib's `AlgEquiv.apply_symm_apply`
   (`e₀ (e₀.symm y) = y`) close the goal.

The proof does not use M281.002 or M273.007/M273.008. No hypothesis, global
instance or public auxiliary declaration is added; the tower and
algebraicity facts of step 1 are local `have`s.

## Private helper lemma

```lean
private theorem continuous_restrictScalarsHom
    (K P L : Type) [Field K] [Field P] [Field L]
    [Algebra K P] [Algebra P L] [Algebra K L]
    [IsScalarTower K P L] [Algebra.IsAlgebraic P L] :
    Continuous (AlgEquiv.restrictScalarsHom K : Gal(L/P) →* Gal(L/K))
```

For a scalar tower `K → P → L` with `L` algebraic over `P`, restricting
scalars from `Gal(L / P)` to `Gal(L / K)` is continuous for the Krull
topologies. Mathlib has no such lemma. The Library has it only as the
private theorem `continuous_restrictScalars` in
`Langlands/Galois/AbsoluteTopologyProof.lean` (lines 14–34, namespace
`Langlands.GaloisRepresentation`), which cannot be used from another file.
The helper copies that proof verbatim; the only changes are the name, the
universe (`Type` instead of `Type u`, `Type v`, `Type w`) and line breaks. The proof: a
group homomorphism is continuous if it is continuous at `1`; a neighbourhood
of `1` in `Gal(L / K)` contains the fixing subgroup of some
finite-dimensional intermediate field `E` of `L / K`; `E` is generated over
`K` by a finite set `s` (`essFiniteType_iff`); the intermediate field of
`L / P` generated by `s` is finite-dimensional because `L` is algebraic over
`P`, so its fixing subgroup is a neighbourhood of `1` in `Gal(L / P)`; and an
automorphism fixing it fixes `s`, hence (after restricting scalars) fixes
`E = K(s)` (`forall_mem_adjoin_smul_eq_self_iff`).

The helper is private to this module and states only Mathlib notions.

## Relation to the original proof

The original proof (lines 165–285) rebuilds the data of the definition body,
proves that the conjugation `theta : Gal(SeparableClosure F / F) ≃*
Gal(SeparableClosure F₀ / F₀)` is continuous with the source lemma
`RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous`
(source row M235.009), and composes it with M281.002 for `e₀` and a continuous
lift into the intrinsic base. M235.009 is not in the Library, and the source's
instance `FiniteDimensional K F₀` comes from the unproved
`abstractFixedField_finiteDimensional` (M099.005). The implemented proof
instead identifies the map with `tau ↦ (AlgEquiv.autCongr e tau.1).restrictScalars K`
and uses the same continuity argument as M281.002.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean>),
SHA-256 `d8403d819db83b085b6fad6144c82340f414f44f5675e495b83e79ffd28ee1a1`.
The theorem `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous`
has its docstring at lines 151–152, its signature at lines 153–164 and its proof
at lines 165–285. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous` | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuousStatement` (U002 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as described above and placed in its own module `U003/Proofs`; the source imports are replaced by the two published imports; all other
declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M281.003 proof.
