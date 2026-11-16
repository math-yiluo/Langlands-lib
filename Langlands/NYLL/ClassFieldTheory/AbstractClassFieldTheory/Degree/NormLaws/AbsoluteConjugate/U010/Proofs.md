# The absolute norm commutes with conjugation

This module proves the theorem
`Langlands.NYLL.ClassFormation.relativeNorm_absoluteConjugate_apply`, the proof phase of
M026.010 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m026).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.relativeNorm_absoluteConjugate_applyStatement` applied to the
theorem's parameters:

```lean
theorem relativeNorm_absoluteConjugate_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm_absoluteConjugate_applyStatement A K σ a
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, where `IntegralRepGroupType` is the universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires. The theorem takes `[ContinuousMul G]`, `A`, `K`, `σ`, the finiteness instance and `a`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements`, the target is the proposition

```lean
letI : Finite
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))) :=
  Finite.of_equiv
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K
        (le_baseField K))
    (absoluteConjugateCosetEquiv K σ).symm
((relativeNorm A (baseField G)
    (conjugateClosedSubgroup K σ)
    (le_baseField (conjugateClosedSubgroup K σ))
    (conjugateFixedElement A K σ a) :
  ambientFixedAddSubgroup A (baseField G)) : A.V) =
  A.ρ σ⁻¹
    ((relativeNorm A (baseField G) K
      (le_baseField K) a :
      ambientFixedAddSubgroup A (baseField G)) : A.V)
```

Here `A : Rep ℤ G`, `K : ClosedSubgroup G` has finite index in `G` (the instance binder on the coset space of `K` in `(baseField G).toSubgroup`, the whole group (M010.003), with `le_baseField` (M010.005) the inclusion of `K`), `σ : G` and `a : ambientFixedAddSubgroup A K`; `ambientFixedAddSubgroup A K` (M023.001) is the additive subgroup of `A.V` of the elements fixed by every element of `K`. `conjugateClosedSubgroup K σ` (M026.001) is the conjugate abstract field `K^σ`, whose subgroup is `σ⁻¹ K σ` (the construction writes the action on the right), and `conjugateFixedElement A K σ a` (M026.003) is the right conjugate `a^σ`, the element `A.ρ σ⁻¹ a.1` regarded as fixed by `K^σ`. `relativeNorm A (baseField G) K _` (M024.009) is the absolute norm from `A_K` to `A_G`, the sum over the cosets `gK` of `G/K` of `A.ρ g a` (`relativeCosetAction`, M024.001; the value is `relativeNormValue`, M024.005). The `letI` makes the coset space of `K^σ` finite through the equivalence `absoluteConjugateCosetEquiv K σ` (M026.007) with the coset space of `K`. The target says that the absolute norm of `a^σ` is `A.ρ σ⁻¹` applied to the absolute norm of `a`, that is, `N(a^σ) = N(a)^σ`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements`, which defines the target and imports `absoluteConjugateCosetEquiv` (M026.007), `conjugateFixedElement` (M026.003), `relativeNorm` (M024.009) with `relativeNormValue` (M024.005) and `relativeCosetAction` (M024.001), `baseField` (M010.003) and `le_baseField` (M010.005).

The module opens `KummerTheory` and `CyclicCohomology`, as the source does, for `ambientFixedAddSubgroup` and `extensionSubgroup`, and `open scoped BigOperators` for the `∑` notation; the source's scoped `Pointwise` is not needed.

## Implemented proof

The module first proves the private source helper M026.009 `relativeCosetAction_absoluteConjugate` as a private theorem with the source statement: for a coset `q` of `K^σ`, the action of `q` on `a^σ` is `A.ρ σ⁻¹` of the action of the coset `absoluteConjugateCosetEquiv K σ q` of `K` on `a`. After `Quotient.inductionOn'` reduces to a representative `x`, the source rewrites with `relativeCosetAction_mk`, `absoluteConjugateCosetEquiv_mk` and `conjugateFixedElement_coe`; the port states the resulting goal `A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1)` with `change`, since all three rewrites hold by definition (the first is published with a `...Statement` type, which `rw` cannot use, and the other two are M026.008 and M026.004, whose proofs are not yet in the Library). The source `calc` then follows unchanged: both sides equal `A.ρ (x.1 * σ⁻¹) a.1` by `map_mul` and group arithmetic.

The main theorem unfolds the published proposition and introduces, as the source does, the `Fintype` instance on the coset space of `K`, the `Fintype` instance `conjugateFintype` on the coset space of `K^σ` transported along `absoluteConjugateCosetEquiv K σ`, and the equality `hconjugateFintype` of the latter with `Fintype.ofFinite` (by `Subsingleton.elim`). The source then unfolds both norms with `simp only [relativeNorm_apply_coe, relativeNormValue]`. The port uses instead a local fact `hcoe`, proved by `rfl`: for every closed subgroup `L'` of finite index and `b : ambientFixedAddSubgroup A L'`, the underlying element of `relativeNorm A (baseField G) L' (le_baseField L') b` is the coset sum `∑ q, relativeCosetAction A (baseField G) L' (le_baseField L') b q` over `Fintype.ofFinite`. It is stated for the inclusion proof `le_baseField` because the published `le_baseField` has the type `le_baseFieldStatement L'`, and `simp` cannot instantiate the general lemmas (whose inclusion argument has type `L' ≤ baseField G`) with it; the source lemma M024.010 `relativeNorm_apply_coe` is also not in the Library. After `simp only [hcoe]` and `rw [hconjugateFintype]`, the source `calc` follows unchanged: `Finset.sum_congr` with the helper rewrites each summand, `map_sum` pulls `A.ρ σ⁻¹` out of the sum, and `Equiv.sum_comp` reindexes the sum along `absoluteConjugateCosetEquiv K σ`. The development check reported only the axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, lines 145–245](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean#L145-L245):
the private helper `relativeCosetAction_absoluteConjugate` (M026.009) at lines 145–171, the docstring at lines 173–176 and the theorem at lines 177–245. It lies in `namespace ClassFormation` (line 16), with `open KummerTheory` (line 18) and `open CyclicCohomology` (line 20), its `noncomputable section` (line 24), `open scoped BigOperators Pointwise` (line 26) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29). The source is:

```lean
private theorem relativeCosetAction_absoluteConjugate [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K)
    (q : (baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))) :
    relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [relativeCosetAction_mk, absoluteConjugateCosetEquiv_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * (σ * x.1 * σ⁻¹)) a.1 := by simp [mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1) := by
      rw [map_mul]
      rfl

/-- conjugation compatibility of normalized valuations: the absolute norm commutes with conjugation.

The construction writes the action on fields and elements on the right.  Thus the
left action used by `Rep` realizes `a^σ` as `ρ(σ⁻¹)a`. -/
theorem relativeNorm_absoluteConjugate_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (conjugateClosedSubgroup K σ)
            (le_baseField (conjugateClosedSubgroup K σ))) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K
            (le_baseField K))
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V) := by
  let := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K
        (le_baseField K))
  let conjugateFintype : Fintype
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) :=
    Fintype.ofEquiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))
      (absoluteConjugateCosetEquiv K σ).symm
  have hconjugateFintype : Fintype.ofFinite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) = conjugateFintype :=
    Subsingleton.elim _ _
  simp only [relativeNorm_apply_coe, relativeNormValue]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      ∑ q, A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            apply Finset.sum_congr rfl
            intro q _
            exact relativeCosetAction_absoluteConjugate A K σ a q
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            rw [map_sum]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a q) := by
            rw [(absoluteConjugateCosetEquiv K σ).sum_comp]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`;
its SHA-256 is `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- port the private helper `relativeCosetAction_absoluteConjugate` (M026.009) as a private theorem of this module, with its source statement, replacing its source `rw [relativeCosetAction_mk, absoluteConjugateCosetEquiv_mk, relativeCosetAction_mk, conjugateFixedElement_coe]` by a `change` to the resulting goal;
- give the main theorem the published proposition `relativeNorm_absoluteConjugate_applyStatement A K σ a` as its type and begin the proof with `unfold` of it;
- replace `simp only [relativeNorm_apply_coe, relativeNormValue]` by `simp only [hcoe]` with the local `rfl` fact `hcoe` described above;
- omit the source's scoped `Pointwise` and all other source declarations.

The names, docstring, binders, the `Fintype` set-up and both `calc` blocks are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M026.010. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
