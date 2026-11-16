# Relative norms commute with the conjugation-stable action

This module proves the theorem
`Langlands.NYLL.ClassFormation.relativeNorm_conjugateStableAction`, the proof phase of
M043.007 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m043).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.relativeNorm_conjugateStableActionStatement` applied to
the theorem's parameters:

```lean
theorem relativeNorm_conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm_conjugateStableActionStatement B F E hEF s hF hE a
```

## Target and binders

The theorem has its own binders `{R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]`, `B`, `F`, `E`, `hEF`, `s`, the instance `[Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]`, `hF`, `hE` and `a`, exactly as the published target and the source theorem. The section variables `{G : Type u} [Group G] [TopologicalSpace G]` (section `GroupOnly`) and `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (section `Representation`) are used only by the private helpers, as in the source file `Degree/NormConjugation.lean`.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements`, the target is the proposition

```lean
relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
  conjugateStableAction B F s hF (relativeNorm B F E hEF a)
```

Here `R` is a topological group with continuous multiplication (in the universe-zero type `IntegralRepGroupType`) and `B : Rep ℤ R`. `F` and `E` are closed subgroups (abstract fields) with `E ≤ F`, so `E` is an extension of `F`, and the coset space `F ⧸ E` is finite; here `extensionSubgroup F E hEF` (M004.002) is `E` as a subgroup of `F`. The element `s : R` stabilizes both fields: `hF : conjugateClosedSubgroup F s = F` and `hE : conjugateClosedSubgroup E s = E` (M026.001, `F^s = F` and `E^s = E`). For `a` fixed by `E` (M023.001), `conjugateStableAction B E s hE a` (M043.003) is the right conjugate `a^s`, that is `B.ρ s⁻¹ a.1`, transported along `hE` to an element fixed by `E`. `relativeNorm B F E hEF` (M024.009) is the norm from the elements fixed by `E` to the elements fixed by `F`: it sends `b` to the sum of `B.ρ k b.1` over a system of representatives `k` of the cosets of `F ⧸ E`. The target says that the norm of the conjugate is the conjugate of the norm: `N_{E/F}(a^s) = N_{E/F}(a)^s`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements`, which defines the target and imports `conjugateStableAction` (M043.003), `conjugateFixedElement` (M026.003), `conjugateClosedSubgroup` (M026.001), the proved `conjugateClosedSubgroup_mem` (M026.002), `ambientFixedAddSubgroup` (M023.001), `extensionSubgroup` (M004.002), `relativeCosetAction` (M024.001), `relativeNormValue` (M024.005) and `relativeNorm` (M024.009);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.SubgroupEquiv.Definitions`, the published definition `conjugateSubgroupEquiv` (M035.002): conjugation `k ↦ s⁻¹ * k * s` as a multiplicative equivalence from `K.toSubgroup` onto `(conjugateClosedSubgroup K s).toSubgroup`.

The module opens `KummerTheory` (for `ambientFixedAddSubgroup`) and `CyclicCohomology` (for `extensionSubgroup`) and `open scoped BigOperators`, as the source files do; the source's `open CategoryTheory` and the universe `v` of `UniversalNormDescent.lean` are not needed. The universe `u` of the source file `Degree/NormConjugation.lean` is kept for the section `GroupOnly`.

The Library has no proofs of the source theorems M035.001, M035.004, M035.006, M035.010, M035.011, M035.012, M043.004 and M043.005 and no definition M035.005, and of the source lemmas used by their proofs, `relativeCosetAction_mk` (M024.002) is published with the Prop-valued type `relativeCosetAction_mkStatement`, while `conjugateFixedElement_coe` (M026.004) and `relativeNorm_apply_coe` (M024.010) have only their `...Statement` propositions, and no proofs, in the Library at this workspace's base commit `72480b70c88adff84a438bd7029d64ee3977469c`. The module therefore ports the helpers it needs as private declarations, and replaces rewrites with those lemmas by definitional `change` steps, as described below.

## Implemented proof

The module first proves private ports of the source helpers, each with its source statement:

1. `conjugateClosedSubgroup_mono` (M035.001): if `L ≤ K` then `L^s ≤ K^s`. For `x ∈ L^s`, `conjugateClosedSubgroup_mem` (M026.002) gives `s * x * s⁻¹ ∈ L`, hence `∈ K`, hence `x ∈ K^s` by the same theorem in the other direction.
2. `map_extensionSubgroup_conjugate` (M035.004): the image of `extensionSubgroup K L hLK` under `conjugateSubgroupEquiv K s` is `extensionSubgroup K^s L^s _`. Forward: for `k ∈ L`, its image `s⁻¹ * k * s` lies in `L^s` by M026.002, since `s * (s⁻¹ * k * s) * s⁻¹ = k`. Backward: an element `x` of `K^s` lying in `L^s` is the image of `s * x * s⁻¹`, which lies in `L` by M026.002.
3. `relativeConjugateCosetEquiv` (M035.005, a private noncomputable definition): the bijection `K ⧸ L ≃ K^s ⧸ L^s` of left coset spaces induced by `conjugateSubgroupEquiv K s`, by `Quotient.congr`; compatibility with the coset relations `x⁻¹ * y ∈ H` follows from step 2 and the fact that the equivalence is multiplicative. Its source proof is unchanged.
4. `relativeConjugateCosetEquiv_mk` (M035.006): the bijection sends the class of `k` to the class of `s⁻¹ * k * s`, by `rfl`.
5. `finite_conjugateExtension` (M035.010): `K^s ⧸ L^s` is finite when `K ⧸ L` is, by `Finite.of_equiv` along step 3.
6. `relativeCosetAction_conjugate` (source-private M035.011): for every coset `q` of `K ⧸ L`, the coset action (M024.001) of the conjugate `a^s` at the conjugate coset is `B.ρ s⁻¹` of the coset action of `a` at `q`. By quotient induction and step 4, with `change` for the definitional values of the coset action at a representative and of `conjugateFixedElement`, it is `ρ(s⁻¹ k s) ρ(s⁻¹) a = ρ(s⁻¹) ρ(k) a`, which follows from `map_mul` of `ρ` and `s⁻¹ * k * s * s⁻¹ = s⁻¹ * k`.
7. `relativeNorm_conjugate_apply` (M035.012): `N_{L^s/K^s}(a^s) = N_{L/K}(a)^s`. After `Subtype.ext`, a `change` states both sides as the defining sums over the cosets (`relativeNormValue`). The `Fintype` instance on `K^s ⧸ L^s` is replaced by the one transported along step 3 (`Subsingleton.elim`); the sum is reindexed along step 3 (`Equiv.sum_comp`), each term is rewritten by step 6, and `map_sum` pulls `B.ρ s⁻¹` out of the sum.
8. `transport_fixed_coe` (M043.004): transport of a fixed element along an equality of fields `F' = F` does not change the underlying element; by `cases` and `rfl`.
9. `relativeNorm_transport_coe` (M043.005): for equalities `F' = F` and `E' = E`, the norm `N_{E/F}` of the transport of `a` has the same underlying element as `N_{E'/F'}(a)`; by `cases` on both equalities and `rfl`.

The main proof, after `show` states the published proposition unfolded, is the source proof. Let `hConj` be step 1 for `E ≤ F` and register the finiteness of `F^s ⧸ E^s` (step 5). Both sides lie in a subtype, so `Subtype.ext` reduces the goal to their underlying elements, and a calculation shows:

- the norm of `conjugateStableAction B E s hE a = hE ▸ a^s` has the underlying element of `N_{E^s/F^s}(a^s)` (step 9, with `F' = F^s`, `E' = E^s`);
- this is the underlying element of `N_{E/F}(a)^s` (step 7);
- this is the underlying element of `conjugateStableAction B F s hF (N_{E/F}(a)) = hF ▸ N_{E/F}(a)^s` (step 8).

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings; the inspected theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passages are in two files.

In [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 80–149](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean#L80-L149): the private helpers `transport_fixed_coe` (M043.004) at lines 80–86 and `relativeNorm_transport_coe` (M043.005) at lines 88–102, and the docstring at lines 115–116 and the theorem at lines 117–149. They lie in `namespace ClassFormation` (line 20), with `open KummerTheory` (line 22) and `open CyclicCohomology` (line 23), after `universe u v` (line 18), in its `noncomputable section` (line 27) with `open CategoryTheory` (line 29) and `open scoped BigOperators` (line 30). The source passages are:

```lean
private theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl
```

```lean
private theorem relativeNorm_transport_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ extensionSubgroup F' E' hE'F')]
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) : B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') : B.V) := by
  cases hF
  cases hE
  rfl
```

```lean
/-- Relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
theorem relativeNorm_conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a) := by
  let hConj := conjugateClosedSubgroup_mono hEF s
  let : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup F s)
        (conjugateClosedSubgroup E s) hConj) :=
    finite_conjugateExtension F E hEF s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a) :
        ambientFixedAddSubgroup B F) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a) :
            ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := by
      exact relativeNorm_transport_coe B
        (conjugateClosedSubgroup F s) (conjugateClosedSubgroup E s) F E
        hF hE hConj hEF (conjugateFixedElement B E s a)
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B F) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm
```

In [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`, lines 37–297](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean#L37-L297): `conjugateClosedSubgroup_mono` (M035.001) at lines 37–46, `map_extensionSubgroup_conjugate` (M035.004) at lines 79–97, `relativeConjugateCosetEquiv` (M035.005) at lines 101–132, `relativeConjugateCosetEquiv_mk` (M035.006) at lines 139–145 (with `@[simp]` at line 138), `finite_conjugateExtension` (M035.010) at lines 194–205, `relativeCosetAction_conjugate` (M035.011) at lines 215–241 and `relativeNorm_conjugate_apply` (M035.012) at lines 246–297; their docstrings are at lines 36, 77–78, 99–100, 134–137, 193, 214 and 243–245. They lie in `namespace ClassFormation` (line 18), with `open KummerTheory` (line 20) and `open CyclicCohomology` (line 22), in its `noncomputable section` (line 26) with `open scoped BigOperators` (line 28) and `universe u` (line 30); the first five in `section GroupOnly` (lines 32–207) with `variable {G : Type u} [Group G] [TopologicalSpace G]` (line 34), the last two in `section Representation` (lines 209–299) with the comment at line 211 and `variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 212). The source passages are:

```lean
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  rw [conjugateClosedSubgroup_mem] at hx ⊢
  exact hLK hx
```

```lean
theorem map_extensionSubgroup_conjugate [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (extensionSubgroup K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    rw [conjugateClosedSubgroup_mem]
    simpa [mul_assoc] using hk
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · change s * x.1 * s⁻¹ ∈ L.toSubgroup
      exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · exact (conjugateSubgroupEquiv K s).apply_symm_apply x
```

```lean
noncomputable def relativeConjugateCosetEquiv [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := extensionSubgroup K L hLK
    let Hs := extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
    have hmap : H.map e.toMonoidHom = Hs :=
      map_extensionSubgroup_conjugate K L hLK s
    change x⁻¹ * y ∈ H ↔ (e x)⁻¹ * e y ∈ Hs
    rw [← hmap]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      change e (x⁻¹ * y) = (e x)⁻¹ * e y
      rw [map_mul, map_inv]
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        change e z = (e x)⁻¹ * e y at hez
        simpa only [map_mul, map_inv] using hez
      rw [← heq]
      exact hz)
```

```lean
theorem relativeConjugateCosetEquiv_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl
```

```lean
theorem finite_conjugateExtension [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (relativeConjugateCosetEquiv K L hLK s)
```

```lean
private theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L hLK s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeConjugateCosetEquiv_mk, relativeCosetAction_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) =
        A.ρ ((s⁻¹ * k.1 * s) * s⁻¹) a.1 := by
      have hm := congrArg (fun φ => φ a.1)
        (map_mul A.ρ (s⁻¹ * k.1 * s) s⁻¹)
      exact hm.symm
    _ = A.ρ (s⁻¹ * k.1) a.1 := by
      congr 2
      simp [mul_assoc]
    _ = A.ρ s⁻¹ (A.ρ k.1 a.1) := by
      exact congrArg (fun φ => φ a.1) (map_mul A.ρ s⁻¹ k.1)
```

```lean
theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e := relativeConjugateCosetEquiv K L hLK s
  let conjugateFintype : Fintype
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) :=
    Fintype.ofEquiv (K.toSubgroup ⧸ extensionSubgroup K L hLK) e
  have hconjugateFintype : Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) = conjugateFintype :=
    Subsingleton.elim _ _
  apply Subtype.ext
  simp only [relativeNorm_apply_coe, relativeNormValue,
    conjugateFixedElement_coe]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := by
          exact (e.sum_comp fun q =>
            relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a) q).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact relativeCosetAction_conjugate A K L hLK s a q
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]
```

The complete original files are retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
(SHA-256 `5ac5450e039760193ab008f2bed81158a543d2d9982515cd2e376baeadfe1284`) and
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`
(SHA-256 `2ec220a4a18e54914548db7f0ecea669819fe5b6f8b421c13e996dd6ceed4602`).

Modifications by Worker 739 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `relativeNorm_conjugateStableActionStatement B F E hEF s hF hE a` as its type, and begin the proof with `show` stating it unfolded; the rest of the main proof is the source proof;
- port the nine helpers listed under *Implemented proof* as private declarations of this module, with their source names, binders, statements and, except as listed next, proofs, in source order within each file (the `Degree/NormConjugation.lean` helpers first, in their source sections `GroupOnly` and `Representation`);
- in `conjugateClosedSubgroup_mono`, replace `rw [conjugateClosedSubgroup_mem] at hx ⊢` and `exact hLK hx` by `refine (conjugateClosedSubgroup_mem K s x).2 ?_` and `exact hLK ((conjugateClosedSubgroup_mem L s x).1 hx)`, and in `map_extensionSubgroup_conjugate` replace `rw [conjugateClosedSubgroup_mem]` by `refine (conjugateClosedSubgroup_mem L s _).2 ?_`, because the published M026.002 has the Prop-valued type `conjugateClosedSubgroup_memStatement`, which `rw` does not use as an equation;
- in `map_extensionSubgroup_conjugate`, replace `simpa [mul_assoc] using hk`, which in this environment leaves `hk` as membership in `extensionSubgroup K L hLK` instead of `↑k ∈ L` and fails, by reading `hk` as `(k : G) ∈ L.toSubgroup` (definitionally), rewriting the goal with `s * (s⁻¹ * k.1 * s) * s⁻¹ = k.1` (proved by `simp [mul_assoc]`) and `exact`;
- in `relativeCosetAction_conjugate`, keep `rw [relativeConjugateCosetEquiv_mk]` and replace the rewrites `relativeCosetAction_mk, relativeCosetAction_mk, conjugateFixedElement_coe` by `change A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) = A.ρ s⁻¹ (A.ρ k.1 a.1)`, the goal those rewrites produce, because `relativeCosetAction_mk` is published with the type `relativeCosetAction_mkStatement` and `conjugateFixedElement_coe` is not proved in the Library at the base commit; both are `rfl` in the source;
- in `relativeNorm_conjugate_apply`, replace `simp only [relativeNorm_apply_coe, relativeNormValue, conjugateFixedElement_coe]` by a `change` to the goal it produces, the defining sum of `relativeNormValue` on the left (with its `Fintype.ofFinite` instance) and `A.ρ s⁻¹` of the defining sum on the right, because `relativeNorm_apply_coe` and `conjugateFixedElement_coe` are not proved in the Library at the base commit; both are `rfl` in the source;
- omit the docstrings of the ported helpers, the `@[simp]` attribute of `relativeConjugateCosetEquiv_mk`, the universe `v`, `open CategoryTheory` and all other source declarations of both files.

The name, binders, docstring and proof steps of the main theorem are the source's. The retained originals belong to registered source
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
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M043.007. Its private helpers are not exported and do not
discharge the M035 or M043.004–M043.005 targets. It discharges no host
class-formation, cup, transfer, Tate or reciprocity target.
