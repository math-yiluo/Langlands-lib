# The Herbrand quotient of a finite module is one (finiteness form)

This module proves the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_eq_one_of_finite_module`, the proof phase of
M119.014 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m119).
Its type is the published proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_eq_one_of_finite_moduleStatement` applied to the
theorem's parameters:

```lean
theorem herbrandQuotient_eq_one_of_finite_module
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient_eq_one_of_finite_moduleStatement (G := G) (A := A) σ hgen
```

## Target and binders

The section variables are those of the published statement module and the source: `{G A B C : Type}`, `[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and the actions of `G` on `A`, `B` and `C`, in `namespace ProfiniteCohomology.Herbrand`; only those on which the theorem depends are included. The theorem takes `σ`, `hgen` and `[Finite A]`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`, the target is the proposition

```lean
herbrandQuotient (G := G) (A := A) σ = 1
```

Here `G : Type` is a finite group acting on the commutative group `A : Type` by multiplicative automorphisms, `σ : G`, and `HerbrandH0 G A` (M113.028) and `HerbrandHMinusOne G A σ` (M113.029) are the low-degree Tate quotients `A^G / N_G A` and `ker N_G / I_G A` (with `I_G A` the image of `a ↦ a^(σ-1)`). `herbrandQuotient (G := G) (A := A) σ` (M118.001) is the rational number `#H⁰ / #H⁻¹`, defined under finiteness instances for both quotients. For a generator `σ` of `G` (`hgen`) and a finite module `A`, the target says that the Herbrand quotient is `1`; the hypothesis `hgen` is used by the proof. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`, which defines the target and imports `herbrandQuotient` (M118.001) through the published `Core.Definitions` module, and `HerbrandH0`, `HerbrandHMinusOne` and the subgroups of M113 with their finiteness instances;
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U005.Proofs`, the published proof of M113.005 `fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one` (an element killed by `σ - 1`, for a generator `σ`, is fixed by `G`);
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U006.Proofs`, the published proof of M113.006 `monoidHom_card_eq_card_ker_mul_card_range` (`#X = #ker f · #range f` for a finite group `X`);
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U008.Proofs`, the published proof of M113.008 `card_subgroupOf_eq_card` (`#(H.subgroupOf K) = #H` for `H ≤ K`);
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U066.Proofs`, the published proof of M113.066 `tateNorm_sigmaMinusOne_eq_one` (`N_G(a^(σ-1)) = 1`);
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U068.Proofs`, the published proof of M113.068 `smul_tateNorm_eq` (norms are fixed by `G`). These five have universe-polymorphic `...Statement` types that quantify over all their arguments; the module applies them to arguments directly.

The module opens no namespace; the source's `open CategoryTheory` and its `universe uG uA` are not needed.

## Implemented proof

The source proof is the term `herbrandQuotient_finite_module_eq_one σ hgen`, an application of M118.004, whose proof is not yet in the Library. The port uses instead the source proof of M118.004 (`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`, lines 63–67), which applies M118.003 and M113.109; these and the chain behind M113.109 are proved as private copies stated in this module's section context, where the groups live in `Type`.

The module first proves, as private theorems with the source statements and source proofs of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, the chain of source results leading to M113.109 `herbrand_finite_module_card_eq`, none of whose proofs is yet in the Library (M113.109 is routed to Task `7bed7a2e`): M113.024 (for a generator `σ`, the kernel of `a ↦ a^(σ-1)` is `A^G`, from M113.005; the source's `by simpa using ha`, which relies on the unpublished simp lemma M113.019 `sigmaMinusOneHom_apply`, is replaced by `MonoidHom.mem_ker.mp ha`, accepted because `sigmaMinusOneHom σ a` is `sigmaMinusOne G A σ a` by definition); M113.025 and M113.026 (`#A = #ker N · #N A` and `#A = #A^G · #I_G A`, from M113.006 and M113.024); M113.027 (hence `#A^G · #I_G A = #ker N · #N A`); M113.067 and M113.069 (`I_G A ≤ ker N` and `N A ≤ A^G`, from M113.066 and M113.068); M113.107 and M113.108 (`#A^G = #H⁰ · #N A` and `#ker N = #H⁻¹ · #I_G A`, by Lagrange's theorem `Subgroup.card_eq_card_quotient_mul_card_subgroup` and M113.008); and M113.109 (`#H⁰ = #H⁻¹`: substituting these into the balance and cancelling the positive factor `#N A · #I_G A`). Each copy carries the source's `omit … in` clause and the suffix `_aux`. It also proves M118.003, whose proof is not yet in the Library, as the private theorem `herbrandQuotient_eq_one_of_card_eq_aux` with its source proof.

After `show` states the published proposition unfolded, the proof is that of M118.004: `herbrandQuotient_eq_one_of_card_eq_aux` applied to `herbrand_finite_module_card_eq_aux σ hgen`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passages are
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`, lines 446–450](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean#L446-L450) and [`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`, lines 49–67](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean#L49-L67) and [`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, lines 266–313](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L266-L313) and [`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, lines 792–797](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L792-L797) and [`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, lines 818–823](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L818-L823) and [`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, lines 1650–1711](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L1650-L1711):
the docstring at line 446 and the theorem at lines 447–450 of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`; M118.003 and M118.004 at lines 49–67 of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`; and the source theorems M113.024–.027 (lines 266–313), M113.067 (lines 792–797), M113.069 (lines 818–823) and M113.107–.109 (lines 1650–1711) of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`, which the port proves as private copies. The main theorem lies in `namespace CyclicCohomology` (line 21), its `noncomputable section` (line 23), `namespace ProfiniteCohomology` and `namespace Herbrand` (lines 25–26), with `open CategoryTheory` (line 28), `universe uG uA` (line 30) and the variables of lines 32–35. The copied theorems lie in the same namespaces of their files, whose variable lines are those of this module except that the groups have universes `uG uA uB uC`. The source passages are:

```lean
/-- Herbrand-quotient multiplicativity, the finite-module case. -/
theorem herbrandQuotient_eq_one_of_finite_module
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 :=
  herbrandQuotient_finite_module_eq_one σ hgen
```

```lean
/-- If the actual low-degree quotients have the same finite cardinality, then
the Herbrand quotient is `1`. -/
theorem herbrandQuotient_eq_one_of_card_eq (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  have hden : ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  unfold herbrandQuotient
  rw [hcard]
  exact div_self hden

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: the Herbrand quotient of a finite
cyclic module is `1`. -/
theorem herbrandQuotient_finite_module_eq_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  exact herbrandQuotient_eq_one_of_card_eq (G := G) (A := A) σ
    (herbrand_finite_module_card_eq (G := G) (A := A) σ hgen)
```

```lean
omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- If `σ` generates `G`, the kernel of `a ↦ a^(σ-1)` is the fixed subgroup. -/
theorem sigmaMinusOneHom_ker_eq_fixedSubgroup
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    MonoidHom.ker (sigmaMinusOneHom (G := G) (A := A) σ) = fixedSubgroup G A := by
  ext a
  constructor
  · intro ha
    exact fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one
      (G := G) (A := A) (σ := σ) hgen (by simpa using ha)
  · intro ha
    change sigmaMinusOne G A σ a = 1
    simp [sigmaMinusOne, ha σ]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module source: the norm homomorphism factors the cardinality of
`A` into norm-kernel and norm-image cardinalities. -/
theorem card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup [Finite A] :
    Nat.card A = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [normKernelSubgroup, tateNormSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range (tateNormHom (G := G) (A := A))

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module source: for a cyclic generator `σ`, the coboundary
homomorphism factors the cardinality of `A` into fixed and augmentation
cardinalities. -/
theorem card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card A = Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) := by
  simpa [sigmaMinusOneHom_ker_eq_fixedSubgroup (G := G) (A := A) σ hgen,
    augmentationSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range
      (sigmaMinusOneHom (G := G) (A := A) σ)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module cardinality balance behind `h(G,A)=1`: for a finite cyclic
group action, the product `#A^G · #I_G A` equals `#ker N_G · #N_G A`. -/
theorem herbrand_finite_module_cardinality_balance
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) =
      Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  rw [← card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup
      (G := G) (A := A) σ hgen,
    ← card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup (G := G) (A := A)]
```

```lean
/-- The augmentation image lies in the norm kernel. -/
theorem augmentationSubgroup_le_normKernelSubgroup (σ : G) :
    augmentationSubgroup G A σ ≤ normKernelSubgroup G A := by
  intro a ha
  rcases ha with ⟨b, rfl⟩
  exact tateNorm_sigmaMinusOne_eq_one (G := G) (A := A) σ b
```

```lean
/-- The norm image lies in the fixed subgroup, as in Herbrand-quotient theory. -/
theorem tateNormSubgroup_le_fixedSubgroup :
    tateNormSubgroup G A ≤ fixedSubgroup G A := by
  intro a ha g
  rcases ha with ⟨b, rfl⟩
  exact smul_tateNorm_eq (G := G) (A := A) g b
```

```lean
omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Quotient-cardinality source for `H⁰(G,A)=A^G/N_G A`. -/
theorem card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup [Finite A] :
    Nat.card (fixedSubgroup G A) =
      Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [HerbrandH0,
    card_subgroupOf_eq_card (tateNormSubgroup_le_fixedSubgroup (G := G) (A := A))] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Quotient-cardinality source for
`H^{-1}(G,A)=ker(N_G)/I_G A`. -/
theorem card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup
    (σ : G) [Finite A] :
    Nat.card (normKernelSubgroup G A) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (augmentationSubgroup G A σ) := by
  simpa [HerbrandHMinusOne,
    card_subgroupOf_eq_card (augmentationSubgroup_le_normKernelSubgroup (G := G) (A := A) σ)] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The two low-degree Herbrand quotients of a finite cyclic module have equal
cardinality, the finite-module source for Herbrand-quotient multiplicativity. -/
theorem herbrand_finite_module_card_eq
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ) := by
  have h0 := card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup
    (G := G) (A := A)
  have hm := card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup
    (G := G) (A := A) σ
  have hbal := herbrand_finite_module_cardinality_balance
    (G := G) (A := A) σ hgen
  rw [h0, hm] at hbal
  have hfactor :
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) =
        Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
    calc
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ))
          =
          (Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A)) *
            Nat.card (augmentationSubgroup G A σ) := by
            ac_rfl
      _ = (Nat.card (HerbrandHMinusOne G A σ) *
            Nat.card (augmentationSubgroup G A σ)) *
            Nat.card (tateNormSubgroup G A) := hbal
      _ = Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
            ac_rfl
  have hNpos : 0 < Nat.card (tateNormSubgroup G A) :=
    Finite.card_pos (α := tateNormSubgroup G A)
  have hIpos : 0 < Nat.card (augmentationSubgroup G A σ) :=
    Finite.card_pos (α := augmentationSubgroup G A σ)
  exact Nat.mul_right_cancel (Nat.mul_pos hNpos hIpos) hfactor
```

The complete original files are retained at `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean` (SHA-256
`28215b237d5b5024f73b33d90b059eb6273b8fc92ff3c0ae88f9f9dfb804ad27`) and `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` (SHA-256
`53b28b77b5f5f3450745dd1ea265858d605ea582e41d537d690f1bd1736aee58`) and `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` (SHA-256
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`).

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- prove the source theorems M113.024–.027, M113.067, M113.069 and M113.107–.109 of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` and M118.003, with their source statements, `omit` clauses and proofs, as private theorems in this module's section context (groups in `Type`) with the suffix `_aux`, referring to each other by these names; in the copy of M113.024 replace `by simpa using ha` by `MonoidHom.mem_ker.mp ha`;
- give the theorem the published proposition `herbrandQuotient_eq_one_of_finite_moduleStatement (G := G) (A := A) σ hgen` as its type, and begin the proof with `show` stating it unfolded;
- replace the source term `herbrandQuotient_finite_module_eq_one σ hgen` (the unpublished M118.004) by the source proof of M118.004 with the private copies;
- omit `open CategoryTheory`, the universe declaration and all other source declarations.

The names (up to the suffix `_aux`), docstrings, binders and remaining proof steps of all copied theorems and of the main theorem are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. Worker 5264 prepared this module as revision 1 of the shared draft of Task 7142 (`8a2f229a-7526-448d-b445-2324316ba3ce`); Worker 749, the task's executor, rechecked it in the approved environment and submitted it unchanged apart from this sentence, with Worker 5264 as coauthor. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M119.014. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
