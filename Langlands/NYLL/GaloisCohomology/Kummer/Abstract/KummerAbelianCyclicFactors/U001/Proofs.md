# NYLL M020.001: jointly faithful cyclic factors of a finite abelian group

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement`
by the theorem
`Langlands.NYLL.KummerTheory.finiteCommGroup_exists_jointlyFaithful_cyclic_factors`.
The theorem's type is exactly that proposition applied to its source
parameter, `finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement Q`.

Its target import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements`
([`Statements.lean`](../Statements.lean)). That published Lean/Markdown pair
and everything it imports are unchanged.

## Target and parameters

The theorem has one universe parameter, `u_1`, as the published proposition
does. Its parameters are explicit `(Q : Type u_1)` with instances
`[CommGroup Q] [Finite Q]`. Unfolding the proposition gives

```lean
∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
  (∀ i, 1 < m i) ∧
  ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
    (∀ i, Function.Surjective (f i)) ∧
    (⨅ i, MonoidHom.ker (f i)) = ⊥
```

So: a finite commutative group `Q` has a finite family, indexed by a type in
`Type 0`, of surjective homomorphisms `f i` onto the cyclic groups
`Multiplicative (ZMod (m i))` of orders `m i > 1`, whose kernels meet in the
trivial subgroup.

## Implemented proof

The proof is the source tactic proof preceded by one added tactic.

1. `unfold finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement`
   (added) replaces the goal by the existential above, so that the anonymous
   constructor in step 4 sees its structure.
2. `obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q`
   applies Mathlib's structure theorem for finite abelian groups
   (multiplicative form): there are `ι : Type`, `hι : Fintype ι`,
   `m : ι → ℕ` with `hm : ∀ i, 1 < m i`, and a multiplicative isomorphism
   `e : Q ≃* ((i : ι) → Multiplicative (ZMod (m i)))`.
3. `let f i := (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e`
   defines the `i`-th coordinate homomorphism `Q → Multiplicative (ZMod (m i))`.
4. `refine ⟨ι, hι, m, hm, f, ?_, ?_⟩` supplies the witnesses, leaving
   surjectivity and the kernel intersection.
5. Surjectivity: for each `i`, `(Function.surjective_eval i).comp e.surjective`.
   Evaluation at `i` is surjective on the product (each factor is nonempty)
   and `e` is surjective; the composite is `f i` by definition.
6. Kernels: `apply le_antisymm`. The inclusion `⊥ ≤ ⨅ i, ker (f i)` is
   `bot_le`. For the other inclusion, take `x` in every kernel;
   `rw [Subgroup.mem_bot]` makes the goal `x = 1`, and `apply e.injective`
   turns it into `e x = e 1`, proved coordinatewise by `ext i`. For each
   `i`, `Subgroup.mem_iInf` gives `x ∈ ker (f i)`, so `MonoidHom.mem_ker`
   gives `f i x = 1`, and `simpa [f]` rewrites both this and the goal
   (using `map_one` for `e 1` and the evaluation of `1` in the product) to
   `e x i = 1`.

The development check of the draft module (diagnostic
`3f4bb059-3736-4922-bca0-69cdddd8670c`) reports no errors or warnings. The
theorem has the universe parameter `u_1`, and its axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement`
  (M020.001 statement), used only by unfolding.
- Mathlib: `CommGroup.equiv_prod_multiplicative_zmod_of_finite`
  (`Mathlib/GroupTheory/FiniteAbelian/Basic.lean`, line 179),
  `Pi.evalMonoidHom` (`Mathlib/Algebra/Group/Pi/Lemmas.lean`, line 188),
  `Function.surjective_eval` (`Mathlib/Logic/Function/Basic.lean`, line 678),
  `MulEquiv.surjective`, `MulEquiv.injective`, `Subgroup.mem_bot` and
  `Subgroup.mem_iInf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean`, lines
  139 and 252), `MonoidHom.mem_ker`
  (`Mathlib/Algebra/Group/Subgroup/Ker.lean`, line 249), `le_antisymm`,
  `bot_le` and the default `simp` set. Line numbers refer to Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

No NYLL declaration other than the statement is used, and no host
class-formation, cup, transfer, Tate or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean:35–59`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean#L35-L59).
Lines 35–36 are the docstring, 37–43 the signature and 44–59 the proof. The
theorem lies in `namespace KummerTheory` (line 25, with
`open CyclicCohomology` at line 27), the `noncomputable section` (line 31)
and `section FiniteAbelianCyclicFactors` (line 33), which has no section
variables before line 37. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m020)
lists this theorem as M020.001 (source unit from line 37; the next unit
starts at line 67). The whole-file SHA-256 is
`abedaf33dffa23e93392885b9c29e77ead8a9452ee32d9100614f6f0ac731033`,
recomputed by Worker 395 on 15 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `finiteCommGroup_exists_jointlyFaithful_cyclic_factors` (M020.001) | Published `finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement` in KummerAbelianCyclicFactors.Statements |
| Proof `finiteCommGroup_exists_jointlyFaithful_cyclic_factors` | This theorem of the same adapted name in KummerAbelianCyclicFactors.U001.Proofs |

Worker 395 made only these changes on 15 November 2026 UTC:

- prefix the namespace with `Langlands.NYLL`;
- replace the two source imports by the sole published Statements import;
- state the theorem's type as the published proposition applied to `Q`;
- add the leading `unfold` of that proposition;
- omit the source's `open CyclicCohomology`, which this proof does not use,
  and the other declarations of the source file.

The section name, the `noncomputable section`, the docstring, the theorem
name, the binders with their names and order, and the source tactics are
unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors. Worker 4918's statement is used unchanged.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M020.001. It is not a class-formation, cup, transfer,
Tate or reciprocity result.
