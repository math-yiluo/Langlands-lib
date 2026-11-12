# Kernel cosets and saturated cosets

This adapts Naganori Yamaguchi's NYLL M006.006 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original file was read; its SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The public declaration is
`Langlands.NYLL.ClassFormation.kernelCosetEquivSaturation`.

The full source telescope (lines 23–25 and 84–89) is preserved: independent
universes `u v`, implicit `G : Type u` and `D : Type v`, instances
`Group G` and `Group D`, explicit `d : G →* D`, implicit subgroups `L K`,
and explicit `hLK : L ≤ K`. The result is actual `Equiv` data between

```
(↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker))
```

and

```
(↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))).
```

These are types of left cosets. The subgroup `L` may be nonnormal, and neither
coset type is required to be finite. There is no commutativity assumption.
Normality of `d.ker`, supplied by Mathlib for every group homomorphism,
is sufficient for the construction.

The equivalence sends the coset of a kernel element to the coset of the same
element in the larger saturated subgroup. Its inverse comes from
`Equiv.ofBijective`. The following source helpers occur as local terms inside
the definition, with the same names and bodies. They introduce no further
public declarations.

| Source unit and lines | Source name in `ClassFormation` | Local implementation |
| --- | --- | --- |
| M006.001, 27–29 | `kernelToSaturation` | `let` for the subgroup inclusion |
| M006.002, 31–40 | `kernelToSaturation_rel_iff` | `have` proving equivalence of the two coset relations |
| M006.003, 42–46 | `kernelCosetToSaturationCoset` | `let` for the quotient map |
| M006.004, 48–56 | `kernelCosetToSaturationCoset_injective` | `have` proving injectivity |
| M006.005, 58–78 | `kernelCosetToSaturationCoset_surjective` | `have` proving surjectivity |
| M006.006, 80–89 | `kernelCosetEquivSaturation` | The public namespaced data definition |

For well-definedness and injectivity, the original relation argument unfolds
`QuotientGroup.leftRel_apply`, `Subgroup.mem_subgroupOf`, and
`Subgroup.mem_inf`. The kernel condition on the difference follows from
the two representatives already belonging to `d.ker`. Quotient induction
then proves injectivity.

For surjectivity, a representative `z` in `K ⊓ (L ⊔ d.ker)` is written
as `n * l` with `n ∈ d.ker` and `l ∈ L`, using
`Subgroup.mem_sup_of_normal_left`. Since `L ≤ K`, the equality
`n = z * l⁻¹` puts `n` in `K`. The element `n` therefore represents a
kernel coset with the required image. The final two arguments of
`Equiv.ofBijective` are exactly these injectivity and surjectivity proofs.

This extraction replaces the source import
`Nyll.GaloisCohomology.GroupTheory.QuotientTower` with
`Mathlib.GroupTheory.QuotientGroup.Basic`. The construction only uses
Mathlib's subgroup inclusion, kernel normality, join membership, coset
relations, quotient map and induction, and `Equiv.ofBijective`.
The published NYLL quotient-tower equivalence concerns a subgroup tower
and does not have these two coset endpoints; Mathlib's quotient-group
isomorphism theorems require normality of the subgroup being divided out.
No exact existing declaration was found in the Library search.
The focused compile confirms that no preceding M006 publication,
cardinal-index definition, or additional NYLL import is needed.

Worker 120 made the namespace prefix, focused extraction, import change,
file documentation and docstring edit, and moved the five original private
helpers inside the definition. Their scopes become local `let` and `have`
bindings, without changing their mathematical content. The final
`Equiv.ofBijective` body is unchanged after unfolding these bindings.
A private probe retains the original M006.001–006 commands in their original
section context and checks equality of the entire unapplied original and
adapted constants by `rfl`, with explicit independent universes. A separate
whole-constant assignment checks every parameter and endpoint.
No global or local instance is introduced.

This contribution publishes equivalence data. It does not publish standalone
theorems under the five helper names, relative-index identities, or any
class-formation or reciprocity result. Later public propositions and their
exact proofs remain separate obligations.

The source copyright, author and Apache-2.0 header is retained in the Lean
file. The source registration is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable errata note was found. The original license files remain at
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
