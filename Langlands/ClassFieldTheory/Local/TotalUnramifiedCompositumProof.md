# Finite totally ramified and unramified composita

Authors: Worker 159 (Lean proof and this documentation), with Worker 27
credited for the suggested arithmetic proof route recorded in the task. No
unpublished Lean draft was reused. The imported statement was authored by
Workers 27 and 231 and is unchanged.

## Result and precise scope

`Langlands.LocalClassField.totalUnramifiedCompositum.{u}` proves exactly
`Langlands.LocalClassField.TotalUnramifiedCompositum.{u}`, imported from
`Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumStatement`. There
are no additional outer hypotheses.

For a prime `p`, `F : PadicField.{u} p`, and finite intermediate extensions
`E` and `K'` of `AlgebraicClosure F.Carrier`, assume `E/F` is Galois and the
two canonical absolute ramification-index equalities

\[
e(E)=[E:F]e(F),\qquad e(K')=e(F).
\]

The theorem proves that `E.field` and `K'.field` are linearly disjoint. It
chooses the finite field `M` whose underlying intermediate field is exactly
`E.field ⊔ K'.field`, with the actual inclusions into this supremum, and
proves all six clauses of the statement for this same `M`:

1. `[M:K']=[E:F]`;
2. `e(M)=e(E)`;
3. `IsGalois K'.field M.field`;
4. bijectivity of the canonical `relativeResidueMap` from `K'` to `M`;
5. equality of canonical orders on every element of `E` under its inclusion
   into `M`;
6. equality of the determinant norm from `M` to `K'` on that inclusion with
   the image of the determinant norm from `E` to `F`.

The universe is arbitrary. The proof assumes neither prime degree nor a
Galois condition on `K'/F`. Degree-one extensions and the element zero are
included. In particular, the order assertion uses the existing `ord 0 = 0`
convention. No assertion about ramification breaks, norm polynomials, norm
surjectivity or infinite unramified extensions is made here.

## Implemented arithmetic proof

Write `n=[M:K']`, `d=[E:F]`, and let `r` be the relative residue degree of the
actual embedding `K' → M` in `Langlands.Weil.Local.extensionResidueDegree`.
The auxiliary lemmas are internal to the module.

First, `ramificationIndex_le_of_extension` proves monotonicity of the
absolute ramification index under a finite extension. Apply
`ramificationIndex_mul_ord_relative_algebraMap` from `NormOrderProof` to
the canonical uniformizer of the base field. Its order is one, so the
comparison says

\[
e(\text{base})\,\operatorname{ord}_{\text{extension}}(\pi)
=e(\text{extension}).
\]

Both indices are positive. The integer order is therefore at least one,
which gives the inequality. Applying this to `E → M` yields `e(E) ≤ e(M)`.

Second, `relative_ramification_identity` specializes
`PadicField.ramificationIndex_mul_extensionResidueDegree` from
`UnramifiedCriterionProof` to the given algebra map. It explicitly identifies
the algebra installed by `extensionAlgebra` with the supplied algebra using
`toAlgebra_algebraMap`. Thus the relative extension degree in that theorem
is the `Module.finrank` for the same inclusion algebra used here, and

\[
e(M)r=n e(K').
\]

Since `extensionResidueDegree_pos` gives `r ≥ 1`, this implies
`e(M) ≤ n e(K')`. Mathlib's `IntermediateField.finrank_sup_le`, combined
with the tower law and positivity of `[K':F]`, gives `n ≤ d`. Consequently,

\[
d e(F)=e(E)\le e(M)\le n e(K')=n e(F)\le d e(F).
\]

The private `arithmetic` lemma extracts `n=d`, `e(M)=e(E)` and `r=1`.
It then uses `extensionResidueCardinality` to show that the two canonical
residue fields have equal cardinality. The actual `relativeResidueMap` is
an injective field homomorphism, so `Nat.bijective_iff_injective_and_card`
makes it bijective. This does not replace the map by an unrelated residue
field isomorphism.

Finally, the order comparison is applied to an arbitrary `z : E.field`.
After substituting `e(M)=e(E)`, cancellation of the nonzero common integer
index proves the required order equality. The imported comparison already
handles zero. Linear disjointness follows from the tower law, `n=d`, and
`IntermediateField.LinearDisjoint.of_finrank_sup`.

## Galois, norm and trace transport

For any specified finite `M` equal to the supremum, the proof regards `E`
and `K'` as intermediate fields of `M` using `IntermediateField.restrict`
and their actual inclusion proofs. `lift_restrict` and `lift_sup` show that
these restricted fields have supremum top. The canonical
`restrictAlgEquiv` identifies each original field with its restricted copy.

For the Galois conclusion, `IsGalois.of_algEquiv` transfers the given Galois
structure of `E/F` to its restricted copy. `IsGalois.sup_right` then proves
the Galois structure over the restricted copy of `K'`.
`IsGalois.of_equiv_equiv` transports it to the actual inclusion algebra
`K'.field → M.field`; compatibility follows from
`restrictAlgEquiv.apply_symm_apply` on underlying elements.

For norms and traces, `LinearDisjoint.algEquiv_of_isAlgebraic` transfers
linear disjointness to the two restricted copies. This uses the proved
finite-dimensionality, hence algebraicity, of `E/F`. Mathlib's
`IntermediateField.LinearDisjoint.norm_algebraMap` and
`IntermediateField.LinearDisjoint.trace_algebraMap` apply to those copies
inside `M`. The respective `Algebra.norm_eq_of_ringEquiv` and
`Algebra.trace_eq_of_ringEquiv` lemmas change the base field back to `K'`;
`Algebra.norm_eq_of_algEquiv` and `Algebra.trace_eq_of_algEquiv` change the
source copy back to `E`. The algebra-map compatibility squares are proved
for the actual inclusions. These are determinant and linear-algebra trace
identities, not separately chosen maps.

The exported helper is
`Langlands.LocalClassField.totalUnramifiedCompositum_trace.{u}`. It takes
`p`, `F`, every finite `E K' M`, a proof
`hM : M.field = E.field ⊔ K'.field`, the two inclusion proofs `hE`, `hK`,
and `E.field.LinearDisjoint K'.field`. Its conclusion is, for every `z`,

```lean
Algebra.trace K'.field M.field (IntermediateField.inclusion hE z) =
  algebraMap F.Carrier K'.field (Algebra.trace F.Carrier E.field z)
```

Its type installs precisely the three `asPadicField` algebras, the two
inclusion-induced algebras, all four scalar towers and the relative
finite-dimensional instance displayed in the target. It has no Galois or
ramification hypotheses beyond the stated linear-disjointness input and
is valid for every such `M`, not merely the existential witness chosen by
the main theorem.

## Dependencies and source

The module imports the unchanged target, `NormOrderProof`, and
`Galois.Local.UnramifiedCriterionProof`. It uses the normalization and
relative residue infrastructure in their published import closures, and
Mathlib's finite-dimensional, intermediate-field, Galois, linear-disjoint,
norm and trace results. The private `compositum_result` assembles the
results with `M` as a parameter. The main theorem supplies the finite
supremum and its two lattice inclusions. This keeps instance inference
manageable without changing the mathematical assumptions.

The original source is Jean-Pierre Serre, *Local Fields*, Greenberg English
translation, GTM 67 (1979), registered as `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 159 read Chapter V, §4, printed pp. 87–88 (PDF pp. 94–95). The setup
states the linear disjointness, unchanged uniformizers and Galois property
under unramified base extension. The present arithmetic proof implements
the degree-bound argument using canonical absolute indices and the
published residue-degree identity. Norm and trace base change are derived
linear-algebra consequences; the trace helper is internal derived content,
not a quotation of Proposition 6. Proposition 6's norm-existence conclusion
is outside this module.

Worker 159 also read the Local Fields entries on PDF pp. 2–3 of Serre,
*Corrections to J-P. Serre's books* (2019), registered as
`serre-book-corrections-2019`, file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
Those entries contain no correction to the cited pp. 87–88.

A development Lake build and inspection of the main theorem completed with
zero errors or warnings, universe parameter `u`, and only `propext`,
`Classical.choice` and `Quot.sound`. Development checking alone is not
independent semantic acceptance or publication.
