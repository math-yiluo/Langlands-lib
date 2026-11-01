# Open chart loci and field-valued coverage of the quotient Grassmannian

Let `R` be any commutative ring, `M` any `R`-module with an additive
commutative group, and `k : ℕ`. All rings, modules and index types in this
module have universe zero. The Grassmannian is Mathlib's
`Module.Grassmannian A (A ⊗[R] M) k`: its points are submodules whose
**quotients** are finite projective of stalk rank `k`.

The module proves that a fixed tuple gives coordinates on an open locus,
and that a spanning family contains such a tuple over every field.
There is no finiteness or freeness assumption on `M`, no independence
assumption on the original family, and no positivity assumption on `k`.
The base ring and the commutative test algebras may be zero rings.

## Field-valued coverage

For any family `g : ι → M` spanning `M` over `R`, every field `K` with
an `R`-algebra structure, and every
`N : Module.Grassmannian K (K ⊗[R] M) k`, the theorem
`Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top`
supplies an injective `I : Fin k → ι` such that

\[
 K^k \longrightarrow (K\otimes_R M)/N,\qquad
 v\longmapsto \sum_i v_i q_N(1\otimes g_{I(i)})
\]

is bijective. Here `q_N` is the quotient map.

The namespace `Module.Grassmannian.FieldCover` contains the implemented
proof. `span_mkQ_tmul_eq_top` first extends the spanning equality to `K`
and then maps it to the quotient. `finrank_quotient_eq` evaluates stalk
rank at the zero prime of the field to obtain quotient dimension `k`.
`cover` extracts a linearly independent subfamily with the same span,
forms a basis, and reindexes its finite index set by `Fin k`. The
displayed map is the inverse of that basis's coordinate equivalence.
The exported theorem applies this construction directly.

## The open locus

Fix `x : Fin k → M`, a commutative `R`-algebra `A`, and
`N : Module.Grassmannian A (A ⊗[R] M) k`. In the namespace
`Module.Grassmannian.ChartOpenLocus` define

\[
 Q=(A\otimes_R M)/N,\qquad
 q_i=q_N(1\otimes x_i),\qquad
 W=\operatorname{span}_A\{q_i\},\qquad C=Q/W.
\]

The Lean names are `Q`, `q0`, `W` and `K`, respectively; `K` here is a
cokernel module, not the field used in the preceding section. Since
`Q` is finite, `C` is finite. The definition `U` is

\[
 U=\operatorname{Spec} A\setminus V(\operatorname{Ann}_A C).
\]

Thus it is the complement of the support of `C`.
`isOpen_U` proves openness by complementing a closed zero locus, and
`mem_U` gives the condition
`¬ Module.annihilator A C ≤ p.asIdeal`.

The theorem
`Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset`
supplies this open set and proves, for every commutative `R`-algebra `B`
and every `φ : A →ₐ[R] B`, that

\[
 \left(v\mapsto\sum_i v_i q_{\phi_*N}(1\otimes x_i)\right)
 \text{ is bijective}
 \quad\Longleftrightarrow\quad
 \operatorname{image}(\operatorname{Spec}\phi)\subseteq U.
\]

The point `φ_*N` is Mathlib's actual `Module.Grassmannian.map φ N`.
There is no flatness hypothesis on `φ`.

The proof proceeds through three equivalences.

- `span_tmul_eq_top_iff` identifies the condition that the extended
  `q_i` span `B ⊗[A] Q` with `Subsingleton (B ⊗[A] C)`. It uses
  right exactness of tensor product on `W → Q → C → 0` and identifies
  the image of the tensored inclusion with the span of the pure tensors.
- `subsingleton_iff_forall_mem_U` identifies that vanishing condition
  with every prime of `B` mapping into `U`. In the forward direction,
  membership in the finite module's support gives a nonzero fibre over
  the residue field of the contracted prime. The map to the residue
  field of the original prime extends this fibre to a nonzero vector
  space. Tensor cancellation identifies it with a scalar extension of
  the supposedly zero `B ⊗[A] C`, a contradiction. In the reverse
  direction, a nonzero `B ⊗[A] C` has a proper annihilator. A maximal
  ideal containing it contracts to a prime containing
  `Ann_A C`, contradicting the given spectral-image condition.
- `exists_equiv` identifies the quotient of `φ_*N` with `B ⊗[A] Q`
  and computes the images of the distinguished `x_i`.
  `bijective_iff` therefore translates spanning into surjectivity of
  `B^k → (B ⊗[R] M)/(φ_*N)`. The helper
  `bijective_of_surjective_of_rankAtStalk` applies Mathlib's theorem for
  surjections between finite flat modules with equal ranks at maximal
  ideals to obtain bijectivity. Both ranks are `k`. The proof derives
  nontriviality of `B` only in the presence of such a prime.

The final theorem installs the algebra structure induced by `φ` and
composes these equivalences.

These are open subsets of affine test spectra and coverage of
field-valued points. Scheme construction, gluing of the Grassmannian
charts, projectivity, Hilbert schemes and the normalized CM moduli
comparison remain obligations of the larger construction.

## Source, reuse and adaptations

The registered source is `anthropic-flt-complete-lean-source-6e837e75`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, retained distribution
SHA-256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete originals read and compared are:

- `P2M/Sol/S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top.lean`,
  lines 1–69, SHA-256
  `8f6e6464602fb6e95276f8bf5573c6e7d484f605fae68aa46e7c98cf1355e122`;
- `P2M/Sol/S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset.lean`,
  lines 1–238, SHA-256
  `5524cdcfebc4cd86f63777f4f1bddae59bae265be924a71d8afbf0f0a5b2fba6`;
- the corresponding `Theorems/Thm_*.lean` exported wrappers, complete
  lines 1–15 and 1–16, respectively.

Both complete exported theorem signatures are identical to the wrappers.
The solution namespaces become `Module.Grassmannian.FieldCover` and
`Module.Grassmannian.ChartOpenLocus`, and the `solution` declarations
receive the original exported names. The port preserves the source's
universe-zero scope, quotient convention, hypotheses and conclusions.

Focused Mathlib imports replace `import Mathlib` and `P2M.Util`. The
source's proof of equal-rank surjectivity implying bijectivity is replaced
by an application of
`Module.bijective_of_surjective_of_rankAtStalk_eq` from
`Mathlib/RingTheory/Flat/LocallyFree.lean`; the rank calculation ends with
an explicit constant-function reduction. The source's duplicate
`subsingleton_tensor` helper is omitted in favour of the existing
`TensorProduct.uniqueRight` instance. The faithfully flat tensor
nontriviality instance is imported from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`, and applies to the
nontrivial field extension in the residue-fibre argument. The deprecated
three-case `TensorProduct.induction_on` is replaced by the current
`TensorProduct.inductionOn`, whose pure-tensor and addition cases also
cover zero. Local instances use the current `have`/`let` style.

The implementation reuses Mathlib's actual Grassmannian base change,
finite-module support, residue-field lifts and tensor-product
equivalences. Searches of the current Library and Mathlib found no
existing exported versions of these two results. This pair imports only
Mathlib and complements the separately published algebraic chart
equivalences in `Langlands.RingTheory.Grassmannian.Charts`.

The original distribution is Apache 2.0 licensed. The unchanged published
[LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE), and
[ATTRIBUTION](../../../licenses/Anthropic-FLT/ATTRIBUTION.md) apply and
are byte-identical to the pinned source files. The source attribution
table has no separate entry for either of these modules.
