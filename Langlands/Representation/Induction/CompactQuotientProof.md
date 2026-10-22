# Smooth induction from a subgroup with compact coset space

This module proves the published proposition
`Langlands.Induction.CompactQuotientClause` from
[`StructuralStatement`](StructuralStatement.md). The closing theorem is
`Langlands.Induction.compactQuotientClause_holds`:

```
theorem compactQuotientClause_holds {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [IsTopologicalGroup G] (H : Subgroup G) :
    CompactQuotientClause (V := V) H
```

Its binder telescope is the target's: the group and carrier universes are
independent, and there are no further hypotheses. In particular there is no
Hausdorff, closedness, compact-open basis or finite-dimensionality
assumption. For every `sigma : Representation ℂ H V`, compactness of the
left coset space `LeftQuotient H` (that is, `H \ G`) and admissibility of `sigma`
imply that `compactInclusion H sigma` is bijective and that
`smoothInduced H sigma` is admissible. The statement pair and its imports are
unchanged; this module only imports `StructuralStatement`.

## Lemmas

The intermediate lemmas are stated over an arbitrary commutative ring `R`, a
group `G` with a topology making it a topological group, and any subgroup `P`.
The finiteness step additionally assumes `IsNoetherianRing R`. The closing
theorem applies them with `R = ℂ` and `P = H`. Several facts proved privately in
[`Definitions`](Definitions.md) are reproved here under new public names,
because private declarations cannot be used and the Definitions pair must stay
unchanged.

- `eval_covariant`: `eval P σ f (p * x) = σ p (eval P σ f x)`. This is the
  covariance field of the underlying coinduced function.
- `eval_mul_of_mem_fixedVectors`: if `f` is fixed by a subgroup `K` under
  `smoothInduced`, then `eval P σ f (x * k) = eval P σ f x` for `k ∈ K`.
  The action is right translation.
- `eval_isLocallyConstant`: a smooth induced function is locally constant.
  Its uniform open right stabilizer `K` makes it constant on the open
  neighborhood `x * K` of each point `x`.
- `quotientMap_preimage_quotientSupport`: the preimage of the projected
  support in `G` is exactly the support of the function. If `y` lies in the
  support and `x` lies in the same coset as `y`, then `y = p * x` with
  `p ∈ P`, so covariance gives `f(y) = σ(p) f(x)`. Hence `f(x)` is also
  nonzero.
- `isClosed_quotientSupport`: the projected support is closed in `P \ G`.
  The support is the complement of the zero fiber, which is open by local
  constancy, so the support is closed. Its preimage under the quotient map is
  this support, and a quotient map detects closed sets.
- `compactInclusion_bijective_of_compactSpace`: with `CompactSpace (LeftQuotient P)`,
  `compactInclusion P σ` is bijective. It is injective because it is the
  subtype inclusion. It is surjective because every smooth induced function has
  closed projected support, and a closed subset of a compact space is compact,
  so the function already belongs to compact induction.

## Finite double-coset cover

`exists_finset_doubleCoset_cover` proves that a compact `P \ G` and an open
subgroup `K` of `G` give a finite `t : Finset G` such that every `x : G` can
be written `x = p * i * k` with `i ∈ t`, `p ∈ P` and `k ∈ K`. The projection
`G → P \ G` is an open map, by Mathlib's
`MulAction.isOpenQuotientMap_quotientMk` for the action of `P` on `G` by left
multiplication. Hence the images of the open sets `i * K`, for `i : G`, form
an open cover of `P \ G`. Every coset `P x` lies in the image of `x * K`.
Compactness yields a finite subcover indexed by `t`. If `P x` lies in the image
of `i * K`, then `x` and `i * k` lie in the same coset for some `k ∈ K`, so
`p = x * (i * k)⁻¹ ∈ P` and `x = p * i * k`.

The cover is derived inside the proof from compactness and openness of `K`. It
is not an additional input of the closing theorem.

## Evaluation at representatives

`conjOpenSubgroup P K i` is the open subgroup `P ∩ i K i⁻¹` of `P`, built as
the preimage of `K` under the continuous homomorphism `p ↦ i⁻¹ * p * i`.
`mem_conjOpenSubgroup` gives this membership condition.

`eval_mem_fixedVectors` shows that if `f` is fixed by `K`, then `f(i)` is
fixed by `σ` restricted to `P ∩ i K i⁻¹`. For `p` in that subgroup, put
`k = i⁻¹ * p * i ∈ K`. Then `σ(p) f(i) = f(p * i) = f(i * k) = f(i)` by
covariance and `K`-invariance.

`fixedEvaluation P σ K t` is the `R`-linear map from the `K`-fixed vectors of
`smoothInduced P σ` to the finite product, over `i ∈ t`, of the fixed vectors
of `σ` under `P ∩ i K i⁻¹`. It sends `f` to the family of values `f(i)`.
`fixedEvaluation_injective` proves that this map is injective whenever `t`
satisfies the double-coset cover property. Suppose all values `f(i)` vanish.
Write an arbitrary `x` as `p * i * k`. Then `f(x) = f(p * i) = σ(p) f(i) = 0`,
by `K`-invariance and covariance. The selected finite set `t` is not an input
of the closing theorem; it is chosen inside the proof.

## Admissibility

`smoothInduced_isAdmissible_of_compactSpace` assumes `IsNoetherianRing R`,
`CompactSpace (LeftQuotient P)` and admissibility of `σ`. It concludes that
`smoothInduced P σ` is admissible. Smoothness is the published
`smoothInduced_smooth`. Admissibility in `Langlands.IsAdmissible` asks for
finiteness of the fixed vectors under every open subgroup. For an arbitrary
open subgroup `K` of `G`, choose a finite double-coset cover `t`. Each factor
`fixedVectors σ (P ∩ i K i⁻¹)` is a finite module by admissibility of `σ`,
because `P ∩ i K i⁻¹` is an open subgroup of `P`. A finite product of finite
modules is finite. Over a Noetherian ring, a module that injects into a finite
module is finite, by Mathlib's `Module.Finite.of_injective`. The injection is
`fixedEvaluation`. No compact-open neighborhood basis is needed, since the
argument applies directly to every open subgroup.

The closing theorem takes `σ`, the compactness instance and admissibility,
then pairs `compactInclusion_bijective_of_compactSpace` with
`smoothInduced_isAdmissible_of_compactSpace` at `R = ℂ`.

## Source

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), source `bernstein-zelevinsky-1977-induced-i` (content
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).
Section 1.8(a), printed page 444 (PDF page 5), defines the induced and
compactly induced representations. Proposition 1.9(e), printed page 445 (PDF
page 6), states that when `G` is compact modulo `P = MU`, `I` and `i` coincide
and preserve admissibility. Both pages were read in the original. The case
here takes the source's `U` trivial, its character trivial and its `M` equal
to `H`, as in the StructuralStatement Markdown. Bernstein and Zelevinsky
refer to their earlier paper (their reference [1], Chapter I) for the
proof, which was not consulted. The route above, with a finite double-coset
cover and evaluation into fixed vectors of `P ∩ i K i⁻¹`, is internal and is
implemented directly from the published definitions. The generalization of the lemmas to commutative and Noetherian
coefficient rings and to arbitrary subgroups is an implementation choice;
the closing theorem is exactly the complex target.

## Checks

The module compiles in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
with no errors or warnings. A private check assigned
`@compactQuotientClause_holds` to the fully quantified target type, with the
group and carrier in independent universes, and `#check` showed identical
binder telescopes for `@CompactQuotientClause` and the closing theorem. The
axioms of `compactQuotientClause_holds` are `propext`, `Classical.choice` and
`Quot.sound`. These are development checks; machine validation and independent
review are separate.

All declarations and proofs in this module are by Worker 53.
