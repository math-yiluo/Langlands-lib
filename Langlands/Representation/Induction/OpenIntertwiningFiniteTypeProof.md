# The finite-type support criterion for compact-induction intertwining kernels: proof

Author: Worker 67.

`Langlands.Induction.compactInductionFiniteTypeKernel` proves the published
`Langlands.Induction.CompactInductionFiniteTypeKernelStatement.{uR,uG,uV,uW}`
from `Langlands.Representation.Induction.OpenIntertwiningStatement`. Its type is
exactly that proposition at arbitrary universes `uR`, `uG`, `uV`, `uW`. It adds no
parameters, typeclasses or hypotheses. The module imports only the statement module.
It contains this theorem and four helper declarations, described below. The
statement pair and every pair it imports are unchanged. No unproved proposition is
assumed.

## The statement being proved

`R` is a commutative ring and `G` a topological group. `H` is a subgroup that is open
(`hHo`) and compact (`hHc`). `σ` on `V` and `τ` on `W` are representations of `H`.
`σ.asModule` is finitely generated over `MonoidAlgebra R H` (`hσ`). For every
`Φ : G → (V →ₗ[R] W)`, the statement says that `IsIntertwiningKernel H σ τ Φ` holds
if and only if

- `Φ` has the covariance `Φ (h * g * h') = τ h ∘ₗ Φ g ∘ₗ σ h'`, and
- `(DoubleCoset.mk H H '' Function.support Φ).Finite`.

`IsIntertwiningKernel H σ τ Φ` is the same covariance together with
`(quotientSupport H (fun g => Φ g v)).Finite` for every `v : V`. Here
`quotientSupport H f = quotientMap H '' Function.support f` is the set of right cosets
`H g` with `f g ≠ 0`. So in both directions the covariance carries over unchanged, and
the proof only exchanges the two finiteness conditions.

## Helper declarations (same module)

1. `leftQuotientToDoubleCoset H : LeftQuotient H → DoubleCoset.Quotient H H` sends a
   right coset `H g` to its double coset `H g H`. It is `Quotient.lift` of
   `DoubleCoset.mk H H`. It is well defined because `b * a⁻¹ ∈ H`
   (`QuotientGroup.rightRel_apply`) gives `b = (b * a⁻¹) * a`, and
   `DoubleCoset.mk_mem_mul` removes the left factor from `H`.
   `leftQuotientToDoubleCoset_quotientMap` records
   `leftQuotientToDoubleCoset H (quotientMap H g) = DoubleCoset.mk H H g` (by `rfl`).
2. `eq_zero_of_forall_translate_generators`: let `S` span `σ.asModule` over
   `MonoidAlgebra R H`. An `R`-linear map `f : V →ₗ[R] W` with
   `f (σ h (σ.asModuleEquiv s)) = 0` for all `s ∈ S` and `h ∈ H` is zero.
   *Proof.* The predicate `P x := ∀ h, f (σ h (σ.asModuleEquiv x)) = 0` on
   `σ.asModule` is proved for all `x` by `Submodule.span_induction` on
   `x ∈ span S = ⊤`. The generator, zero and sum cases are immediate. For the case
   `a • x` the proof rewrites with `Representation.asModuleEquiv_map_smul`
   (`a • x` acts as `σ.asAlgebraHom a`) and inducts on `a` with
   `MonoidAlgebra.induction_linear`. On `single h' r`,
   `Representation.asAlgebraHom_single` gives `r • σ h'`. Then
   `f (σ h (r • σ h' y)) = r • f (σ (h * h') y) = 0` by `map_mul` of `σ` and the
   hypothesis `P x` at `h * h'`. Applying `P` at `h = 1` to
   `σ.asModuleEquiv.symm v` gives `f v = 0`.
3. `finite_doubleCoset_support_of_isIntertwiningKernel` is the forward direction
   (below).
4. `finite_quotientSupport_of_finite_doubleCoset_support` is the reverse direction
   (below).

## Forward direction: per-vector finiteness implies finitely many double cosets

This direction uses `hσ` and the kernel property. It does not use openness or
compactness of `H`, nor any topology.

`Module.Finite.fg_top` (the field of `hσ`) gives a `Finset S ⊆ σ.asModule` with
`span (MonoidAlgebra R H) S = ⊤`. The finite set that bounds the double cosets is

`⋃ s ∈ S, leftQuotientToDoubleCoset H '' quotientSupport H (fun g => Φ g (σ.asModuleEquiv s))`.

It is finite by `Set.Finite.biUnion` over `S` and `Set.Finite.image`. Each
`quotientSupport` is finite by the second conjunct of `IsIntertwiningKernel` at the
vector `σ.asModuleEquiv s`. Let `g` be in the support, so `Φ g ≠ 0`. By helper 2 (in
contrapositive form, after `push Not`) there are `s ∈ S` and `h ∈ H` with
`Φ g (σ h (σ.asModuleEquiv s)) ≠ 0`. Covariance at `(1, h, g)`, simplified with
`map_one` of `τ`, gives `Φ (g * h) v = Φ g (σ h v)`. So `Φ (g * h) (σ.asModuleEquiv s) ≠ 0`,
that is `quotientMap H (g * h)` lies in the `s`-th quotient support. Its image under
`leftQuotientToDoubleCoset H` is `DoubleCoset.mk H H (g * h)`, which equals
`DoubleCoset.mk H H g` by `DoubleCoset.mk_mul_mem`.

## Reverse direction: finitely many double cosets imply per-vector finiteness

This direction uses openness and compactness of `H`. It does not use `hσ` or the
covariance.

Let `D = DoubleCoset.mk H H '' Function.support Φ`, a finite set by hypothesis, and
`C = ⋃ q ∈ D, DoubleCoset.quotToDoubleCoset H H q`.

- **`C` is compact.** Each `quotToDoubleCoset H H q` is by definition
  `doubleCoset q.out H H = H * {q.out} * H`. It is compact by `IsCompact.mul`
  (applied twice, with `isCompact_singleton`) from `hHc`. A finite union of compact
  sets is compact (`Set.Finite.isCompact_biUnion`).
- **Its image in `H \ G` is finite.** `quotientMap H` is continuous
  (`continuous_quot_mk`), so `quotientMap H '' C` is compact. The Library theorem
  `Langlands.Induction.discreteTopology_leftQuotient` (in
  `Langlands.Representation.Induction.OpenAdjunction`) makes `LeftQuotient H`
  discrete since `H` is open. So the image is finite (`IsCompact.finite_of_discrete`).
- **It contains the per-vector supports.** Let `v : V` and `Φ g v ≠ 0`. Then
  `Φ g ≠ 0`, so `DoubleCoset.mk H H g ∈ D`, and `g ∈ quotToDoubleCoset H H (mk H H g)`
  by `DoubleCoset.mem_quotToDoubleCoset_iff`. Hence
  `quotientSupport H (fun g => Φ g v) ⊆ quotientMap H '' C`, which is finite.

## Assembly

`compactInductionFiniteTypeKernel` introduces the data. For `→` it returns the
covariance (first conjunct of the kernel property) and helper 3. For `←` it returns
the covariance and helper 4 at every `v`.

## Route and provenance

The source is M.-F. Vignéras, *Représentations ℓ-modulaires d'un groupe réductif
p-adique avec ℓ ≠ p*, Progress in Mathematics 137, Birkhäuser, 1996. Literature ID
`provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`, SHA-256
`4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`. The relevant
part is Chapter I, 8.5, printed pp.67–68 (PDF pp.85–86), which the author read.
There, condition a) on the support of `f` follows from the per-vector condition by
the single sentence "Comme `W ∈ Mod_R K` est de type fini, la fonction `f` vérifie
a)". The forward direction above spells out that sentence through the generators of
`σ.asModule`.

The source does not spell out the converse inclusion. The statement's Markdown and the task suggest
that each double coset `H g H` is a finite union of right cosets, because
`H ∩ g⁻¹ H g` has finite index in the compact group `H`. The implemented proof
reaches the same conclusion differently: `H g H` is compact, and its image in the
discrete space `H \ G` is therefore finite. It does not form the quotient
`H / (H ∩ g⁻¹ H g)`. No separate double-coset finiteness theorem is published. The
reverse-direction helper is stated for an arbitrary `Φ` with finitely many double
cosets in its support, so a proof of `CompactInductionDoubleCosetStatement` can reuse
the same compactness argument.

## Scope

This unit proves only `CompactInductionFiniteTypeKernelStatement`. It does not prove
`CompactInductionKernelStatement`, `CompactInductionDoubleCosetStatement` or their
conjunction `CompactInductionIntertwiningStatement`. Neither smoothness of `σ` or `τ`
nor any property of `G` beyond `IsTopologicalGroup` is used.

## Development check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the module
with no errors or warnings. Inspection of `compactInductionFiniteTypeKernel` reported
level parameters `uR`, `uG`, `uV`, `uW` and exactly the axioms `propext`,
`Classical.choice` and `Quot.sound`. This is development evidence. Independent review,
the Lake build and the exact-target check are separate.
