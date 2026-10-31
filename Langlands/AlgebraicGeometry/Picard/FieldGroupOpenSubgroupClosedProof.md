# Proof: open subsets of a group scheme over a field closed under geometric division are closed

Proof author: Worker 1028. Verification and submission: Worker 1150.

`Langlands.GroupScheme.fieldGroupOpenSubgroupClosed` proves exactly the
published proposition
`Langlands.GroupScheme.FieldGroupOpenSubgroupClosedStatement.{u}`. It applies
to every field `k` in universe `u` and every group object `G` in `Over (Spec k)`
whose structure morphism is locally of finite type. Here `G` is a group object
for the cartesian monoidal structure of the slice category. The theorem also
applies to every open subset `U` of the underlying space of `G.left`, under
one condition: for every algebraically closed field `K : Type u`, every
`b : Spec K ⟶ Spec k` and all `K`-points `p q : Over.mk b ⟶ G` whose images lie
in `U`, the image of `p * q⁻¹` also lies in `U`. The conclusion is that `U` is
closed. The theorem keeps the arbitrary universe and every quantifier of the
statement and adds no hypothesis.

This is the scheme-theoretic form of the elementary fact that an open subgroup
of a topological group is closed. A closely related published form is Stacks
Project Lemma 39.7.7 (Tag 047S; registered source
`stacks-groupoid-schemes-chapter-pdf-2026-07-14`, PDF p.10): for a morphism of
group schemes `ψ : G' → G` over a field, if `ψ(G')` is open in `G`, then it is
also closed. The underlying space of a group scheme is not a
topological group. The implemented proof therefore works with points that
take values in algebraically closed fields. It uses base change to an
algebraic closure, a translation morphism and closed points of a Jacobson
scheme. This is an internal derived argument; the cited Stacks lemma supplies classical context, while the steps below describe the Lean proof.

## The proof of `isClosed_of_isOpen_of_mul_inv_mem`

The theorem `isClosed_of_isOpen_of_mul_inv_mem` has the same content with
explicit arguments; `fieldGroupOpenSubgroupClosed` applies it.

Let `y` be in the closure of `U`. Put `K = AlgebraicClosure κ(y)`. Let
`s : Spec K ⟶ G.left` be the geometric point over `y`, that is, `Spec.map` of
the algebra map followed by `fromSpecResidueField`, and put `b = s ≫ G.hom`.
Since `Spec K` has one point, the image of a `K`-point lies in `U` exactly when
its value at that point does (`mem_iff`).

Let `G_K = pullback G.hom b`, with projections `fst` to `G.left` and `snd` to
`Spec K`. The projection `fst` is open. Indeed, `b` is universally open because
its target is the spectrum of a field (Mathlib's instance for morphisms to
integral one-point schemes), and `fst` is a base change of `b`. The scheme
`G_K` is a Jacobson space because `snd` is locally of finite type. The set
`U_K = fst⁻¹ U` is open. The section `s' = pullback.lift s (𝟙 _)` sends the
point of `Spec K` into the closure of `U_K`, because `fst` is open and
`fst (s' pt) = y` lies in the closure of `U`.

In the slice category, `X_K = Over.mk (snd ≫ b)` has two morphisms to `G`:
`fstO`, induced by `fst`, and `sO`, induced by `snd ≫ s`. The division
morphism `ρ : G_K ⟶ G_K` is `pullback.lift (sO * fstO⁻¹).left snd`. On points it
is `z ↦ s · z⁻¹`. For a section `z` of `snd`, the slice morphism
`secO z : Over.mk b ⟶ X_K` satisfies `secO z ≫ sO = Over.homMk s`. By
`MonObj.comp_mul` and `GrpObj.comp_inv`, the value of the `K`-point
`Over.homMk s * (secO z ≫ fstO)⁻¹` is `fst (ρ (z pt))` (`secO_ρ`).

Every nonempty open subset of `G_K` contains a closed point
(`nonempty_inter_closedPoints`). Since `K` is algebraically closed, this
closed point is the value of a section of `snd` (`pointOfClosedPoint`).

The rest of the proof proceeds in four steps.

1. Apply this to `U_K`, which is nonempty because its closure contains a
   point. This gives a `K`-point `q₀` in `U`, so `1 = q₀ * q₀⁻¹` is in `U`.
2. The point `ρ (s' pt)` lies in `U_K`, because `secO s' ≫ fstO = Over.homMk s`
   and `s * s⁻¹ = 1`.
3. Since `ρ` is continuous, `ρ⁻¹ U_K` is an open neighbourhood of `s' pt`, so
   it meets `U_K`. The intersection contains the value of a section `z`. Put
   `q = secO z ≫ fstO`. Then both `q` and `Over.homMk s * q⁻¹` lie in `U`.
4. The hypothesis gives `q⁻¹ = 1 * q⁻¹ ∈ U`, and then
   `Over.homMk s = (Over.homMk s * q⁻¹) * (q⁻¹)⁻¹ ∈ U`. Hence `y = s pt ∈ U`.

## Scope

The field `k` is arbitrary: it need not be perfect or algebraically closed.
`G` is an arbitrary group object over `Spec k` that is locally of finite type.
The proof uses no commutativity, separatedness, smoothness or Noetherian
hypothesis. The condition on `U` is needed only for points with values in
algebraically closed fields in universe `u`. Nothing is asserted about
connected components.
