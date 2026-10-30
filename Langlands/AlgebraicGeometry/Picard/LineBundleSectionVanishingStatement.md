# Vanishing of line-bundle sections along field points and tangent vectors

This module states one proposition and proves nothing:
`Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingStatement`.
It has one universe parameter `u`. It is the conjunction of seven clauses,
nested to the right, so clause 1 is `.1`, clause 2 is `.2.1`, and clause 7
is `.2.2.2.2.2.2`.

## Ingredients

Every clause quantifies over schemes in `Scheme.{u}` with no hypothesis on
them. Every line bundle is the published `LineBundle X`: an actual module
sheaf `L.obj` on `X` that is locally isomorphic to the structure sheaf. Every
section is an arbitrary element of
`Langlands.SchemeModule.GlobalSections L.obj = Γ(L.obj, ⊤)` and may be zero.
The clauses use only the following published constructions.

- `VanishesAlong L f s` (module
  `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`) means
  `pullbackSection f L.obj s = 0`. Here `f : Y ⟶ X` is any morphism and
  `pullbackSection` is the published pullback of a global section to a
  global section of `(Scheme.Modules.pullback f).obj L.obj`.
- `trivializationOpen L.obj s` (module
  `Langlands.AlgebraicGeometry.Modules.SectionLocus`) is the supremum of all
  opens on which the morphism `𝒪 → L.obj` with `1 ↦ s` restricts to an
  isomorphism. It is the whole open on which `s` generates `L.obj`.
- `tensorSection L.obj M.obj s t` (module
  `Langlands.AlgebraicGeometry.Modules.TensorSections`) is the published
  product section `s ⊗ t` of the actual sheaf tensor product
  `tensorObj L.obj M.obj`.
- The tensor line bundle is exactly
  `LineBundle.tensor pullbackTensorComparisonIsIso L M`. The constructor
  `LineBundle.tensor` (module
  `Langlands.AlgebraicGeometry.Picard.LineBundleTensor`) takes a proof that
  the canonical pullback tensor comparison is invertible. It receives the
  published theorem `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`
  (module `Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`). No new
  preservation hypothesis is added. Its underlying module is
  `tensorObj L.obj M.obj`, so `tensorSection L.obj M.obj s t` is one of its
  global sections.
- `IsTangentVectorAt p x v` (module
  `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`), for a field
  `K`, `p : X ⟶ Spec K`, `x : Spec K ⟶ X` and `v : Spec K[ε] ⟶ X`, means
  `v ≫ p = dualNumberProjection K` and
  `dualNumberAugmentation K ≫ v = x`. So `v` is a `K[ε]`-point over `K`
  whose restriction along the augmentation `a + bε ↦ a` is `x`. `K[ε]` is
  Mathlib's `DualNumber K`.

The Lean names differ slightly from the task text: the second section,
called `u` in the task, is `t` here, and the tangent vector, called `t` in
the task, is `v` here.

## The seven clauses

1. Field-point test. For every scheme `X`, field `F : Type u`, line bundle
   `L`, morphism `x : Spec F ⟶ X`, section `s` and point `y` of `Spec F`:
   `VanishesAlong L x s ↔ x y ∉ trivializationOpen L.obj s`. Since `Spec F`
   has exactly one point, `x y` is the image point of `x`. The clause says
   that `s` vanishes along `x` precisely when `s` does not generate `L` at
   that image point.
2. Tensor test at a field point. For `X`, `F`, `x` as in clause 1, line
   bundles `L` and `M`, and sections `s` of `L` and `t` of `M`: `s ⊗ t`
   vanishes along `x`, as a section of the tensor line bundle above, if and
   only if `s` vanishes along `x` or `t` vanishes along `x`.
3. Right cancellation along a morphism. For schemes `X` and `Y`, line
   bundles `L` and `M` on `X`, sections `s` of `L` and `t` of `M`, and an
   arbitrary morphism `f : Y ⟶ X`: if `f y ∈ trivializationOpen M.obj t`
   for every point `y` of `Y`, then `s ⊗ t` vanishes along `f` if and only
   if `s` vanishes along `f`.
4. Left cancellation along a morphism. With the same data, if
   `f y ∈ trivializationOpen L.obj s` for every point `y` of `Y`, then
   `s ⊗ t` vanishes along `f` if and only if `t` vanishes along `f`.
5. Tangent generation. For every field `K : Type u`, scheme `X`, morphisms
   `p : X ⟶ Spec K`, `x : Spec K ⟶ X` and `v : Spec K[ε] ⟶ X`, line bundle
   `M` and section `t` of `M`: if `IsTangentVectorAt p x v` and `t` does not
   vanish along `x`, then `v y ∈ trivializationOpen M.obj t` for every
   point `y` of `Spec K[ε]`.
6. Right tangent cancellation. With the data of clause 5 and also a line
   bundle `L` with a section `s`: if `IsTangentVectorAt p x v` and `t` does
   not vanish along `x`, then `s ⊗ t` vanishes along `v` if and only if `s`
   vanishes along `v`.
7. Left tangent cancellation. With the same data: if
   `IsTangentVectorAt p x v` and `s` does not vanish along `x`, then
   `s ⊗ t` vanishes along `v` if and only if `t` vanishes along `v`.

## Hypotheses that are not assumed

No clause assumes algebraic closure, smoothness, properness, projectivity,
ampleness, finite type, quasi-compactness, separatedness or a noetherian
condition. The tangent clauses include the zero tangent vector
`dualNumberProjection K ≫ x`; no nonzero hypothesis is imposed. They add no
separate hypothesis that `x` is a rational point, because the published
lemma `Langlands.AlgebraicGeometry.Picard.IsTangentVectorAt.isRationalPoint`
derives `x ≫ p = 𝟙 _` from
`IsTangentVectorAt p x v`.

The cancellation hypotheses in clauses 3, 4, 6 and 7 are generation
conditions, not mere nonvanishing of the cancelled factor along the
morphism. Over a nonreduced base a nonzero section need not generate: on
`Spec K[ε]` the section `ε` of the structure sheaf is nonzero but generates
nowhere. In clauses 6 and 7 the hypothesis is nonvanishing at the field
point `x`. Since `x` is `v` restricted to the only point of `Spec K[ε]`,
clause 1 makes this equivalent to generation at that point.

## Provenance

The provenance is derived internal section calculus. No literature theorem
is claimed. The seven clauses were assembled by Worker 354 in a shared draft
for this task. It reuses Worker 899's field-point and right-cancellation
calculus from the parent task `eda1f6ff-d036-4f23-aabb-7663e7606b42`, the
algebraically closed separating-line-bundle proof, which needs exactly
these consequences. Mathematically, clause 1 is the familiar description of
the generation locus `X_s = {x | s ∉ 𝔪_x L_x}` through residue-field points.
The Library's comparison between residue-field nonvanishing and the
trivialization open is
`Langlands.SchemeModule.lineBundleResidueOpenComparison`. Clause 2 follows
from clause 1 and the published whole-locus formula
`Langlands.SchemeModule.tensorSectionGenerationLocus`. Clauses 3 and 4
express that a section generating at every image point frames the pulled
back line bundle. Clause 5 holds because `Spec K[ε]` has exactly one point,
the image of the augmentation.

These remarks describe the intended proof route only. The module imports
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`,
`Langlands.AlgebraicGeometry.Picard.LineBundleTensor`,
`Langlands.AlgebraicGeometry.Modules.TensorSections` and
`Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`, and none of the
comparison theorems named above. It defines no new section, tensor product,
pullback or locus, and it proves none of the seven clauses. The proof is the
separate obligation of a `lean.proof@1` successor task.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
