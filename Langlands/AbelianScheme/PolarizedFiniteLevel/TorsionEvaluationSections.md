# Torsion evaluations on global sections

This internal support unit computes the published torsion evaluation
`Datum.torsionEvaluation` (module
`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus`) on sections. Let
`a` be a datum over `S` with abelian scheme `π : A → S`, cubic bundle `L³`,
and rigidification module `V = π_* L³`. For a coefficient tuple `r`, let
`P_r = a.torsionPoint r : S → A` be the corresponding torsion section. The
torsion evaluation is the composite

`V ≅ 𝟙^* V ≅ (P_r ≫ π)^* V ≅ P_r^* π^* V → P_r^* L³`,

whose last map is `P_r^*` of the adjoint evaluation `π^* π_* L³ → L³`. The
unit shows that on global sections this composite is ordinary pullback of a
section along `P_r`.

## Declarations

- `pullback_map_app_sectionPullbackLE`: for a morphism `f : X → Y`, a map
  of module sheaves `φ : M → N` on `Y`, opens `U ≤ f⁻¹ V`, and a section
  `m` of `M` over `V`, the pullback map `f^* φ` sends the restricted pulled
  back section `sectionPullbackLE f M h m` to
  `sectionPullbackLE f N h (φ m)`.
- `pullbackId_inv_app_eq_sectionPullbackLE`: the inverse of the identity
  comparison `M ≅ 𝟙^* M` sends a section `m` over `U` to its pullback
  `sectionPullbackLE (𝟙 X) M (le_refl U) m` along the identity.
- `Datum.torsionEvaluation_app_top`: for every global section `σ` of `V`,

  `(a.torsionEvaluation r).app ⊤ σ = pullbackSection (a.torsionPoint r) a.cubicBundle.obj σ`.

  Here `σ` is read as a section of `L³` over `π⁻¹(S) = A`.

## Proofs

The first lemma unfolds `sectionPullbackLE` and combines the naturality of
section pullback (`sectionPullback_naturality`, Library module
`Langlands.AlgebraicGeometry.SectionPullback`) with the naturality of the
module map `f^* φ` under restriction.

The second lemma rewrites the left-hand side with `sectionPullback_id`, which
says that pulling back along the identity, followed by the forward identity
comparison, returns the section. Composing with the inverse comparison and
using `Iso.hom_inv_id` gives the claim.

The main theorem follows the four factors of the composite on the section
`σ`:

1. the identity comparison gives `sectionPullbackLE (𝟙 S) V σ` (second lemma);
2. `pullbackCongr_hom_sectionPullbackLE` (Library module
   `Langlands.AlgebraicGeometry.Modules.PullbackAffineSections`) changes the
   morphism to `P_r ≫ π`;
3. `pullbackComp_inv_sectionPullbackLE` (same module) splits the pullback
   into `sectionPullbackLE P_r (π^* V) (sectionPullbackLE π V σ)`;
4. the first lemma moves the evaluation map inside. The evaluation of
   `sectionPullbackLE π V σ` is `σ`, by
   `Datum.cubicEvaluationAdjoint_eq_evaluationAdjoint` and
   `evaluationAdjoint_sectionPullback` (Library modules
   `CubicEvaluation` and `ProjectiveBundle.EvaluationAdjoint`).

The right-hand side is converted at the start with
`pullbackSection_eq_sectionPullback` and `sectionPullbackLE_self`. The
unfolded composite is identified with the nested application by `rfl`, and
the four equations are rewritten in turn.
