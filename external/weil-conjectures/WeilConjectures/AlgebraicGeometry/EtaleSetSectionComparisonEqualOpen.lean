/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen
import WeilConjectures.AlgebraicGeometry.EtaleSetCartesianUnitEquality

/-! # The agreement open for canonical inverse-image section comparisons
Source: Stacks Project, Tag 09XM, with inverse-image unit compatibility in
Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-section-comparison-equal-open). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XM, applied to the pulled-back sheaf on the
étale object `V ×[R] S`; Sites Tags 03CB and 03CC for composition of inverse images.
(blueprint: lem-weil-pbc-sets-section-comparison-equal-open).

Proof:
1. Put F = f⁻¹G and Q = V ×[R] S. Apply
   `existsUnique_etaleSections_equal_open` to `(F, Q, s, t)`, giving the unique
   agreement open U in Q with its arbitrary-map factorization criterion.
2. For h ≫ f = k put P = V ×[R] T and p = (id_V,h) : P → Q. Write q : Q → S
   and q' : P → T for the étale second projections. Inverse image along an étale
   map is restriction, hence F(Q) is canonically Γ(Q,q⁻¹F), and (h⁻¹F)(P) is
   Γ(P,q'⁻¹h⁻¹F). Under these isomorphisms, restriction along p is the unit for h
   evaluated on Q: use p ≫ q = q' ≫ h, naturality of units in the site object,
   and the composition unit equation. The latter equation sends both paths
   around this cartesian square to the unit for its outer composite. The
   canonical iterated-pullback isomorphism is specified by its projections.
   Compose with h⁻¹f⁻¹G ≅ k⁻¹G and that pullback isomorphism. The resulting
   map is exactly etaleSetSectionComparison h f k hk G V. These identifications
   are isomorphisms, so its two values agree exactly when s,t restricted along p
   agree in the agreement-open factorization criterion.
3. That criterion identifies equality with factorization of p through U. A map
   factors through an open immersion exactly when all its points lie in U,
   by the open immersion lifting property; equivalently p⁻¹U is top.
Empty domains satisfy the same equivalence. For s=t the unique open U is top.
No limiting or finiteness hypothesis is used. -/
theorem etaleSetSectionComparison_equal_open
    {R S : Scheme.{u}} (f : S ⟶ R)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (V : R.Etale)
    (s t : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))) :
    ∃ U : (pullback V.hom f).Opens,
      ∀ (T : Scheme.{u}) (h : T ⟶ S) (k : T ⟶ R) (hk : h ≫ f = k),
        etaleSetSectionComparison h f k hk G V s =
          etaleSetSectionComparison h f k hk G V t ↔
        (pullback.map V.hom k V.hom f (𝟙 V.left) h (𝟙 R)
          (by simp) (by simpa using hk.symm)) ⁻¹ᵁ U = ⊤ := by
  classical
  let F := (Scheme.etaleSetPullback f).obj G
  let Q := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  obtain ⟨U, hU, _⟩ := existsUnique_etaleSections_equal_open S F Q s t
  refine ⟨U, ?_⟩
  intro T h k hk
  subst k
  let A := (MorphismProperty.Over.pullback @Etale ⊤ (h ≫ f)).obj V
  let e : A ≅ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Q :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).app V
  let p : A.left ⟶ Q.left :=
    pullback.map V.hom (h ≫ f) V.hom f (𝟙 V.left) h (𝟙 R)
      (by simp) (by simp)
  have hp : e.hom.left ≫ pullback.fst Q.hom h = p := by
    apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullback, Functor.id_obj, Functor.const_obj_obj,
        Iso.app_hom, MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
        Category.id_comp, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
        Category.comp_id, A, Q, e, p]
      exact pullbackLeftPullbackSndIso_inv_fst V.hom f h
    · simp only [MorphismProperty.Over.pullback, Functor.id_obj, Functor.const_obj_obj,
        Iso.app_hom, MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
        Category.id_comp, Category.assoc, limit.lift_π, PullbackCone.mk_π_app, A, Q, e, p]
      exact pullbackLeftPullbackSndIso_inv_fst_snd V.hom f h
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op Q)
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h
  let γ := (c.hom.app G).hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj Q))
  let H := (Scheme.etaleSetPullback (h ≫ f)).obj G
  let τ := H.obj.map e.hom.op
  have hγ : Function.Injective γ := CategoryTheory.injective_of_mono γ
  have hτ : Function.Injective τ := CategoryTheory.injective_of_mono τ
  have hcomparison :
      etaleSetSectionComparison h f (h ≫ f) rfl G V s =
          etaleSetSectionComparison h f (h ≫ f) rfl G V t ↔ η s = η t := by
    change τ (γ (η s)) = τ (γ (η t)) ↔ η s = η t
    exact ⟨fun heq ↦ hγ (hτ heq), fun heq ↦ congrArg (fun x ↦ τ (γ x)) heq⟩
  have hfactor := hU A.left p
  have hunit := etaleSetCartesianUnit_eq_iff h F Q A e p hp s t
  have hopen : (∃ b : A.left ⟶ U.toScheme, b ≫ U.ι = p) ↔ p ⁻¹ᵁ U = ⊤ := by
    constructor
    · rintro ⟨b, hb⟩
      apply top_unique
      intro x _
      change p x ∈ U
      have hx := congrArg (fun a : A.left ⟶ Q.left ↦ a x) hb
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hx
      rw [← hx]
      exact (b x).property
    · intro hall
      refine ⟨IsOpenImmersion.lift U.ι p ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro x ⟨y, rfl⟩
      have hy : y ∈ p ⁻¹ᵁ U := by rw [hall]; trivial
      exact hy
  exact hcomparison.trans (hunit.trans (hfactor.symm.trans hopen))


end AlgebraicGeometry
