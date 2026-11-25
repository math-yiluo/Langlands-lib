/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 2000] CategoryTheory.sheafIsAbelian CategoryTheory.Abelian.hasPushouts
namespace CategoryTheory.Sheaf.Torsor
private noncomputable abbrev integers (S : AlgebraicGeometry.Scheme.{u}) :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}).obj
    (AddCommGrpCat.of (ULift.{max u w + 1} ℤ))

private noncomputable abbrev one (S : AlgebraicGeometry.Scheme.{u}) (U : S.Etaleᵒᵖ) :
    (integers.{u, w} S).obj.obj U :=
  (toSheafify S.smallEtaleTopology
    ((Functor.const S.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)))).app U ⟨1⟩

private theorem one_natural (S : AlgebraicGeometry.Scheme.{u})
    {U V : S.Etaleᵒᵖ} (f : U ⟶ V) :
    (integers.{u, w} S).obj.map f (one S U) = one S V := by
  exact (ConcreteCategory.congr_hom ((toSheafify S.smallEtaleTopology
    ((Functor.const S.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)))).naturality f) ⟨1⟩).symm

private theorem integer_hom_ext (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} (T : Torsor G)
    {A : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}}
    (a b : integers.{u, w} S ⟶ A)
    (h : ∀ U, T.sheaf.obj.obj U → a.hom.app U (one S U) = b.hom.app U (one S U)) :
    a = b := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext S.smallEtaleTopology _ _ A.property
  apply NatTrans.ext
  funext U
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  change a.hom.app U (one S U) = b.hom.app U (one S U)
  apply T.ext_of_nonempty ((sheafCompose S.smallEtaleTopology (forget _)).obj A)
  intro V f ht
  change A.obj.map f.op (a.hom.app U (one S U)) =
    A.obj.map f.op (b.hom.app U (one S U))
  have ha := ConcreteCategory.congr_hom (a.hom.naturality f.op) (one S U)
  have hb := ConcreteCategory.congr_hom (b.hom.naturality f.op) (one S U)
  change a.hom.app _ ((integers S).obj.map f.op (one S U)) =
    A.obj.map f.op (a.hom.app U (one S U)) at ha
  change b.hom.app _ ((integers S).obj.map f.op (one S U)) =
    A.obj.map f.op (b.hom.app U (one S U)) at hb
  rw [one_natural] at ha hb
  exact ha.symm.trans ((h _ ht.some).trans hb)

private theorem projection_epi (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T) : Epi E.projection := by
  constructor
  intro A a b hab
  apply integer_hom_ext S T
  intro U t
  have h := congrArg (fun f ↦ f.hom.app U (E.generator U t)) hab
  change a.hom.app U (E.projection.hom.app U (E.generator U t)) =
    b.hom.app U (E.projection.hom.app U (E.generator U t)) at h
  simpa only [E.projection_generator] using h

private theorem presentation_hom_ext (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T)
    {A : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} (a b : E.middle ⟶ A)
    (hi : E.inclusion ≫ a = E.inclusion ≫ b)
    (hj : ∀ U t, a.hom.app U (E.generator U t) = b.hom.app U (E.generator U t)) :
    a = b := by
  obtain ⟨l, _, hl⟩ := E.universal A (E.inclusion ≫ b)
    (fun U t ↦ b.hom.app U (E.generator U t))
    (fun U V f t ↦ by
      rw [← ConcreteCategory.comp_apply, ← b.hom.naturality, ConcreteCategory.comp_apply,
        E.generator_natural])
    (fun U g t ↦ by rw [E.generator_vadd, map_add]; rfl)
  exact (hl a ⟨hi, hj⟩).trans (hl b ⟨rfl, fun _ _ ↦ rfl⟩).symm

private theorem projection_factors (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T)
    {A : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}}
    (k : E.middle ⟶ A) (hk : E.inclusion ≫ k = 0) :
    ∃ l : integers.{u, w} S ⟶ A, E.projection ≫ l = k := by
  obtain ⟨σ, hσ⟩ := T.exists_section_of_invariant
    ((sheafCompose S.smallEtaleTopology (forget _)).obj A)
    (terminalIsTerminal (C := S.Etale))
    (fun U t ↦ k.hom.app U (E.generator U t))
    (fun U V f t ↦ by
      change A.obj.map f (k.hom.app U (E.generator U t)) = _
      rw [← ConcreteCategory.comp_apply, ← k.hom.naturality, ConcreteCategory.comp_apply,
        E.generator_natural])
    (fun U g t ↦ by
      change k.hom.app U (E.generator U (T.vadd U g t)) = _
      rw [E.generator_vadd, map_add, hom_app_hom_app_of_comp_eq_zero hk, add_zero])
  let β : (Functor.const S.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)) ⟶ A.obj :=
    { app U := AddCommGrpCat.ofHom
        (uliftZMultiplesHom _ (A.obj.map (terminal.from U.unop).op σ))
      naturality U V f := by
        ext n
        change n.down • A.obj.map (terminal.from V.unop).op σ =
          A.obj.map f (n.down • A.obj.map (terminal.from U.unop).op σ)
        have hf : (terminal.from U.unop).op ≫ f = (terminal.from V.unop).op := by
          apply Quiver.Hom.unop_inj
          exact terminalIsTerminal.hom_ext _ _
        rw [map_zsmul, ← ConcreteCategory.comp_apply, ← A.obj.map_comp, hf] }
  let l : integers.{u, w} S ⟶ A := ⟨sheafifyLift S.smallEtaleTopology β A.property⟩
  have hl (U : S.Etaleᵒᵖ) : l.hom.app U (one S U) =
      A.obj.map (terminal.from U.unop).op σ := by
    have h := congrArg (fun f : (Functor.const S.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)) ⟶ A.obj ↦ f.app U ⟨1⟩)
      (toSheafify_sheafifyLift S.smallEtaleTopology β A.property)
    change l.hom.app U (one S U) =
      (1 : ℤ) • A.obj.map (terminal.from U.unop).op σ at h
    simpa only [one_zsmul] using h
  refine ⟨l, presentation_hom_ext S E _ k ?_ ?_⟩
  · rw [← Category.assoc, E.inclusion_projection, zero_comp, hk]
  · intro U t
    change l.hom.app U (E.projection.hom.app U (E.generator U t)) = _
    rw [E.projection_generator, hl]
    exact (hσ U t).symm

private theorem inclusion_mono (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T) : Mono E.inclusion := by
  have : IsGrothendieckAbelian.{max u w + 1}
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  have : S.smallEtaleTopology.WEqualsLocallyBijective
      AddCommGrpCat.{max u w + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let K := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
    (cokernel.condition _)
  have hK : K.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨s, ⟨e⟩⟩ := exists_equiv_lifts (terminalIsTerminal (C := S.Etale)) hK T
  obtain ⟨l, hl, _⟩ := E.universal (Injective.under G) (Injective.ι G)
    (fun U t ↦ (e.iso.hom.hom.app U t).val)
    (fun U V f t ↦ by
      exact congrArg Subtype.val
        (ConcreteCategory.congr_hom (e.iso.hom.hom.naturality f) t).symm)
    (fun U g t ↦ congrArg Subtype.val (e.map_vadd U g t))
  exact mono_of_mono_fac hl.1

/-- The extension presentation sequence is short exact.
Source: Stacks 03AJ. Proof: construct the augmentation as a cokernel and verify
exactness using the universal property and local torsor sections.
(auxiliary; not a blueprint node) -/
theorem extension_presentation_shortExact (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T) :
    (ShortComplex.mk E.inclusion E.projection E.inclusion_projection).ShortExact := by
  classical
  have := inclusion_mono S E
  have := projection_epi S E
  have hc : IsColimit (CokernelCofork.ofπ E.projection E.inclusion_projection) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro A k hk
    exact ⟨(projection_factors S E k hk).choose, (projection_factors S E k hk).choose_spec⟩
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ hc }
end CategoryTheory.Sheaf.Torsor
