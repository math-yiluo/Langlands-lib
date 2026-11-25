/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorSignedRepresentatives
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorLocalizationSections
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass
/-! Independent comparison result for the principal torsor sign calculation.

## References

* Stacks 03AJ, 06XU
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale

/-- If an extension `S` of `S.X₃` by `S.X₁` maps to an injective resolution of `S.X₁` by `h`
extending the augmentation, and `c` is the induced map on `S.X₃`, then `c` represents minus
the extension class. -/
theorem InjectiveResolution.extMk_eq_neg_extClass {T : Scheme.{u}}
    {S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (R : InjectiveResolution S.X₁) (h : S.X₂ ⟶ R.cocomplex.X 0) (hh : S.f ≫ h = R.ι.f 0)
    (c : S.X₃ ⟶ R.cocomplex.X 1) (hc : S.g ≫ c = h ≫ R.cocomplex.d 0 1)
    (hc' : c ≫ R.cocomplex.d 1 2 = 0) :
    R.extMk c 2 rfl hc' = -hS.extClass := by
  let c' := R.cocomplex.liftCycles c 2 (by simp) hc'
  have hcc : c' ≫ R.cocomplex.iCycles 1 = c := R.cocomplex.liftCycles_i c 2 (by simp) hc'
  let ψ : S ⟶ resolutionLiftSequence T R :=
    { τ₁ := 𝟙 _
      τ₂ := h
      τ₃ := c'
      comm₁₂ := by simpa [resolutionLiftSequence] using hh.symm
      comm₂₃ := by
        rw [← cancel_mono (R.cocomplex.iCycles 1)]
        simp [resolutionLiftSequence, c', hc] }
  have hnat := hS.extClass_naturality (resolutionLiftSequence_shortExact T R) ψ
  rw [Ext.comp_mk₀_id] at hnat
  have hfirst := R.extMk_firstCycles _ (resolutionLiftSequence_shortExact T R)
  have he : R.extMk c 2 rfl hc' =
      R.extMk (c' ≫ R.cocomplex.iCycles 1) 2 rfl (by simp) := by
    congr 1
    exact hcc.symm
  rw [he, ← R.mk₀_comp_extMk _ _ _ (by simp), hfirst, Ext.comp_neg]
  exact congrArg Neg.neg hnat.symm
/-- A framed extension is the inverse-section localization pushout and its normalized
relative class is minus the class of (0,aug(g)). -/
theorem principalTorsorFramedComparison
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) :
  ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (P : Sheaf.Torsor G)
    (e : P.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (s : P.sheaf.obj.obj (op (Scheme.Etale.mk W.ι)))
    (g : G.obj.obj (op (Scheme.Etale.mk W.ι)))
    (_hs : s = P.vadd (op (Scheme.Etale.mk W.ι)) g
      (P.sheaf.obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op e))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : G ⟶ E) (b : E ⟶ (principalTorsorLocalization i W h).X₃)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (F : P.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (_hF : ∀ (U : T.Etaleᵒᵖ) (x : G.obj.obj U) (p : P.sheaf.obj.obj U),
      @id (E.obj.obj U) (F.app U (P.vadd U x p)) = F.app U p + a.hom.app U x)
    (_hbF : ∀ (U : T.Etaleᵒᵖ) (p : P.sheaf.obj.obj U),
      b.hom.app U (F.app U p) = (principalTorsorLocalization i W h).g.hom.app U
        (torsorExtensionOne T U.unop))
    (_hFs : @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
      (F.app (op (Scheme.Etale.mk W.ι)) s) = 0),
    (∃ hL : (principalTorsorLocalization i W h).ShortExact,
      hE.extClass = hL.extClass.comp
        (Ext.mk₀ ((C.openSection T Z i W h G).symm (-g))) (add_zero 1)) ∧
    ∀ (L : InjectiveResolution G)
      (y : relativeCohomology T (Scheme.Etale.mk W.ι) L 1),
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) L.cocomplex 0 0
        ((L.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) y →
      C.relative T Z i W h G L 0 hE.extClass = -y := by
  intro T Z i _ W h G P e s g hs E a b hab hE F hF hbF hFs
  have hg := principalTorsorLocalization_g_one i W h (C.openSection T Z i W h)
    (hC.1 T Z i W h) (hC.2.1 T Z i W h)
  have hFe : E.obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op
      (F.app (op (Scheme.Etale.mk (𝟙 T))) e) = a.hom.app (op (Scheme.Etale.mk W.ι)) (-g) := by
    have hn := ConcreteCategory.congr_hom (F.naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op) e
    have h0 := hF _ g (P.sheaf.obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op e)
    rw [← hs, hFs] at h0
    simp only [ConcreteCategory.comp_apply] at hn
    rw [map_neg, eq_neg_iff_add_eq_zero]
    exact (congrArg (· + a.hom.app (op (Scheme.Etale.mk W.ι)) g) hn).symm.trans h0.symm
  refine ⟨⟨principalTorsorLocalization_shortExact i W h, ?_⟩, ?_⟩
  · let φ₂ := (integralSectionEquiv T E).symm (F.app _ e)
    have hφ₂ : φ₂.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) = F.app _ e := by
      rw [← integralSectionEquiv_apply, AddEquiv.apply_symm_apply]
    let ψ : principalTorsorLocalization i W h ⟶ ShortComplex.mk a b hab :=
      { τ₁ := (C.openSection T Z i W h G).symm (-g)
        τ₂ := φ₂
        τ₃ := 𝟙 _
        comm₁₂ := by
          apply (C.openSection T Z i W h E).injective
          rw [hC.1 T Z i W h _ _ a, hC.1 T Z i W h _ _ φ₂, hC.2.1 T Z i W h,
            AddEquiv.apply_symm_apply, integral_hom_app_one, hφ₂, hFe]
        comm₂₃ := by
          apply (integralSectionEquiv T _).injective
          rw [integralSectionEquiv_apply, integralSectionEquiv_apply, Category.comp_id]
          exact (congrArg (b.hom.app (op (Scheme.Etale.mk (𝟙 T)))) hφ₂).trans (hbF _ e) }
    have hnat := (principalTorsorLocalization_shortExact i W h).extClass_naturality hE ψ
    rw [Ext.mk₀_id_comp] at hnat
    exact hnat.symm
  · intro L y hy
    have := hE.mono_f
    have := hE.epi_g
    let k : E ⟶ L.cocomplex.X 0 := Injective.factorThru (L.ι.f 0) a
    have hak : a ≫ k = L.ι.f 0 := Injective.comp_factorThru _ _
    obtain ⟨c, hc⟩ : ∃ c : _ ⟶ L.cocomplex.X 1, b ≫ c = k ≫ L.cocomplex.d 0 1 :=
      ⟨hE.exact.desc (k ≫ L.cocomplex.d 0 1) (by rw [reassoc_of% hak,
        L.ι_f_zero_comp_complex_d]), hE.exact.g_desc _ _⟩
    have hc' : c ≫ L.cocomplex.d 1 2 = 0 := by
      rw [← cancel_epi b, reassoc_of% hc]
      simp
    have hext : hE.extClass = -L.extMk c 2 rfl hc' := by
      rw [InjectiveResolution.extMk_eq_neg_extClass hE L k hak c hc hc', neg_neg]
    rw [hext, map_neg]
    congr 1
    let t := k.hom.app (op (Scheme.Etale.mk (𝟙 T))) (F.app _ e)
    have hbd := hy.add (torsorSignedRepresents_boundary T (Scheme.Etale.mk W.ι) L.cocomplex 0 t)
    refine (hC.2.2 T Z i W h G L 0 c hc').unique ?_
    have hc₁ : c.hom.app (op (Scheme.Etale.mk (𝟙 T))) (b.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (F.app _ e)) = (L.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) t :=
      congrArg (fun m ↦ m.hom.app (op (Scheme.Etale.mk (𝟙 T))) (F.app _ e)) hc
    have hk : k.hom.app (op (Scheme.Etale.mk W.ι)) (a.hom.app (op (Scheme.Etale.mk W.ι)) (-g)) =
        (L.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) (-g) :=
      congrArg (fun m ↦ m.hom.app (op (Scheme.Etale.mk W.ι)) (-g)) hak
    have hn := ConcreteCategory.congr_hom (k.hom.naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op) (F.app _ e)
    simp only [ConcreteCategory.comp_apply] at hn
    rw [zero_add, ← hc₁, hbF, ← hn, hFe, hk, map_neg, add_neg_cancel, add_zero] at hbd
    exact hbd
end AlgebraicGeometry.Etale
