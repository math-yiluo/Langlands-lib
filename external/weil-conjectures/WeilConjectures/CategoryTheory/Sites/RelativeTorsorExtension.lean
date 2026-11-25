/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact

/-! # Relative extensions of a torsor

Source: Stacks Project, Tags 03AJ and 0A45. The quotient of the free torsor
extension by the prescribed lift on an open subset gives the relative class.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ShortComplex

private theorem quotientLift_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (e : S.X₃ ≅ T.X₂) (h : T.X₁ ⟶ S.X₂) (hh : h ≫ S.g ≫ e.hom = T.f) :
    let a := S.f ≫ cokernel.π h
    let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g)
      (by calc
        h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
          simp only [Category.assoc]
        _ = 0 := by rw [hh, T.zero])
    ∃ hz : a ≫ b = 0, (ShortComplex.mk a b hz).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have hzcomp : h ≫ (S.g ≫ e.hom ≫ T.g) = 0 := by
    calc
      h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
        simp only [Category.assoc]
      _ = 0 := by rw [hh, T.zero]
  let a := S.f ≫ cokernel.π h
  let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g) hzcomp
  have hb : cokernel.π h ≫ b = S.g ≫ e.hom ≫ T.g := cokernel.π_desc _ _ _
  have hab : a ≫ b = 0 := by
    dsimp only [a]
    rw [Category.assoc, hb, ← Category.assoc, S.zero, zero_comp]
  have : Mono h := mono_of_mono_fac hh
  have hhc : (ShortComplex.mk h (cokernel.π h) (cokernel.condition h)).ShortExact :=
    { exact := ShortComplex.exact_cokernel h }
  have ha : Mono a := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    let k := kernel.ι a
    have hk : (k ≫ S.f) ≫ cokernel.π h = 0 := by
      rw [Category.assoc]
      exact kernel.condition a
    let r := hhc.fIsKernel.lift (KernelFork.ofι (k ≫ S.f) hk)
    have hr : r ≫ h = k ≫ S.f := hhc.fIsKernel.fac _ WalkingParallelPair.zero
    have hrt : r ≫ T.f = 0 := by
      calc
        r ≫ T.f = (r ≫ h) ≫ S.g ≫ e.hom := by rw [← hh]; simp only [Category.assoc]
        _ = 0 := by rw [hr, Category.assoc, reassoc_of% S.zero, zero_comp, comp_zero]
    have hrzero : r = 0 := (cancel_mono T.f).1 (by simpa using hrt)
    have hka : k ≫ S.f = 0 := by rw [← hr, hrzero, zero_comp]
    exact (cancel_mono S.f).1 (by simpa using hka)
  have hbepi : Epi b := epi_of_epi_fac hb
  have hbCoker : IsColimit (CokernelCofork.ofπ b hab) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro M f hf
    have hSf : S.f ≫ (cokernel.π h ≫ f) = 0 := by
      rw [← Category.assoc]
      exact hf
    let q := hS.gIsCokernel.desc (CokernelCofork.ofπ (cokernel.π h ≫ f) hSf)
    have hq : S.g ≫ q = cokernel.π h ≫ f := hS.gIsCokernel.fac _ WalkingParallelPair.one
    have htq : T.f ≫ (e.inv ≫ q) = 0 := by
      calc
        T.f ≫ (e.inv ≫ q) = h ≫ (S.g ≫ q) := by
          rw [← hh]
          simp only [Category.assoc, e.hom_inv_id_assoc]
        _ = 0 := by rw [hq, ← Category.assoc, cokernel.condition, zero_comp]
    let r := hT.gIsCokernel.desc (CokernelCofork.ofπ (e.inv ≫ q) htq)
    have hr : T.g ≫ r = e.inv ≫ q := hT.gIsCokernel.fac _ WalkingParallelPair.one
    refine ⟨r, ?_⟩
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, hb, Category.assoc, Category.assoc, hr,
      ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp, hq]
  exact ⟨hab, { exact := ShortComplex.exact_of_g_is_cokernel _ hbCoker }⟩

end CategoryTheory.ShortComplex

namespace CategoryTheory.Sheaf.Torsor
open AlgebraicGeometry Abelian

private abbrev integral (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def one (X : Scheme.{u}) (U : X.Etaleᵒᵖ) : (integral X).obj.obj U :=
  (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩

private def RelativeSpec (X : Scheme.{u})
    {G Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (P : Torsor G)
    (U : X.Etale) (τ : P.sheaf.obj.obj (op U)) (q : integral X ⟶ Q)
    (β : Ext Q G 1) : Prop :=
  ∃ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E) (b : E ⟶ Q)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ V g p, f.app V (P.vadd V g p) = (show E.obj.obj V from f.app V p) + a.hom.app V g) ∧
    (∀ V p, b.hom.app V (f.app V p) = q.hom.app V (one X V)) ∧
    (show E.obj.obj (op U) from f.app (op U) τ) = 0 ∧ β = hE.extClass

private theorem relativeSpec_existsUnique (X : Scheme.{u})
    {G Q L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (P : Torsor G)
    (U : X.Etale) (τ : P.sheaf.obj.obj (op U))
    (t : L ⟶ integral X) (q : integral X ⟶ Q) (htq : t ≫ q = 0)
    (hT : (ShortComplex.mk t q htq).ShortExact)
    (η : ∀ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      (L ⟶ A) ≃+ A.obj.obj (op U))
    (hη : ∀ {A B} (f : A ⟶ B) (g : L ⟶ A),
      η B (g ≫ f) = f.hom.app (op U) (η A g))
    (hηt : η (integral X) t = one X (op U)) :
    ∃! β : Ext Q G 1, RelativeSpec X P U τ q β := by
  obtain ⟨E⟩ : Nonempty (ExtensionPresentation.{u, u} X P) :=
    nonempty_extensionPresentation X P
  let S := ShortComplex.mk E.inclusion E.projection E.inclusion_projection
  have hS : S.ShortExact := extension_presentation_shortExact X E
  let h := (η E.middle).symm (E.generator (op U) τ)
  have hp : h ≫ E.projection = t := by
    apply (η (integral X)).injective
    rw [hη, AddEquiv.apply_symm_apply, hηt]
    exact E.projection_generator _ _
  obtain ⟨hab, hE⟩ := ShortComplex.quotientLift_shortExact S
    (ShortComplex.mk t q htq) hS hT (by exact CategoryTheory.Iso.refl (integral X)) h (by
      change h ≫ E.projection ≫ 𝟙 _ = t
      simpa using hp)
  let a := E.inclusion ≫ cokernel.π h
  let b := cokernel.desc h (E.projection ≫ q) (by rw [← Category.assoc, hp, htq])
  change (ShortComplex.mk a b hab).ShortExact at hE
  let f : P.sheaf.obj ⟶ (cokernel h).obj ⋙ forget AddCommGrpCat.{u + 1} :=
    { app V := TypeCat.ofHom fun p => (cokernel.π h).hom.app V (E.generator V p)
      naturality V V' k := by
        ext p
        change (cokernel.π h).hom.app V' (E.generator V' (P.sheaf.obj.map k p)) =
          (cokernel h).obj.map k ((cokernel.π h).hom.app V (E.generator V p))
        rw [← E.generator_natural]
        exact ConcreteCategory.congr_hom ((cokernel.π h).hom.naturality k) _ }
  have hfa V g p : f.app V (P.vadd V g p) =
      (show (cokernel h).obj.obj V from f.app V p) + a.hom.app V g := by
    change (cokernel.π h).hom.app V (E.generator V (P.vadd V g p)) = _
    rw [E.generator_vadd, map_add]
    rfl
  have hfb V p : b.hom.app V (f.app V p) = q.hom.app V (one X V) := by
    change ((cokernel.π h ≫ b).hom.app V) (E.generator V p) = _
    rw [cokernel.π_desc]
    change q.hom.app V (E.projection.hom.app V (E.generator V p)) = _
    rw [E.projection_generator]
    rfl
  have hfτ : (show (cokernel h).obj.obj (op U) from f.app (op U) τ) = 0 := by
    change (cokernel.π h).hom.app (op U) (E.generator (op U) τ) = 0
    have hh := hη (cokernel.π h) h
    have he : (η E.middle) h = E.generator (op U) τ := AddEquiv.apply_symm_apply _ _
    rw [cokernel.condition, map_zero, he] at hh
    exact hh.symm
  refine ⟨hE.extClass, ⟨_, a, b, hab, hE, f, hfa, hfb, hfτ, rfl⟩, ?_⟩
  rintro β ⟨E', a', b', hab', hE', f', hf'a, hf'b, hf'τ, rfl⟩
  obtain ⟨α, ⟨hαa, hαf⟩, hαuniq⟩ := E.universal E' a'
    (fun V p => f'.app V p)
    (fun V V' k p => (ConcreteCategory.congr_hom (f'.naturality k) p).symm)
    hf'a
  have hαb : α ≫ b' = E.projection ≫ q := by
    obtain ⟨l, hl, huniq⟩ := E.universal Q 0
      (fun V _ => q.hom.app V (one X V))
      (by
        intro V V' k p
        rw [← ConcreteCategory.comp_apply, ← q.hom.naturality,
          ConcreteCategory.comp_apply]
        congr 1
        exact ConcreteCategory.congr_hom
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality k)
          ⟨1⟩ |>.symm)
      (by intro V g p; change _ = _ + 0; exact (add_zero _).symm)
    apply (huniq _ ⟨by rw [← Category.assoc, hαa, hab'], ?_⟩).trans
      (huniq _ ⟨by rw [← Category.assoc, E.inclusion_projection, zero_comp], ?_⟩).symm
    · intro V p
      change b'.hom.app V (α.hom.app V (E.generator V p)) = _
      rw [hαf, hf'b]
    · intro V p
      change q.hom.app V (E.projection.hom.app V (E.generator V p)) = _
      rw [E.projection_generator]
      rfl
  have hhα : h ≫ α = 0 := by
    apply (η E').injective
    rw [hη, map_zero]
    change α.hom.app (op U) ((η E.middle) ((η E.middle).symm _)) = 0
    rw [AddEquiv.apply_symm_apply, hαf]
    exact hf'τ
  let α' := cokernel.desc h α hhα
  have hα'a : a ≫ α' = a' := by
    rw [Category.assoc, cokernel.π_desc]
    exact hαa
  have hα'b : α' ≫ b' = b := by
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc]
    exact hαb
  have hh := hE.extClass_naturality hE'
    (ShortComplex.homMk (𝟙 _) α' (𝟙 _) (by simpa using hα'a.symm)
      (by simpa using hα'b))
  change hE.extClass.comp (Ext.mk₀ (𝟙 G)) (add_zero 1) =
    (Ext.mk₀ (𝟙 Q)).comp hE'.extClass (zero_add 1) at hh
  simpa only [Ext.comp_mk₀_id, Ext.mk₀_id_comp] using hh.symm

/-- A torsor with a specified section determines a unique relative extension class
whenever the integer source has its normalized open-support presentation.
Source: Stacks Project, Tag 03AJ, free abelian presentation, and Tag 0A45, excision.
(auxiliary; not a blueprint node)
Proof: take the free extension of the torsor by the constant integers. The sections
adjunction turns the chosen torsor section into a lift of the open-source inclusion.
Kill this lift by a cokernel. The two short exact sequences show that the quotient
is an extension of the supported source by G. Any competing equivariant torsor map
extends uniquely over the free presentation and kills the same lift. It therefore
factors through this cokernel, inducing identity on both ends of the extensions.
Naturality of extension classes proves uniqueness. This also covers zero sources
and the empty open, since all constructions are categorical cokernels. -/
theorem relative_extension_existsUnique (X : Scheme.{u})
    {G Q L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (P : Torsor G)
    (U : X.Etale) (τ : P.sheaf.obj.obj (op U))
    (t : L ⟶ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
    (q : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ Q) (htq : t ≫ q = 0)
    (hT : (ShortComplex.mk t q htq).ShortExact)
    (η : ∀ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      (L ⟶ A) ≃+ A.obj.obj (op U))
    (hη : ∀ {A B} (f : A ⟶ B) (g : L ⟶ A),
      η B (g ≫ f) = f.hom.app (op U) (η A g))
    (hηt : η (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) t = (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) ⟨1⟩) :
    ∃! β : Ext Q G 1,
  ∃ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E) (b : E ⟶ Q)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ V g p, f.app V (P.vadd V g p) = (show E.obj.obj V from f.app V p) + a.hom.app V g) ∧
    (∀ V p, b.hom.app V (f.app V p) = q.hom.app V ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) ∧
    (show E.obj.obj (op U) from f.app (op U) τ) = 0 ∧ β = hE.extClass := by
  exact relativeSpec_existsUnique X P U τ t q htq hT η hη hηt

end CategoryTheory.Sheaf.Torsor
