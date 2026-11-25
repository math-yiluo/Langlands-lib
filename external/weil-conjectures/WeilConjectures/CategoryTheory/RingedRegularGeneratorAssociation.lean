/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Association of generators of a regular principal ideal sheaf

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
rank-one generator calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private theorem unitEnd_apply
    (f : End (SheafOfModules.unit (siteModuleRings O))) (U : Cᵒᵖ)
    (x : O.obj.obj U) :
    f.asHom.val.app U x = @Mul.mul (O.obj.obj U) inferInstance x
      (f.asHom.val.app U (1 : O.obj.obj U)) := by
  let f' : ModuleCat.of (O.obj.obj U) (O.obj.obj U) ⟶
      ModuleCat.of (O.obj.obj U) (O.obj.obj U) := f.asHom.val.app U
  change f' x = x * f' 1
  simpa only [smul_eq_mul, mul_one] using f'.hom.map_smul x (1 : O.obj.obj U)

private theorem epi_unit_isIso
    (f : End (SheafOfModules.unit (siteModuleRings O))) [Epi f.asHom] :
    IsIso f.asHom := by
  let q := (SheafOfModules.toSheaf (siteModuleRings O)).map f.asHom
  have : Epi q := inferInstance
  have : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' _ q).2 inferInstance
  have hinj (U : Cᵒᵖ) : Function.Injective (f.asHom.val.app U) := by
    intro x y hxy
    have hsheaf : Presieve.IsSheaf J (O.obj ⋙ forget CommRingCat) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        ((sheafCompose J (forget CommRingCat)).obj O).property
    apply (hsheaf.isSeparated _ (Presheaf.imageSieve_mem J q.hom
      (1 : O.obj.obj U))).ext
    rintro V g ⟨z, hz⟩
    change f.asHom.val.app (op V) z = O.obj.map g.op 1 at hz
    rw [map_one, unitEnd_apply O] at hz
    have hu : @IsUnit (O.obj.obj (op V)) inferInstance
        (f.asHom.val.app (op V) (1 : O.obj.obj (op V))) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨z, ?_⟩
      change @Mul.mul (O.obj.obj (op V)) inferInstance _ z = 1
      exact (mul_comm _ _).trans hz
    apply hu.mul_right_cancel
    have hn := congrArg (fun z ↦ O.obj.map g.op z) hxy
    have hx := PresheafOfModules.naturality_apply f.asHom.val g.op x
    have hy := PresheafOfModules.naturality_apply f.asHom.val g.op y
    have hh : f.asHom.val.app (op V) (O.obj.map g.op x) =
        f.asHom.val.app (op V) (O.obj.map g.op y) := hx.trans (hn.trans hy.symm)
    exact (unitEnd_apply O f (op V) (O.obj.map g.op x)).symm.trans
      (hh.trans (unitEnd_apply O f (op V) (O.obj.map g.op y)))
  have : Mono f.asHom := ⟨by
    intro M g h heq
    apply SheafOfModules.hom_ext
    ext U x
    apply hinj U
    exact congrArg (fun z ↦ z.val.app U x) heq⟩
  exact isIso_of_mono_of_epi f.asHom

private theorem sections_over_ext (M : SheafOfModules (siteModuleRings O)) (U : C)
    {s t : (M.over U).sections}
    (h : s.val (op (Over.mk (𝟙 U))) = t.val (op (Over.mk (𝟙 U)))) : s = t := by
  apply Subtype.ext
  funext V
  have hs := s.property (Over.homMk V.unop.hom :
    V.unop ⟶ Over.mk (𝟙 U)).op
  have ht := t.property (Over.homMk V.unop.hom :
    V.unop ⟶ Over.mk (𝟙 U)).op
  exact hs.symm.trans ((congrArg _ h).trans ht)

private theorem epi_of_generating_over
    (I : RingedSiteIdeal O) (a : (O.obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : C, IsRingedIdealGeneratingList O I.module I.inclusion U 1
      (fun _ ↦ a.val (op U)))
    (f : SheafOfModules.unit (siteModuleRings O) ⟶ I.module)
    (hf : f ≫ I.inclusion = (ringedKoszulScalar O a).asHom) : Epi f := by
  have hepi (U : C) : Epi (f.over U) := by
    obtain ⟨σ, e, hσ⟩ := ha U
    have hs (i : σ.I) : σ.s i =
        (I.module.over U).unitHomEquiv (f.over U) := by
      apply sections_over_ext O I.module U
      apply Subtype.ext
      have h := hσ i
      change ((σ.s i).val (op (Over.mk (𝟙 U))) : I.sections U).val =
        a.val (op U) at h
      change ((σ.s i).val (op (Over.mk (𝟙 U))) : I.sections U).val =
        (f.val.app (op U) (1 : O.obj.obj (op U)) : I.sections U).val
      have hh := congrArg (fun z ↦ z.val.app (op U) (1 : O.obj.obj (op U))) hf
      change (f.val.app (op U) (1 : O.obj.obj (op U)) : I.sections U).val =
        (ringedKoszulScalar O a).asHom.val.app (op U) (1 : O.obj.obj (op U)) at hh
      have hone : (ringedKoszulScalar O a).asHom.val.app (op U)
          (1 : O.obj.obj (op U)) = a.val (op U) := by
        change @Mul.mul (O.obj.obj (op U)) inferInstance 1 (a.val (op U)) = _
        exact one_mul _
      exact h.trans (hh.trans hone).symm
    let g : SheafOfModules.free σ.I ⟶ SheafOfModules.unit ((siteModuleRings O).over U) :=
      (SheafOfModules.freeHomEquiv _).symm
        (fun _ ↦ (SheafOfModules.unit _).unitHomEquiv (𝟙 _))
    have hfactor : g ≫ f.over U = σ.π := by
      apply (SheafOfModules.freeHomEquiv _).injective
      funext i
      rw [SheafOfModules.freeHomEquiv_comp_apply]
      dsimp only [SheafOfModules.GeneratingSections.π]
      simp only [g, Equiv.apply_symm_apply]
      simpa only [← SheafOfModules.unitHomEquiv_comp_apply, Category.id_comp] using
        (hs i).symm
    have : Epi (g ≫ f.over U) := by rw [hfactor]; infer_instance
    exact epi_of_epi g (f.over U)
  constructor
  intro M g h heq
  apply SheafOfModules.hom_ext
  ext U x
  have hlocal : f.over U.unop ≫ g.over U.unop = f.over U.unop ≫ h.over U.unop :=
    congrArg (fun z ↦ z.over U.unop) heq
  let := hepi U.unop
  have hlocal' := (cancel_epi (f.over U.unop)).mp hlocal
  exact congrArg (fun z ↦ z.val.app (op (Over.mk (𝟙 U.unop))) x) hlocal'

/-- Two global generators of a regular principal ideal sheaf differ by an invertible
rank-one scalar. No complexes or coefficient comparison enter this assertion.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
rank-one generator calculation.
(auxiliary; not a blueprint node).

Proof: regular multiplication by t identifies O with the ideal module. Lift a to
that module using its generating section on each slice; these lifts glue because
its inclusion is injective. The resulting O-to-ideal map is epic: on each slice
all the specified generators factor through it. Composing with the inverse of
multiplication by t gives an epic endomorphism of O. An epic rank-one scalar is
locally surjective on 1, hence locally a unit. It is consequently monic and epic,
and therefore invertible. Invert this scalar to obtain the displayed equation.
This proof includes a zero ring, an empty site and a zero ideal generated by a
regular element, since regularity then forces the ambient section ring to be zero. -/
theorem ringed_regular_generator_association
    (I : RingedSiteIdeal O) (t a : (O.obj ⋙ forget CommRingCat).sections)
    (ht : ∀ U : C, I.sections U = Ideal.span {t.val (op U)})
    (hreg : ∀ U : C, Function.Injective
      (fun x : O.obj.obj (op U) ↦ @Mul.mul (O.obj.obj (op U)) inferInstance (t.val (op U)) x))
    (ha : ∀ U : C, IsRingedIdealGeneratingList O I.module I.inclusion U 1
      (fun _ ↦ a.val (op U))) :
    ∃ c : SheafOfModules.unit (siteModuleRings O) ≅
        SheafOfModules.unit (siteModuleRings O),
      (ringedKoszulScalar O t).asHom = c.hom ≫ (ringedKoszulScalar O a).asHom := by
  have hmem (U : C) : a.val (op U) ∈ I.sections U := by
    obtain ⟨σ, e, hσ⟩ := ha U
    have h := hσ (e.symm 0)
    change ((σ.s (e.symm 0)).val (op (Over.mk (𝟙 U))) : I.sections U).val =
      a.val (op U) at h
    exact h ▸ ((σ.s (e.symm 0)).val (op (Over.mk (𝟙 U))) : I.sections U).property
  let ta : I.module.sections :=
    ⟨fun U ↦ ⟨a.val U, hmem U.unop⟩,
      fun f ↦ Subtype.ext (a.property f)⟩
  let tt : I.module.sections :=
    ⟨fun U ↦ ⟨t.val U, by rw [ht]; exact Ideal.subset_span (by simp)⟩,
      fun f ↦ Subtype.ext (t.property f)⟩
  let α := I.module.unitHomEquiv.symm ta
  let τ := I.module.unitHomEquiv.symm tt
  have hα : α ≫ I.inclusion = (ringedKoszulScalar O a).asHom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change @Mul.mul (O.obj.obj U) inferInstance x (a.val U) =
      @Mul.mul (O.obj.obj U) inferInstance x (a.val U)
    rfl
  have hτ : τ ≫ I.inclusion = (ringedKoszulScalar O t).asHom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change @Mul.mul (O.obj.obj U) inferInstance x (t.val U) =
      @Mul.mul (O.obj.obj U) inferInstance x (t.val U)
    rfl
  have hbij (U : Cᵒᵖ) : Function.Bijective (τ.val.app U) := by
    constructor
    · intro x y h
      apply hreg U.unop
      have h' := congrArg Subtype.val h
      change @Mul.mul (O.obj.obj U) inferInstance x (t.val U) =
        @Mul.mul (O.obj.obj U) inferInstance y (t.val U) at h'
      exact (mul_comm _ _).trans (h'.trans (mul_comm _ _))
    · intro x
      let x' : I.sections U.unop := x
      have hx : x'.val ∈ Ideal.span {t.val U} := by
        rw [← ht]
        exact x'.property
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      refine ⟨y, Subtype.ext ?_⟩
      change @Mul.mul (O.obj.obj U) inferInstance y (t.val U) = x'.val
      exact (mul_comm _ _).trans hy.symm
  have hτiso : IsIso τ := by
    let e : (SheafOfModules.unit (siteModuleRings O)).val ≅ I.module.val :=
      PresheafOfModules.isoMk (fun U ↦
      LinearEquiv.toModuleIso (LinearEquiv.ofBijective (τ.val.app U).hom (hbij U)))
      (fun {_ _} f ↦ τ.val.naturality f)
    have he : (SheafOfModules.forget (siteModuleRings O)).map τ = e.hom := rfl
    have : IsIso ((SheafOfModules.forget (siteModuleRings O)).map τ) := by
      rw [he]
      infer_instance
    exact isIso_of_reflects_iso τ (SheafOfModules.forget (siteModuleRings O))
  have hαepi := epi_of_generating_over O I a ha α hα
  let u := α ≫ inv τ
  have hu : IsIso u := epi_unit_isIso O (.of u)
  have : IsIso α := by
    have heq : α = u ≫ τ := by simp [u]
    rw [heq]
    infer_instance
  refine ⟨asIso τ ≪≫ (asIso α).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← hα, Category.assoc, IsIso.inv_hom_id_assoc, hτ]

end CategoryTheory
