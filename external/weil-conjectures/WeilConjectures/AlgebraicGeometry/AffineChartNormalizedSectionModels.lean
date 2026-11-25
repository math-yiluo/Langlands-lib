/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
import WeilConjectures.AlgebraicGeometry.AffineChartSectionRingPresentations
import WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent
import WeilConjectures.AlgebraicGeometry.AffineIsomorphicSourceNormalizedModels

/-! # Normalized section models for affine upper-tail charts

Source: Stacks Project, Tags 01ZR and 01I6.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Scheme.Modules

private lemma affine_model_qc_pushforward_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let A := (pushforward f).obj M
  let e : A ≅ M.restrict (inv f) :=
    (restrictFunctorId.app A).symm ≪≫
      (restrictFunctorCongr (IsIso.inv_hom_id f)).symm.app A ≪≫
      (restrictFunctorComp (inv f) f).app A ≪≫
      (restrictFunctor (inv f)).mapIso ((restrictFunctorAdjCounitIso f).app M)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm inferInstance

/-- Morphisms out of a quasi-coherent module on an affine scheme are determined by their effect
on global sections. -/
private lemma affine_model_hom_ext
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent]
    {α β : M ⟶ N} (h : ∀ m : Γ(M, ⊤), α.app ⊤ m = β.app ⊤ m) :
    α = β := by
  have := affine_model_qc_pushforward_iso X.toSpecΓ M
  apply (pushforward X.toSpecΓ).map_injective
  exact hom_ext_of_isQuasicoherent_Spec h

/-- A `Γ(X, ⊤)`-linear map between the global sections of quasi-coherent modules on an affine
scheme comes from a morphism of modules. -/
private lemma affine_model_hom_exists
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (χ : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have := affine_model_qc_pushforward_iso X.toSpecΓ M
  have := affine_model_qc_pushforward_iso X.toSpecΓ N
  obtain ⟨φ', hφ'⟩ := exists_hom_app_top_eq' (M := (pushforward X.toSpecΓ).obj M)
    (N := (pushforward X.toSpecΓ).obj N) χ.toAddMonoidHom fun a m ↦ by
      have key (P : X.Modules) (x : Γ((pushforward X.toSpecΓ).obj P, ⊤)) :
          ((ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec Γ(X, ⊤)).presheaf.map
            (homOfLE (le_top : (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op).hom a • x =
            (a • (show Γ(P, ⊤) from x) : Γ(P, ⊤)) := by
        have h1 := congr(Hom.app
          $(pushforward_map_smulHom X.toSpecΓ P ((ΓSpecIso Γ(X, ⊤)).inv a)) ⊤ x)
        rw [pushforward_map_app, smulHom_app_apply] at h1
        refine h1.symm.trans ?_
        erw [smulHom_app_apply]
        have h2 : X.toSpecΓ.appTop ((ΓSpecIso Γ(X, ⊤)).inv a) = a := by
          rw [← CommRingCat.comp_apply, toSpecΓ_appTop, Iso.inv_hom_id]
          rfl
        rw [h2, show (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op = 𝟙 _
          from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
        rfl
      exact (congrArg χ (key M m)).trans ((χ.map_smul a m).trans (key N (χ m)).symm)
  refine ⟨(pushforward X.toSpecΓ).preimage φ', fun m ↦ ?_⟩
  have := congr(Hom.app $((pushforward X.toSpecΓ).map_preimage φ') ⊤ m)
  exact this.trans (hφ' m)


end Scheme.Modules

/-- Conjugating section coordinates transports the affine Hom equivalence. -/
private theorem affine_hom_of_section_coordinates
    {X : Scheme.{u}} [IsAffine X] {S : CommRingCat.{u}}
    (ρ : S ≃+* Γ(X, ⊤)) (P Q : ModuleCat.{u} S)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (eM : P ≃+ Γ(M, ⊤)) (eN : Q ≃+ Γ(N, ⊤))
    (hM : ∀ b z, eM (b • z) = ρ b • eM z)
    (hN : ∀ b z, eN (b • z) = ρ b • eN z) :
    ∃ α : (P ⟶ Q) ≃ (M ⟶ N),
      ∀ f z, (α f).app ⊤ (eM z) = eN (f z) := by
  classical
  have hMs (b : S) (z : Γ(M, ⊤)) :
      eM.symm (ρ b • z) = b • eM.symm z := by
    apply eM.injective
    rw [eM.apply_symm_apply, hM, eM.apply_symm_apply]
  let ψ : (M ⟶ N) → (P ⟶ Q) := fun f ↦ ModuleCat.ofHom
    { toFun := fun z ↦ eN.symm (f.app ⊤ (eM z))
      map_add' := by intro z w; simp only [map_add]
      map_smul' := by
        intro b z
        apply eN.injective
        rw [eN.apply_symm_apply, hN, eN.apply_symm_apply, hM,
          Scheme.Modules.Hom.app_smul]
        rfl }
  have hψ : Function.Bijective ψ := by
    constructor
    · intro f g hfg
      apply Scheme.Modules.affine_model_hom_ext
      intro z
      obtain ⟨w, rfl⟩ := eM.surjective z
      have h := congrArg (fun k : P ⟶ Q ↦ eN (k w)) hfg
      change eN (eN.symm (f.app ⊤ (eM w))) =
        eN (eN.symm (g.app ⊤ (eM w))) at h
      simpa only [eN.apply_symm_apply] using h
    · intro f
      let χ : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
        { toFun := fun z ↦ eN (f (eM.symm z))
          map_add' := by intro z w; simp only [map_add]
          map_smul' := by
            intro b z
            obtain ⟨a, rfl⟩ := ρ.surjective b
            rw [hMs, map_smul, hN]
            rfl }
      obtain ⟨g, hg⟩ := Scheme.Modules.affine_model_hom_exists χ
      refine ⟨g, ?_⟩
      ext z
      change eN.symm (g.app ⊤ (eM z)) = f z
      rw [hg]
      change eN.symm (eN (f (eM.symm (eM z)))) = f z
      simp only [eM.symm_apply_apply, eN.symm_apply_apply]
  let E := Equiv.ofBijective ψ hψ
  refine ⟨E.symm, ?_⟩
  intro f z
  have h := congrArg (fun k : P ⟶ Q ↦ eN (k z)) (E.apply_symm_apply f)
  change eN (eN.symm ((E.symm f).app ⊤ (eM z))) = eN (f z) at h
  simpa only [eN.apply_symm_apply] using h

/-- Object reconstruction and full faithfulness in normalized section coordinates.
Source: Stacks Project, Tag 01ZR (affine proof), and Tag 01I6.
(blueprint: lem-pc-affine-chart-normalized-section-models).

Proof: The representative of the starting class is equivalent to j in the
preorder, so its spectrum map is an isomorphism. The second projection of its
pullback chart to U(a) is therefore an isomorphism. Its inverse pullback unit on
global sections gives the additive equivalences δM and δN. The upper-tail chart
cone is limiting by upperTailChartCone_isLimit. Reindex it along the equivalence
from the antisymmetrization to the tail. All charts, including its vertex, are
affine by affine base change. Affine spectrum/global-sections duality turns this
limiting cone into a colimit of F. Identify its vertex with the direct chart by
pullback pasting. This gives ρ₀; stage pullback pasting gives ρₓ. Their equation on
the iterated chart follows from the colimit cocone equation after applying global
sections and comparing the two projections of each pasting isomorphism. Apply
quasi-coherent affine reconstruction at the starting chart, then the affine
pullback/scalar-extension identification at every stage and at the vertex.
Transport through these ring and chart isomorphisms to get e₀M,e₀N,eₓM,eₓN.
The identification is linear along ρ₀ or ρₓ, giving the four scalar equations.
The tensor-to-pullback identification sends 1 ⊗ m to the pullback unit applied to
m, giving all four normalizations with the same δM,δN. Finally the affine
quasi-coherent equivalence is fully faithful: conjugating its Hom equivalence by
these object identifications yields α and β, with the displayed coordinate
formulas. No compatibility of α and β with scalar extension of morphisms is
asserted here. This construction also covers zero modules, zero rings and empty
charts, and uses no finite-presentation assumption. -/
theorem affine_chart_normalized_section_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    (M N : (U.X a).Modules)
    (hMq : M.IsQuasicoherent)
    (hNq : N.IsQuasicoherent)
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let B : (U.X a).Modules → ModuleCat.{u} (F.obj t) := fun L ↦ by
      let k := rep.obj t
      let r := Spec.map (R.map (homOfLE k.property))
      change ModuleCat.{u} Γ(pullback r g, ⊤)
      exact ModuleCat.of _ Γ((Scheme.Modules.pullback (pullback.snd r g)).obj L, ⊤)
    let P : ModuleCat.{u} (F.obj t) := B M
    let Q : ModuleCat.{u} (F.obj t) := B N
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    ∃ (δM : (P : Type u) ≃ Γ(M, ⊤)) (δN : (Q : Type u) ≃ Γ(N, ⊤))
      (ρ₀ : ↑(colimit F) →+* Γ((U.pullback₁ q₀).X a, ⊤))
      (e₀M : (ModuleCat.extendScalars r₀).obj P ≃+
        Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M, ⊤))
      (e₀N : (ModuleCat.extendScalars r₀).obj Q ≃+
        Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N, ⊤))
      (α : ((ModuleCat.extendScalars r₀).obj P ⟶
          (ModuleCat.extendScalars r₀).obj Q) ≃
        ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N)),
      (∀ b z, e₀M (b • z) = ρ₀ b • e₀M z) ∧
      (∀ b z, e₀N (b • z) = ρ₀ b • e₀N z) ∧
      (∀ m, e₀M ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
        pullbackΓ (U.pullbackHom q₀ a) M (δM m)) ∧
      (∀ m, e₀N ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
        pullbackΓ (U.pullbackHom q₀ a) N (δN m)) ∧
      (∀ s z, (α s).app ⊤ (e₀M z) = e₀N (s z)) ∧
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        let Uk : (pullback f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := U.pullback₁ q
        let V : (pullback f (c.π.app (op i))).OpenCover.{u} := Uk.pullback₁ p
        let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
          (Uk.pullbackHom p a ≫ U.pullbackHom q a)
          (by
            dsimp only [V]
            rw [Category.assoc, U.pullbackHom_map,
              ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
        ∃ (ρₓ : ↑(F.obj x) →+* Γ((U.pullback₁ q).X a, ⊤))
          (eₓM : (ModuleCat.extendScalars r).obj P ≃+
            Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M, ⊤))
          (eₓN : (ModuleCat.extendScalars r).obj Q ≃+
            Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj N, ⊤))
          (β : ((ModuleCat.extendScalars r).obj P ⟶
              (ModuleCat.extendScalars r).obj Q) ≃
            ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
              (Scheme.Modules.pullback (U.pullbackHom q a)).obj N)),
          (∀ b z, eₓM (b • z) = ρₓ b • eₓM z) ∧
          (∀ b z, eₓN (b • z) = ρₓ b • eₓN z) ∧
          (∀ m, eₓM ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m) =
            pullbackΓ (U.pullbackHom q a) M (δM m)) ∧
          (∀ m, eₓN ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m) =
            pullbackΓ (U.pullbackHom q a) N (δN m)) ∧
          (∀ s z, (β s).app ⊤ (eₓM z) = eₓN (s z)) ∧
          IsAffine (Uk.X a) ∧
          (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) := by
  classical
  intro rep g F t B P Q r₀ q₀
  let kₜ := rep.obj t
  let s := pullback.snd (Spec.map (R.map (homOfLE kₜ.property))) g
  have geometry := affine_chart_section_ring_presentations R c hc i f j hij U a ha
  have : IsIso s := geometry.1
  have : IsAffine (U.X a) := ha
  have : M.IsQuasicoherent := hMq
  have : N.IsQuasicoherent := hNq
  let ρ₀ := geometry.2.2.choose
  have hρ₀ := geometry.2.2.choose_spec
  have models := affine_isomorphic_source_normalized_models s M N hMq hNq
  let δM := models.choose
  let δN := models.choose_spec.choose
  have H := models.choose_spec.choose_spec
  have model₀ := H _ geometry.2.1 (U.pullbackHom q₀ a) (colimit F) r₀ ρ₀ hρ₀.1
  let e₀M := model₀.choose
  let e₀N := model₀.choose_spec.choose
  have h₀ := model₀.choose_spec.choose_spec
  have : IsAffine ((U.pullback₁ q₀).X a) := geometry.2.1
  have hom₀ := affine_hom_of_section_coordinates ρ₀ _ _ _ _ e₀M e₀N h₀.1 h₀.2.1
  let α := hom₀.choose
  refine ⟨δM, δN, ρ₀.toRingHom, e₀M, e₀N, α,
    h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2, hom₀.choose_spec, ?_⟩
  intro x htx
  have stage := hρ₀.2 x htx
  let ρₓ := stage.choose
  have hρₓ := stage.choose_spec
  let hjk := (rep.obj x).property
  let q := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  let r := (F.map (homOfLE htx)).hom
  have modelₓ := H _ hρₓ.2.1 (U.pullbackHom q a) (F.obj x) r ρₓ hρₓ.1
  let eₓM := modelₓ.choose
  let eₓN := modelₓ.choose_spec.choose
  have hₓ := modelₓ.choose_spec.choose_spec
  have : IsAffine ((U.pullback₁ q).X a) := hρₓ.2.1
  have homₓ := affine_hom_of_section_coordinates ρₓ _ _ _ _ eₓM eₓN hₓ.1 hₓ.2.1
  let β := homₓ.choose
  exact ⟨ρₓ.toRingHom, eₓM, eₓN, β,
    hₓ.1, hₓ.2.1, hₓ.2.2.1, hₓ.2.2.2, homₓ.choose_spec, hρₓ.2.1, hρₓ.2.2⟩

end AlgebraicGeometry
