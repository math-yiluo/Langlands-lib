/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions

/-!
# Lifting an equivariant finite étale scheme

Source: Stacks Project Tag 0A5G, final paragraph.
(blueprint: lem-weil-pbc-finite-etale-scheme-torsor-lift)
-/

@[expose] public section

universe u

open CategoryTheory Limits

open Opposite

-- The following private proof constructions are ported from the corresponding
-- proved section of EtaleTorsorDescent. That module cannot be imported here:
-- its HenselianFiniteEtale import reaches this module through the H¹ comparison.
namespace AlgebraicGeometry.Scheme.EtaleTorsor.SchemeLiftRepresentation

/-- Cancellation on sections of any sheaf isomorphism, via Mathlib's concrete iso law. -/
private lemma sectionIso_hom_inv_apply {Y : Scheme.{u}}
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} (e : A ≅ B)
    {U : Y.Etaleᵒᵖ} (x : A.obj.obj U) :
    e.inv.hom.app U (e.hom.hom.app U x) = x :=
  (((sheafSections _ _).obj U).mapIso e).hom_inv_id_apply x

/-- The reverse cancellation law on sections of any sheaf isomorphism. -/
private lemma sectionIso_inv_hom_apply {Y : Scheme.{u}}
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} (e : A ≅ B)
    {U : Y.Etaleᵒᵖ} (x : B.obj.obj U) :
    e.hom.hom.app U (e.inv.hom.app U x) = x :=
  (((sheafSections _ _).obj U).mapIso e).inv_hom_id_apply x

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

section Representable

variable [TopologicalSpace M] [DiscreteTopology M]

omit [AddCommGroup M] in
/-- A morphism into an arbitrary scheme coproduct is given on the open fibres of a
continuous index function by morphisms into the corresponding, possibly varying, summands. -/
private lemma exists_fiberOpens_comp_sigmaι {Z : Scheme.{u}} (Q : M → Scheme.{u}) (κ : Z ⟶ ∐ Q) :
    ∃ a : C(Z, M), ∀ m, ∃ k : (Z.fiberOpens a m).toScheme ⟶ Q m,
      (Z.fiberOpens a m).ι ≫ κ = k ≫ Sigma.ι Q m := by
  have hκ (x : Z) : ∃ m y, Sigma.ι Q m y = κ x := by
    obtain ⟨m, y, hy⟩ := (sigmaOpenCover Q).exists_eq (κ x)
    exact ⟨m, y, hy⟩
  let a₀ (x : Z) : M := (hκ x).choose
  have ha₀ (x : Z) (m : M) (y : Q m) (hy : Sigma.ι Q m y = κ x) : a₀ x = m := by
    obtain ⟨y', hy'⟩ := (hκ x).choose_spec
    exact congr_arg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 (hy'.trans hy.symm))
  have hfib (m : M) : a₀ ⁻¹' {m} = κ.base ⁻¹' Set.range (Sigma.ι Q m) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ha₀ x m y hy⟩
    obtain ⟨y, hy⟩ := (hκ x).choose_spec
    subst m
    exact ⟨y, hy⟩
  let a : C(Z, M) := ⟨a₀, (IsLocallyConstant.iff_isOpen_fiber.2 fun m ↦ by
    rw [hfib]
    exact (Sigma.ι Q m).isOpenEmbedding.isOpenMap.isOpen_range.preimage
      κ.base.hom.continuous).continuous⟩
  refine ⟨a, fun m ↦ ?_⟩
  have hrange : Set.range ((Z.fiberOpens a m).ι ≫ κ).base ⊆
      Set.range (Sigma.ι Q m).base := by
    rintro _ ⟨v, rfl⟩
    have hv : v.1 ∈ a₀ ⁻¹' {m} := v.2
    rw [hfib] at hv
    obtain ⟨y, hy⟩ := hv
    exact ⟨y, hy.trans (by rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply])⟩
  exact ⟨IsOpenImmersion.lift _ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

variable (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}} (π : Q ⟶ Y)
  [Etale π] (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))

/-- The action of a locally constant function on the `Y`-morphisms into `Q`, transported from
the torsor `R` along `e`. -/
private noncomputable def reprAct {U : Y.Etale} (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    U ⟶ Etale.mk π :=
  (e.hom.hom.app (op U) (R.vadd (op U) f (e.inv.hom.app (op U) ⟨φ⟩))).down

omit [Finite M] in
private lemma comp_reprAct {M : Type (u + 1)} [AddCommGroup M]
    {Y : Scheme.{u}} [TopologicalSpace M] [DiscreteTopology M]
    (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}}
    (π : Q ⟶ Y) [Etale π]
    (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))
    {U V : Y.Etale} (h : V ⟶ U) (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    h ≫ reprAct R π e f φ = reprAct R π e (f.comp h.left.base.hom) (h ≫ φ) := by
  have hnat : e.inv.hom.app (op V) ⟨h ≫ φ⟩ =
      R.sheaf.obj.map h.op (e.inv.hom.app (op U) ⟨φ⟩) :=
    e.inv.hom.naturality_apply h.op ⟨φ⟩
  rw [reprAct, reprAct, hnat]
  have h₁ := R.map_vadd h.op f (e.inv.hom.app (op U) ⟨φ⟩)
  change _ = R.vadd (op V) (f.comp h.left.base.hom) _ at h₁
  rw [← h₁]
  have hnat' : e.hom.hom.app (op V) (R.sheaf.obj.map h.op
      (R.vadd (op U) f (e.inv.hom.app (op U) ⟨φ⟩))) =
      ⟨h ≫ (e.hom.hom.app (op U)
        (R.vadd (op U) f (e.inv.hom.app (op U) ⟨φ⟩))).down⟩ :=
    e.hom.hom.naturality_apply h.op _
  rw [hnat']

/-- The action of the element `m` on `Q`. -/
private noncomputable def reprVadd (m : M) : Q ⟶ Q :=
  (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π))).left

omit [Finite M] in
private lemma reprAct_const {M : Type (u + 1)} [AddCommGroup M]
    {Y : Scheme.{u}} [TopologicalSpace M] [DiscreteTopology M]
    (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}}
    (π : Q ⟶ Y) [Etale π]
    (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))
    {U : Y.Etale} (m : M) (φ : U ⟶ Etale.mk π) :
    reprAct R π e (ContinuousMap.const _ m) φ =
      φ ≫ reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π)) := by
  rw [comp_reprAct, Category.comp_id]
  rfl

omit [Finite M] in
private lemma reprAct_left {M : Type (u + 1)} [AddCommGroup M]
    {Y : Scheme.{u}} [TopologicalSpace M] [DiscreteTopology M]
    (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}}
    (π : Q ⟶ Y) [Etale π]
    (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))
    {U : Y.Etale} (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    (reprAct R π e f φ).left =
      U.left.glueOfContinuousMap f fun m ↦ φ.left ≫ reprVadd R π e m := by
  refine U.left.hom_ext_fiberOpens f fun m ↦ ?_
  rw [Scheme.fiberOpens_ι_glueOfContinuousMap]
  let W : Y.Etale := Etale.mk ((U.left.fiberOpens f m).ι ≫ U.hom)
  let ι : W ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens f m).ι rfl
  have hf : f.comp ι.left.base.hom = ContinuousMap.const _ m :=
    ContinuousMap.ext fun x ↦ x.2
  have h := congr_arg (fun χ : W ⟶ Etale.mk π ↦ χ.left) (comp_reprAct R π e ι f φ)
  rw [hf, reprAct_const] at h
  exact h

omit [Finite M] in
private lemma reprVadd_π (m : M) : reprVadd R π e m ≫ π = π :=
  MorphismProperty.Over.w (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π)))

omit [Finite M] in
private lemma reprVadd_zero : reprVadd R π e 0 = 𝟙 Q := by
  have h₀ : (ContinuousMap.const (Etale.mk π).left (0 : M)) = 0 := rfl
  have h : reprAct R π e (ContinuousMap.const _ 0) (𝟙 (Etale.mk π)) = 𝟙 _ := by
    rw [reprAct, h₀]
    erw [R.zero_vadd]
    rw [sectionIso_inv_hom_apply]
  exact congr_arg (fun χ : Etale.mk π ⟶ Etale.mk π ↦ χ.left) h

/-- The comparison map `∐_{m ∈ M} Q ⟶ Q ×_Y Q`, `(m, q) ↦ (m • q, q)`. -/
private noncomputable abbrev reprSigmaDesc : (∐ fun _ : M ↦ Q) ⟶ pullback π π :=
  Sigma.desc fun m ↦ pullback.lift (reprVadd R π e m) (𝟙 Q) (by simp [reprVadd_π])

omit [Finite M] in
/-- The action of `M` on `Q` is free on every nonempty étale `Y`-scheme. -/
private lemma eq_of_reprVadd {M : Type (u + 1)} [AddCommGroup M]
    {Y : Scheme.{u}} [TopologicalSpace M] [DiscreteTopology M]
    (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}}
    (π : Q ⟶ Y) [Etale π]
    (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))
    {V : Y.Etale} (κ : V ⟶ Etale.mk π) {m m' : M}
    (h : κ.left ≫ reprVadd R π e m = κ.left ≫ reprVadd R π e m') (v : V.left) : m = m' := by
  have h₁ : reprAct R π e (ContinuousMap.const _ m) κ =
      reprAct R π e (ContinuousMap.const _ m') κ := by
    refine etaleHom_ext ?_
    rw [reprAct_const R π e m κ, reprAct_const R π e m' κ]
    exact h
  have h₂ : e.hom.hom.app (op V) (R.vadd (op V) (ContinuousMap.const _ m)
        (e.inv.hom.app (op V) ⟨κ⟩)) =
      e.hom.hom.app (op V) (R.vadd (op V) (ContinuousMap.const _ m')
        (e.inv.hom.app (op V) ⟨κ⟩)) :=
    ULift.ext h₁
  have h₂' := congr_arg (fun z ↦ e.inv.hom.app (op V) z) h₂
  simp only [sectionIso_hom_inv_apply] at h₂'
  have h₃ := (R.bijective_vadd (op V) (e.inv.hom.app (op V) ⟨κ⟩)).1 h₂'
  exact congr_arg (fun f : C(V.left, M) ↦ f v) h₃

omit [Finite M] in
include R e in
private lemma surjective_of_representable : Surjective π := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨V, g, ⟨x⟩, v, hv⟩ :=
    (mem_smallEtaleTopology_iff _).1 (R.nonemptySieve_mem (Etale.mk (𝟙 Y))) y
  let φ := (e.hom.hom.app (op V) x).down
  refine ⟨φ.left v, ?_⟩
  have h₁ : φ.left ≫ π = V.hom := MorphismProperty.Over.w φ
  have h₂ : g.left ≫ 𝟙 Y = V.hom := MorphismProperty.Over.w g
  rw [← hv]
  refine (Scheme.Hom.comp_apply φ.left π v).symm.trans ?_
  rw [h₁, ← h₂]
  erw [Category.comp_id]
  rfl

private theorem isIso_reprSigmaDesc : IsIso (reprSigmaDesc R π e) := by
  have : Etale (Sigma.desc fun _ : M ↦ π) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let E₁ : Y.Etale := Etale.mk (Sigma.desc fun _ : M ↦ π)
  let E₂ : Y.Etale := Etale.mk (pullback.fst π π ≫ π)
  let D : E₁ ⟶ E₂ := MorphismProperty.Over.homMk (reprSigmaDesc R π e)
    (Sigma.hom_ext _ _ fun m ↦ by simp [reprSigmaDesc, reprVadd_π, E₂, E₁])
  have hD : IsIso D := by
    refine isIso_of_yoneda_map_bijective D fun T ↦ ⟨fun x x' hxx ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨a, ha⟩ := exists_fiberOpens_comp_sigmaι (fun _ : M ↦ Q) x.left
      obtain ⟨a', ha'⟩ := exists_fiberOpens_comp_sigmaι (fun _ : M ↦ Q) x'.left
      refine etaleHom_ext (T.left.hom_ext_fiberOpens (a.prodMk a') fun ⟨m, m'⟩ ↦ ?_)
      let V := T.left.fiberOpens (a.prodMk a') (m, m')
      have h₁ : V ≤ T.left.fiberOpens a m := fun y hy ↦ (Prod.ext_iff.1 hy).1
      have h₂ : V ≤ T.left.fiberOpens a' m' := fun y hy ↦ (Prod.ext_iff.1 hy).2
      obtain ⟨k, hk⟩ := ha m
      obtain ⟨k', hk'⟩ := ha' m'
      have e₁ : V.ι ≫ x.left = (T.left.homOfLE h₁ ≫ k) ≫ Sigma.ι (fun _ : M ↦ Q) m := by
        rw [← T.left.homOfLE_ι h₁, Category.assoc, hk, Category.assoc]
      have e₂ : V.ι ≫ x'.left = (T.left.homOfLE h₂ ≫ k') ≫ Sigma.ι (fun _ : M ↦ Q) m' := by
        rw [← T.left.homOfLE_ι h₂, Category.assoc, hk', Category.assoc]
      have hxD : V.ι ≫ x.left ≫ reprSigmaDesc R π e = V.ι ≫ x'.left ≫ reprSigmaDesc R π e :=
        congr_arg (fun χ : T ⟶ E₂ ↦ V.ι ≫ χ.left) hxx
      simp only [← Category.assoc] at hxD
      rw [e₁, e₂] at hxD
      simp only [Category.assoc, Sigma.ι_comp_desc] at hxD
      have hsnd := congr_arg (· ≫ pullback.snd π π) hxD
      have hfst := congr_arg (· ≫ pullback.fst π π) hxD
      simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.comp_id]
        at hsnd hfst
      by_cases hV : IsEmpty V.toScheme
      · exact isInitialOfIsEmpty.hom_ext _ _
      · obtain ⟨v⟩ := not_isEmpty_iff.1 hV
        have hκ : (T.left.homOfLE h₁ ≫ k) ≫ π = V.ι ≫ T.hom := by
          have := congr_arg (· ≫ Sigma.desc fun _ : M ↦ π) e₁
          simp only [Category.assoc, Sigma.ι_comp_desc] at this
          rw [Category.assoc, ← this]
          exact congr_arg _ (MorphismProperty.Over.w x)
        let W : Y.Etale := Etale.mk (V.ι ≫ T.hom)
        let κ : W ⟶ Etale.mk π := MorphismProperty.Over.homMk (T.left.homOfLE h₁ ≫ k) hκ
        have hmm : m = m' := eq_of_reprVadd R π e κ (by
          change (T.left.homOfLE h₁ ≫ k) ≫ reprVadd R π e m =
            (T.left.homOfLE h₁ ≫ k) ≫ reprVadd R π e m'
          rw [Category.assoc, Category.assoc, hfst, ← Category.assoc, ← hsnd,
            Category.assoc]) v
        subst hmm
        rw [e₁, e₂, hsnd]
    · let φe : T ⟶ Etale.mk π := MorphismProperty.Over.homMk (g.left ≫ pullback.fst π π) (by
        rw [Category.assoc]
        exact MorphismProperty.Over.w g)
      let ψe : T ⟶ Etale.mk π := MorphismProperty.Over.homMk (g.left ≫ pullback.snd π π) (by
        change g.left ≫ pullback.snd π π ≫ π = T.hom
        rw [← pullback.condition, ← Category.assoc]
        exact MorphismProperty.Over.w g)
      obtain ⟨f, hf⟩ := (R.bijective_vadd (op T) (e.inv.hom.app (op T) ⟨ψe⟩)).2
        (e.inv.hom.app (op T) ⟨φe⟩)
      have hact : reprAct R π e f ψe = φe := by
        have := congr_arg (fun z ↦ (e.hom.hom.app (op T) z).down) hf
        simp only [sectionIso_inv_hom_apply] at this
        exact this
      have hglue := reprAct_left R π e f ψe
      rw [hact] at hglue
      refine ⟨MorphismProperty.Over.homMk
        (T.left.glueOfContinuousMap f fun m ↦ ψe.left ≫ Sigma.ι (fun _ : M ↦ Q) m) ?_,
        etaleHom_ext ?_⟩
      · change T.left.glueOfContinuousMap f _ ≫ Sigma.desc (fun _ : M ↦ π) = T.hom
        rw [Scheme.glueOfContinuousMap_comp]
        refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
        rw [Category.assoc, Sigma.ι_comp_desc]
        exact congr_arg _ (MorphismProperty.Over.w ψe)
      · change T.left.glueOfContinuousMap f _ ≫ reprSigmaDesc R π e = g.left
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, Scheme.glueOfContinuousMap_comp]
          change _ = φe.left
          rw [hglue]
          congr 1
          funext m
          simp [reprSigmaDesc]
        · rw [Category.assoc, Scheme.glueOfContinuousMap_comp]
          change _ = ψe.left
          refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
          simp only [reprSigmaDesc, Category.assoc, Sigma.ι_comp_desc_assoc, pullback.lift_snd]
          erw [Category.comp_id]
  exact (Etale.forget Y ⋙ Over.forget Y).map_isIso D

variable [IsFinite π]

/-- **The `M`-torsor of a representable torsor.** A torsor `R` under the sheaf of locally constant
`M`-valued functions whose underlying sheaf is represented by a finite étale `Q ⟶ Y`, through
`e`, makes `Q` an `M`-torsor: `m` acts on `Q` as the constant section `m` acts on the identity
section of `Q`. -/
private noncomputable def ofRepresentable : EtaleTorsor M Y where
  P := Q
  π := π
  surjective := surjective_of_representable R π e
  vadd := reprVadd R π e
  vadd_π := reprVadd_π R π e
  zero_vadd := reprVadd_zero R π e
  add_vadd m n := by
    have h₀ : (ContinuousMap.const (Etale.mk π).left (m + n)) =
        ContinuousMap.const _ n + ContinuousMap.const _ m :=
      ContinuousMap.ext fun _ ↦ add_comm m n
    have h : reprAct R π e (ContinuousMap.const _ (m + n)) (𝟙 (Etale.mk π)) =
        reprAct R π e (ContinuousMap.const _ n)
          (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π))) := by
      rw [reprAct, h₀]
      erw [R.add_vadd]
      rw [reprAct, reprAct]
      simp only [ULift.up_down, sectionIso_hom_inv_apply]
    rw [reprAct_const R π e n] at h
    exact congr_arg (fun χ : Etale.mk π ⟶ Etale.mk π ↦ χ.left) h
  isIso_sigmaDesc := isIso_reprSigmaDesc R π e

end Representable

/-- **Torsors with a representable underlying sheaf.** A torsor `P` under the constant sheaf `M`
on the small étale site of `Y` whose underlying sheaf of sets is represented by a finite étale
`Y`-scheme `Q` is the sheaf torsor of an `M`-torsor, with total space `Q`.
(blueprint: `thm-galois-lc-etale`, simply transitive actions) -/
private theorem exists_toSheafTorsor_equiv_of_iso
    (P : Sheaf.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M))) {Q : Scheme.{u}} (π : Q ⟶ Y) [IsFinite π] [Etale π]
    (e : P.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)) :
    ∃ t : EtaleTorsor M Y, t.toSheafTorsor ≈ P ∧ t.P = Q := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let i := Etale.constantSheafIsoContinuousMapSheaf Y M
  let R := Sheaf.Torsor.ofIso i P
  refine ⟨ofRepresentable R π e,
    Setoid.trans ?_ (Sheaf.Torsor.ofIso_symm_ofIso_equiv i P), rfl⟩
  exact (Sheaf.Torsor.ofIso_equiv_ofIso_iff i.symm).2
    (by
      refine ⟨⟨e.symm, fun U f x ↦ ?_⟩⟩
      obtain ⟨φ⟩ := x
      have hφ : (ofRepresentable R π e).smulHom f φ = reprAct R π e f φ :=
        etaleHom_ext ((smulHom_left _ f φ).trans (reprAct_left R π e f φ).symm)
      change e.inv.hom.app U ⟨(ofRepresentable R π e).smulHom f φ⟩ =
        R.vadd U f (e.inv.hom.app U ⟨φ⟩)
      rw [hφ, reprAct]
      simp only [ULift.up_down]
      change e.inv.hom.app U (e.hom.hom.app U
        (R.vadd U f (e.inv.hom.app U ⟨φ⟩))) = _
      exact sectionIso_hom_inv_apply e _)

/-! ### Torsors under a finite constant sheaf are finite locally constant -/

section FiniteLocallyConstant

omit [Finite M] in
/-- A torsor under any constant group sheaf is constant over an étale scheme on which
it has a section: translation identifies the restricted underlying sheaves. -/
private theorem isConstant_over_of_section
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    [G.IsConstant Y.smallEtaleTopology]
    (P : Sheaf.Torsor G) (U : Y.Etale) (x : P.sheaf.obj.obj (op U)) :
    (P.sheaf.over U).IsConstant (Y.smallEtaleTopology.over U) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  let G' := (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  have : G'.IsConstant Y.smallEtaleTopology := inferInstance
  have hG' := Sheaf.isConstant_over (W := U) G'
  let e : (G'.over U).obj ≅ (P.sheaf.over U).obj :=
    NatIso.ofComponents (fun W ↦ Equiv.toIso (Equiv.ofBijective
      (fun a : G.obj.obj (op W.unop.left) ↦
        P.vadd (op W.unop.left) a (P.sheaf.obj.map W.unop.hom.op x))
      (P.bijective_vadd _ _))) (fun {W W'} h ↦ by
        ext a
        change P.vadd _ (G.obj.map h.unop.left.op a) (P.sheaf.obj.map W'.unop.hom.op x) =
          P.sheaf.obj.map h.unop.left.op (P.vadd _ a (P.sheaf.obj.map W.unop.hom.op x))
        rw [P.map_vadd, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          Over.w h.unop])
  exact Sheaf.isConstant_congr _
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso (X := G'.over U) (Y := P.sheaf.over U) e)

variable [TopologicalSpace M] [DiscreteTopology M]

omit [Finite M] in
/-- For any discrete group `M`, its elements surject onto the stalk of an `M`-torsor:
a fixed local section generates every germ by a constant translate. -/
private theorem exists_surjective_sheafFiber (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M))
    {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ∃ f : M → ToType ((pointSmallEtale s).sheafFiber.obj R.sheaf),
      Function.Surjective f := by
  let Φ := pointSmallEtale s
  have hT : IsTerminal (Etale.mk (𝟙 Y)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y
  let t₀ : Φ.fiber.obj (Etale.mk (𝟙 Y)) := (Φ.uniqueFiberObj _ hT).default
  obtain ⟨V₀, g₀, ⟨x₀⟩, v₀, -⟩ :=
    Φ.jointly_surjective _ (R.nonemptySieve_mem (Etale.mk (𝟙 Y))) t₀
  let φ : M → ToType (Φ.sheafFiber.obj R.sheaf) := fun m ↦
    Φ.toPresheafFiber V₀ v₀ R.sheaf.obj (R.vadd (op V₀) (ContinuousMap.const _ m) x₀)
  refine ⟨φ, fun p ↦ ?_⟩
  obtain ⟨V, v, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := R.sheaf.obj) p
  let E₁ : Φ.fiber.Elements := Φ.fiber.elementsMk V v
  let E₂ : Φ.fiber.Elements := Φ.fiber.elementsMk V₀ v₀
  let Wel := IsCofiltered.min E₁ E₂
  let f₁ := IsCofiltered.minToLeft E₁ E₂
  let f₂ := IsCofiltered.minToRight E₁ E₂
  let W : Y.Etale := Wel.1
  let w : Φ.fiber.obj W := Wel.2
  obtain ⟨a₀, ha⟩ := (R.bijective_vadd (op W) (R.sheaf.obj.map f₂.1.op x₀)).2
    (R.sheaf.obj.map f₁.1.op z)
  let a : C(W.left, M) := a₀
  let m : M := a (w.left (IsLocalRing.closedPoint Ω))
  let U := W.left.fiberOpens a m
  have hU : Set.range w.left ⊆ (U : Set W.left) := by
    rintro _ ⟨ξ, rfl⟩
    change a (w.left ξ) = m
    rw [Subsingleton.elim (α := PrimeSpectrum Ω) ξ (IsLocalRing.closedPoint Ω)]
  obtain ⟨w', hw'⟩ := exists_pointSmallEtale_fiber_ofOpens s w U hU
  let ιU := Etale.ofOpensι W U
  have hmap (F : Y.Etaleᵒᵖ ⥤ Type (u + 1)) {A B : Y.Etale} (f : B ⟶ W) (g : W ⟶ A)
      (y : F.obj (op A)) : F.map (f ≫ g).op y = F.map f.op (F.map g.op y) := by
    rw [op_comp, F.map_comp]
    rfl
  have hz : R.sheaf.obj.map (ιU ≫ f₁.1).op z =
      R.sheaf.obj.map (ιU ≫ f₂.1).op (R.vadd (op V₀) (ContinuousMap.const _ m) x₀) := by
    rw [hmap, hmap, ← ha, R.map_vadd, R.map_vadd, R.map_vadd]
    congr 1
    exact ContinuousMap.ext fun ξ ↦ ξ.2
  have h₁ : Φ.fiber.map (ιU ≫ f₁.1) w' = v := by
    rw [Functor.map_comp_apply, hw']
    exact f₁.2
  have h₂ : Φ.fiber.map (ιU ≫ f₂.1) w' = v₀ := by
    rw [Functor.map_comp_apply, hw']
    exact f₂.2
  have e₁ := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w (ιU ≫ f₁.1) w' R.sheaf.obj) z
  have e₂ := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w (ιU ≫ f₂.1) w' R.sheaf.obj)
    (R.vadd (op V₀) (ContinuousMap.const _ m) x₀)
  rw [ConcreteCategory.comp_apply, h₁] at e₁
  rw [ConcreteCategory.comp_apply, h₂] at e₂
  refine ⟨m, ?_⟩
  change Φ.toPresheafFiber V₀ v₀ R.sheaf.obj _ = Φ.toPresheafFiber V v R.sheaf.obj z
  rw [← e₁, ← e₂, hz]

omit [TopologicalSpace M] [DiscreteTopology M] in
/-- **Torsors under a finite constant sheaf are finite locally constant sheaves of sets.** -/
private theorem isFiniteLocallyConstantSheafOfTypes_sheaf
    (P : Sheaf.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M))) :
    (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y, ∀ i,
      (P.sheaf.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧
      Scheme.IsFiniteSheaf P.sheaf := by
  refine ⟨?_, ?_⟩
  · choose V g hg hy using
      (mem_smallEtaleTopology_iff _).1 (P.nonemptySieve_mem (Etale.mk (𝟙 Y)))
    let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y :=
      Scheme.Cover.mkOfCovers Y (fun y ↦ (V y).left) (fun y ↦ (V y).hom) (fun y ↦ by
        obtain ⟨z, hz⟩ := hy y
        refine ⟨y, z, ?_⟩
        have h₂ : (g y).left ≫ 𝟙 Y = (V y).hom := MorphismProperty.Over.w (g y)
        calc (V y).hom z = ((g y).left ≫ 𝟙 Y) z := by rw [h₂]; rfl
          _ = (g y).left z := by erw [Category.comp_id]; rfl
          _ = y := hz) (fun y ↦ (V y).prop)
    have : ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)).IsConstant Y.smallEtaleTopology :=
      Sheaf.isConstant_of_iso _ (Iso.refl _)
    exact ⟨𝒰, fun y ↦ isConstant_over_of_section P (V y) (hg y).some⟩
  · let _ : TopologicalSpace M := ⊥
    have : DiscreteTopology M := ⟨rfl⟩
    refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).2 ?_⟩
    obtain ⟨f, hf⟩ := exists_surjective_sheafFiber
      (Sheaf.Torsor.ofIso (Etale.constantSheafIsoContinuousMapSheaf Y M) P) s
    exact Finite.of_surjective f hf

end FiniteLocallyConstant


private theorem exists_scheme_representative
    (R : Sheaf.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M))) :
    ∃ t : EtaleTorsor M Y, t.toSheafTorsor ≈ R := by
  obtain ⟨hloc, hfin⟩ := isFiniteLocallyConstantSheafOfTypes_sheaf R
  obtain ⟨P, π, hπfin, hπet, ⟨e⟩⟩ :=
    finiteLocallyConstant_sets_representable Y R.sheaf hloc hfin
  have := hπfin
  have := hπet
  obtain ⟨t, ht, _⟩ := exists_toSheafTorsor_equiv_of_iso R π
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso e)
  exact ⟨t, ht⟩

end AlgebraicGeometry.Scheme.EtaleTorsor.SchemeLiftRepresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale

private theorem surjective_of_finiteEtale_pullback_equivalence
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ P : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (π : P ⟶ Y) [IsFinite π] [Etale π] [Surjective (pullback.snd π i)] :
    Surjective π := by
  let U : Y.Opens := ⟨Set.range π, π.isOpenMap.isOpen_range⟩
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isOpenImmersion U.ι
    (by simpa [Scheme.Opens.range_ι, U] using π.isClosedMap.isClosed_range)
  have hbc : Surjective (pullback.snd U.ι i) := by
    constructor
    apply Set.range_eq_univ.mp
    rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    change i ⁻¹' Set.range π = Set.univ
    rw [← Scheme.Pullback.range_snd]
    exact Set.range_eq_univ.mpr (pullback.snd π i).surjective
  have : IsIso (pullback.snd U.ι i) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hbc⟩
  let F : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y ⥤
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i
  let : F.IsEquivalence := hFE
  let A : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ U.ι ⟨inferInstance, inferInstance⟩
  let B : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (𝟙 Y) ⟨inferInstance, inferInstance⟩
  let j : A ⟶ B := MorphismProperty.Over.homMk U.ι (Category.comp_id _)
  have hj : (F.map j).left ≫ pullback.snd (𝟙 Y) i = pullback.snd U.ι i := by
    exact MorphismProperty.Over.w (F.map j)
  have : IsIso (F.map j).left := IsIso.of_isIso_fac_right hj
  have : IsIso (F.map j) := by
    let e := MorphismProperty.Over.isoMk (asIso (F.map j).left)
      (MorphismProperty.Over.w (F.map j))
    change IsIso e.hom
    infer_instance
  have : IsIso j := isIso_of_reflects_iso j F
  have : IsIso U.ι :=
    (MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y).map_isIso j
  constructor
  apply Set.range_eq_univ.mp
  change (U : Set Y) = Set.univ
  rw [← Scheme.Opens.range_ι]
  exact Set.range_eq_univ.mpr U.ι.surjective

private noncomputable def finiteEtale_cofan_isColimit
    {Y P : Scheme.{u}} (π : P ⟶ Y) [IsFinite π] [Etale π]
    (M : Type (u + 1)) [Finite M] :
    let X : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
      MorphismProperty.Over.mk ⊤ π ⟨inferInstance, inferInstance⟩
    let : Etale (Sigma.desc fun _ : M ↦ π) :=
      IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
    let D : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
      MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : M ↦ π)
        ⟨inferInstance, inferInstance⟩
    IsColimit (Cofan.mk D fun m : M ↦
      MorphismProperty.Over.homMk (A := X) (B := D) (Sigma.ι (fun _ : M ↦ P) m)
        (by simp [D, X])) := by
  intro X hD D
  refine Cofan.IsColimit.mk _ (fun s ↦ ?_) ?_ ?_
  · refine MorphismProperty.Over.homMk (A := D) (B := s.pt) (Sigma.desc fun m ↦ (s.inj m).left) ?_
    change Sigma.desc _ ≫ s.pt.hom = Sigma.desc _
    apply Sigma.hom_ext
    intro m
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact MorphismProperty.Over.w (s.inj m)
  · intro s m
    apply MorphismProperty.Over.Hom.ext
    exact Sigma.ι_comp_desc _ _
  · intro s f hf
    apply MorphismProperty.Over.Hom.ext
    apply Sigma.hom_ext
    intro m
    have h := congr_arg (fun g ↦ g.left) (hf m)
    change Sigma.ι (fun _ : M ↦ P) m ≫ f.left =
      Sigma.ι (fun _ : M ↦ P) m ≫ Sigma.desc (fun m ↦ (s.inj m).left)
    rw [Sigma.ι_comp_desc]
    exact h

private noncomputable def finiteEtale_binaryFan_isLimit
    {Y P : Scheme.{u}} (π : P ⟶ Y) [IsFinite π] [Etale π] :
    let X : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
      MorphismProperty.Over.mk ⊤ π ⟨inferInstance, inferInstance⟩
    let T : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
      MorphismProperty.Over.mk ⊤ (pullback.fst π π ≫ π)
        ⟨inferInstance, inferInstance⟩
    IsLimit (BinaryFan.mk
      (MorphismProperty.Over.homMk (A := T) (B := X) (pullback.fst π π) rfl)
      (MorphismProperty.Over.homMk (A := T) (B := X) (pullback.snd π π)
        (pullback.condition.symm))) := by
  intro X T
  refine BinaryFan.IsLimit.mk _ (fun {S} f g ↦ ?_) ?_ ?_ ?_
  · refine MorphismProperty.Over.homMk (A := S) (B := T)
      (pullback.lift f.left g.left ?_) ?_
    · exact (MorphismProperty.Over.w f).trans
        (MorphismProperty.Over.w g).symm
    · change pullback.lift _ _ _ ≫ pullback.fst π π ≫ π = S.hom
      simp only [pullback.lift_fst_assoc]
      exact MorphismProperty.Over.w f
  · intro S f g
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  · intro S f g
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  · intro S f g m hfst hsnd
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (congr_arg (fun g ↦ g.left) hfst).trans (pullback.lift_fst (f := π) (g := π) _ _ _).symm
    · exact (congr_arg (fun g ↦ g.left) hsnd).trans (pullback.lift_snd (f := π) (g := π) _ _ _).symm

private theorem isIso_sigmaDesc_of_equivariant_iso
    {Y P : Scheme.{u}} (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (π : P ⟶ Y) (a : M → (P ⟶ P)) (haπ : ∀ m, a m ≫ π = π)
    (t₀ : Scheme.EtaleTorsor M Y) (e : P ≅ t₀.P)
    (he : e.hom ≫ t₀.π = π)
    (hact : ∀ m, a m ≫ e.hom = e.hom ≫ t₀.vadd m) :
    IsIso (Sigma.desc fun m : M ↦
      pullback.lift (f := π) (g := π) (a m) (𝟙 P) (by simp [haπ])) := by
  let c := pullback.map π π t₀.π t₀.π e.hom e.hom (𝟙 Y)
    (by simpa using he.symm) (by simpa using he.symm)
  let d := Sigma.desc fun m : M ↦
    pullback.lift (f := π) (g := π) (a m) (𝟙 P) (by simp [haπ])
  let d₀ := Sigma.desc fun m : M ↦
    pullback.lift (f := t₀.π) (g := t₀.π) (t₀.vadd m) (𝟙 t₀.P)
      (by simp [t₀.vadd_π])
  have : IsIso d₀ := t₀.isIso_sigmaDesc
  have h : d ≫ c = (Sigma.mapIso fun _ : M ↦ e).hom ≫ d₀ := by
    apply Sigma.hom_ext
    intro m
    apply pullback.hom_ext
    · simp [d, c, d₀, hact, Category.assoc]
    · dsimp only [d, c, d₀]
      simp only [Category.assoc, pullback.lift_snd,
        Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc_assoc, pullback.lift_snd_assoc,
        Category.id_comp, Category.comp_id]
  exact IsIso.of_isIso_fac_right h

/-- An equivariant finite étale scheme whose base change is a torsor is surjective
and has an invertible simple-transitivity morphism.

Source: Stacks Project Tag 0A5G, final paragraph.
(blueprint: lem-weil-pbc-finite-etale-scheme-torsor-lift)

Proof: Finite coproducts and fibre products of finite étale schemes are finite étale.
Base change identifies the morphism from the copies of P to P ×_Y P with the
simple-transitivity morphism downstairs, using the comparison e on both factors and
each coproduct summand. It is therefore invertible downstairs. The fully faithful
base-change functor reflects isomorphisms, proving invertibility upstairs.
The image U of π is open because π is étale, and closed because π is finite.
With its open subscheme structure its inclusion j into Y is finite étale. Factor π
through U. After base change, surjectivity of the torsor downstairs says that the
open immersion j has full image; thus its base change is an isomorphism. Reflect
this isomorphism in the finite étale category to show that j is an isomorphism.
Since U was the image of π, π is surjective. This uses no point of either base:
when Y₀ is empty the equivalence still reflects the isomorphism of j, and the
trivial group is included. No action equations are needed for these two properties. -/
private theorem finiteEtale_torsor_conditions_reflect
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ P : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (π : P ⟶ Y) [IsFinite π] [Etale π]
    (a : M → (P ⟶ P)) (haπ : ∀ m, a m ≫ π = π)
    (t₀ : Scheme.EtaleTorsor M Y₀) (e : pullback π i ≅ t₀.P)
    (he : e.hom ≫ t₀.π = pullback.snd π i)
    (hact : ∀ m : M,
      pullback.map π i π i (a m) (𝟙 Y₀) (𝟙 Y)
        (by rw [Category.comp_id, haπ])
        (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom =
      e.hom ≫ t₀.vadd m) :
    Surjective π ∧ IsIso (Sigma.desc
      fun m : M ↦ pullback.lift (f := π) (g := π) (a m) (𝟙 P)
        (by simp [haπ])) := by
  have : Surjective t₀.π := t₀.surjective
  have : Surjective (pullback.snd π i) := by rw [← he]; infer_instance
  refine ⟨surjective_of_finiteEtale_pullback_equivalence i hFE π, ?_⟩
  classical
  let F : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y ⥤
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i
  let : F.IsEquivalence := hFE
  let X : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ π ⟨inferInstance, inferInstance⟩
  have : Etale (Sigma.desc fun _ : M ↦ π) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let D : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : M ↦ π)
      ⟨inferInstance, inferInstance⟩
  let T : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (pullback.fst π π ≫ π)
      ⟨inferInstance, inferInstance⟩
  let u (m : M) : X ⟶ D :=
    MorphismProperty.Over.homMk (Sigma.ι (fun _ : M ↦ P) m) (by simp [D, X])
  let p₁ : T ⟶ X := MorphismProperty.Over.homMk (pullback.fst π π) rfl
  let p₂ : T ⟶ X := MorphismProperty.Over.homMk (pullback.snd π π)
    pullback.condition.symm
  let α (m : M) : X ⟶ X := MorphismProperty.Over.homMk (a m) (haπ m)
  let h : D ⟶ T := MorphismProperty.Over.homMk
    (Sigma.desc fun m : M ↦ pullback.lift (f := π) (g := π) (a m) (𝟙 P)
      (by simp [haπ])) (by apply Sigma.hom_ext; intro m; simp [T, D, haπ])
  have hc : IsColimit (Cofan.mk D u) := finiteEtale_cofan_isColimit π M
  have ht : IsLimit (BinaryFan.mk p₁ p₂) := finiteEtale_binaryFan_isLimit π
  have : PreservesColimit (Discrete.functor fun _ : M ↦ X) F :=
    (Adjunction.isEquivalence_preservesColimits F).preservesColimitsOfShape.preservesColimit
  have hcF : IsColimit (Cofan.mk (F.obj D) fun m ↦ F.map (u m)) :=
    isColimitCofanMkObjOfIsColimit F (fun _ : M ↦ X) u hc
  have htF : IsLimit (BinaryFan.mk (F.map p₁) (F.map p₂)) :=
    mapIsLimitOfPreservesOfIsLimit F _ _ ht
  let πb := pullback.snd π i
  have : Etale (Sigma.desc fun _ : M ↦ πb) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let Db : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : M ↦ πb)
      ⟨inferInstance, inferInstance⟩
  let Tb : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.mk ⊤ (pullback.fst πb πb ≫ πb)
      ⟨inferInstance, inferInstance⟩
  let ub (m : M) : F.obj X ⟶ Db :=
    MorphismProperty.Over.homMk (Sigma.ι (fun _ : M ↦ pullback π i) m)
      (by exact Sigma.ι_comp_desc (fun _ : M ↦ πb) m)
  let pb₁ : Tb ⟶ F.obj X := MorphismProperty.Over.homMk (pullback.fst πb πb) rfl
  let pb₂ : Tb ⟶ F.obj X := MorphismProperty.Over.homMk (pullback.snd πb πb)
    pullback.condition.symm
  have hcb : IsColimit (Cofan.mk Db ub) := finiteEtale_cofan_isColimit πb M
  have htb : IsLimit (BinaryFan.mk pb₁ pb₂) := finiteEtale_binaryFan_isLimit πb
  let dI := hcF.coconePointUniqueUpToIso hcb
  let tI := htF.conePointUniqueUpToIso htb
  have hbπ (m : M) : (F.map (α m)).left ≫ πb = πb :=
    MorphismProperty.Over.w (F.map (α m))
  let hb : Db ⟶ Tb := MorphismProperty.Over.homMk
    (Sigma.desc fun m : M ↦ pullback.lift (f := πb) (g := πb)
      (F.map (α m)).left (𝟙 (pullback π i)) (by simp [hbπ]))
    (by apply Sigma.hom_ext; intro m; simp [Tb, Db, hbπ])
  have hbact (m : M) : (F.map (α m)).left ≫ e.hom = e.hom ≫ t₀.vadd m := by
    dsimp only [F, α, X, MorphismProperty.Over.mk]
    simpa [pullback.map] using hact m
  have : IsIso hb.left := isIso_sigmaDesc_of_equivariant_iso
    M πb (fun m ↦ (F.map (α m)).left) hbπ t₀ e he hbact
  have : IsIso hb := by
    let e' := MorphismProperty.Over.isoMk (asIso hb.left) (MorphismProperty.Over.w hb)
    change IsIso e'.hom
    infer_instance
  have hu₁ (m : M) : u m ≫ h ≫ p₁ = α m := by
    apply MorphismProperty.Over.Hom.ext
    simp [u, h, p₁, α]
  have hu₂ (m : M) : u m ≫ h ≫ p₂ = 𝟙 X := by
    apply MorphismProperty.Over.Hom.ext
    simp [u, h, p₂]
    rfl
  have hub₁ (m : M) : ub m ≫ hb ≫ pb₁ = F.map (α m) := by
    apply MorphismProperty.Over.Hom.ext
    simp [ub, hb, pb₁]
  have hub₂ (m : M) : ub m ≫ hb ≫ pb₂ = 𝟙 (F.obj X) := by
    apply MorphismProperty.Over.Hom.ext
    simp [ub, hb, pb₂]
    rfl
  have huI (m : M) : F.map (u m) ≫ dI.hom = ub m :=
    hcF.comp_coconePointUniqueUpToIso_hom hcb ⟨m⟩
  have hpI₁ : tI.hom ≫ pb₁ = F.map p₁ :=
    htF.conePointUniqueUpToIso_hom_comp htb ⟨.left⟩
  have hpI₂ : tI.hom ≫ pb₂ = F.map p₂ :=
    htF.conePointUniqueUpToIso_hom_comp htb ⟨.right⟩
  have hh : dI.hom ≫ hb = F.map h ≫ tI.hom := by
    apply Cofan.IsColimit.hom_ext hcF
    intro m
    apply BinaryFan.IsLimit.hom_ext htb
    · calc
        (F.map (u m) ≫ (dI.hom ≫ hb)) ≫ pb₁ =
            (F.map (u m) ≫ dI.hom) ≫ hb ≫ pb₁ := by simp only [Category.assoc]
        _ = ub m ≫ hb ≫ pb₁ := by rw [huI]
        _ = F.map (α m) := hub₁ m
        _ = F.map (u m ≫ h ≫ p₁) := (congr_arg F.map (hu₁ m)).symm
        _ = (F.map (u m) ≫ (F.map h ≫ tI.hom)) ≫ pb₁ := by
          rw [Functor.map_comp, Functor.map_comp]
          simp only [Category.assoc, hpI₁]
    · calc
        (F.map (u m) ≫ (dI.hom ≫ hb)) ≫ pb₂ =
            (F.map (u m) ≫ dI.hom) ≫ hb ≫ pb₂ := by simp only [Category.assoc]
        _ = ub m ≫ hb ≫ pb₂ := by rw [huI]
        _ = 𝟙 (F.obj X) := hub₂ m
        _ = F.map (u m ≫ h ≫ p₂) := by rw [hu₂, F.map_id]
        _ = (F.map (u m) ≫ (F.map h ≫ tI.hom)) ≫ pb₂ := by
          rw [Functor.map_comp, Functor.map_comp]
          simp only [Category.assoc, hpI₂]
  have : IsIso (F.map h ≫ tI.hom) := by rw [← hh]; infer_instance
  have : IsIso (F.map h) := IsIso.of_isIso_comp_right _ tI.hom
  have : IsIso h := isIso_of_reflects_iso h F
  exact (MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y).map_isIso h


/-- A finite étale base-change equivalence lifts a scheme torsor together with its action.
Source: Stacks Project Tag 0A5G, final paragraph, categorical action-lifting argument.
(blueprint: lem-weil-pbc-finite-etale-scheme-torsor-lift)

Proof: A torsor R₀ under the finite constant group is locally the finite constant set M.
Tag 03RV represents its underlying sheaf by a finite étale scheme. Yoneda lifts each
constant action map; its faithfulness gives the action equations. Simple transitivity
on sections and local existence make the representative a scheme torsor t₀, with a
sheaf torsor isomorphism to R₀. This is the argument of
EtaleTorsorDescent.exists_toSheafTorsor_equiv, applied through lower representability
interfaces rather than importing that module, which now creates an import cycle.
Essential surjectivity lifts the finite étale scheme underlying t₀ to P over Y.
Fullness lifts each action endomorphism, conjugated by the chosen base-change isomorphism.
Faithfulness gives the zero and addition equations. Finite coproducts and fibre products
of finite étale schemes are finite étale and are preserved by base change. Thus the map
from the coproduct of the copies of P, indexed by M, to P ×_Y P becomes the torsor
isomorphism for t₀. Reflection of isomorphisms makes it an isomorphism upstairs.
The image of P → Y is open because P → Y is étale and closed because it is finite.
Its open-and-closed immersion U → Y is finite étale, and its pullback is an isomorphism:
t₀ is surjective, so its base-changed image is all Y₀. Reflecting this isomorphism
shows U = Y and hence P → Y is surjective. These data define the lifted scheme torsor.
The chosen isomorphism commutes with the structure maps and every lifted action.
No geometric point is selected, so empty bases and the trivial group are included. -/
theorem finiteEtale_lifts_scheme_torsor
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (R₀ : Sheaf.Torsor
      ((constantSheaf Y₀.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M))) :
    ∃ (t₀ : Scheme.EtaleTorsor M Y₀) (_ : t₀.toSheafTorsor ≈ R₀)
      (t : Scheme.EtaleTorsor M Y) (e : pullback t.π i ≅ t₀.P),
      e.hom ≫ t₀.π = pullback.snd t.π i ∧
      ∀ m : M,
        pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
          (by rw [Category.comp_id, t.vadd_π])
          (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom =
        e.hom ≫ t₀.vadd m := by
  classical
  obtain ⟨t₀, hrepr⟩ :=
    Scheme.EtaleTorsor.SchemeLiftRepresentation.exists_scheme_representative R₀
  let F : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y ⥤
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i
  let : F.IsEquivalence := hFE
  let X₀ : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀ :=
    MorphismProperty.Over.mk ⊤ t₀.π ⟨t₀.isFinite, t₀.etale⟩
  let X : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    F.objPreimage X₀
  let eX := F.objObjPreimageIso X₀
  let e : pullback X.hom i ≅ t₀.P :=
    (MorphismProperty.Over.forget _ ⊤ Y₀ ⋙ Over.forget Y₀).mapIso eX
  have he : e.hom ≫ t₀.π = pullback.snd X.hom i :=
    MorphismProperty.Over.w eX.hom
  let a₀ (m : M) : X₀ ⟶ X₀ :=
    MorphismProperty.Over.homMk (t₀.vadd m) (t₀.vadd_π m)
  let a (m : M) : X ⟶ X := F.preimage (eX.hom ≫ a₀ m ≫ eX.inv)
  have hamap (m : M) : F.map (a m) = eX.hom ≫ a₀ m ≫ eX.inv :=
    F.map_preimage _
  have haπ (m : M) : (a m).left ≫ X.hom = X.hom :=
    MorphismProperty.Over.w (a m)
  have ha0 : a 0 = 𝟙 X := by
    apply F.map_injective
    rw [hamap, F.map_id]
    have hzero : a₀ 0 = 𝟙 X₀ := by
      apply MorphismProperty.Over.Hom.ext
      exact t₀.zero_vadd
    simp [hzero, X]
  have haadd (m n : M) : a (m + n) = a m ≫ a n := by
    apply F.map_injective
    rw [Functor.map_comp, hamap, hamap, hamap]
    have hadd : a₀ (m + n) = a₀ m ≫ a₀ n := by
      apply MorphismProperty.Over.Hom.ext
      exact t₀.add_vadd m n
    simp [hadd, Category.assoc]
  have hact (m : M) :
      pullback.map X.hom i X.hom i (a m).left (𝟙 Y₀) (𝟙 Y)
        (by exact (Category.comp_id X.hom).trans (haπ m).symm)
        (by exact (Category.comp_id i).trans (Category.id_comp i).symm) ≫ e.hom =
      e.hom ≫ t₀.vadd m := by
    have h : F.map (a m) ≫ eX.hom = eX.hom ≫ a₀ m := by
      rw [hamap]
      simp [Category.assoc]
    have hl := congr_arg (fun g ↦ g.left) h
    dsimp [F, a₀, e] at hl ⊢
    simpa [pullback.map] using hl
  have : IsFinite X.hom := X.prop.1
  have : Etale X.hom := X.prop.2
  obtain ⟨hsurj, hiso⟩ :=
    finiteEtale_torsor_conditions_reflect i hFE M X.hom
      (fun m ↦ (a m).left) haπ t₀ e he hact
  let t : Scheme.EtaleTorsor M Y :=
    { P := X.left
      π := X.hom
      surjective := hsurj
      vadd := fun m ↦ (a m).left
      vadd_π := haπ
      zero_vadd := congr_arg (fun g ↦ g.left) ha0
      add_vadd := fun m n ↦ congr_arg (fun g ↦ g.left) (haadd m n)
      isIso_sigmaDesc := hiso }
  exact ⟨t₀, hrepr, t, e, he, hact⟩

end AlgebraicGeometry.Etale
