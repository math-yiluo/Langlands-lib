/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryPullComparison
import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction

/-! A decomposition of the ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(auxiliary; not a blueprint node).
The existence and insertion-normalization part is isolated so that it can be
proved independently from the uniqueness argument. -/
@[expose] public noncomputable section
universe u
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] completed derivedExtension SheafOfModules.monoidalCategory
  strictLimit ordinaryUnit quotientPresentation
attribute [local irreducible] derivedPull

-- Compose four normalization equations without unfolding any module constructions.
private theorem finiteInsertion_chain {D : Type*} [Category* D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : D}
    {u : X₀ ⟶ X₁} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {s : X₃ ⟶ X₄}
    {c : X₁ ⟶ X₄} {t : X₄ ⟶ X₅} {d : X₁ ⟶ X₆} {e : X₆ ⟶ X₅}
    {f : X₅ ⟶ X₇} {g : X₆ ⟶ X₈} {h : X₈ ⟶ X₇} {l : X₀ ⟶ X₉} {v : X₉ ⟶ X₈}
    (hs : a ≫ b ≫ s = c) (ht : c ≫ t = d ≫ e)
    (hn : e ≫ f = g ≫ h) (hd : u ≫ d ≫ g = l ≫ v) :
    u ≫ a ≫ b ≫ s ≫ t ≫ f = l ≫ v ≫ h := by
  rw [reassoc_of% hs, reassoc_of% ht, hn]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ h) hd

-- Cancel the underlying comparison before specializing to module functors.
private theorem finiteInsertion_iso_cancel {D : Type*} [Category* D]
    {X₀ X₁ X₂ X₃ X₄ : D} {u : X₀ ⟶ X₁} {f : X₁ ⟶ X₂}
    {v : X₀ ⟶ X₃} {g : X₃ ⟶ X₄} (e : X₂ ≅ X₃)
    (h : v ≫ e.inv = u ≫ f) :
    u ≫ f ≫ e.hom ≫ g = v ≫ g := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun k ↦ k ≫ e.hom ≫ g) h.symm

private theorem finiteInsertion_isIso {D : Type*} [Category* D]
    {X Y Z : D} (f : X ⟶ Y) (e : Y ≅ Z) (e' : X ≅ Z)
    (h : f ≫ e.hom = e'.hom) : IsIso f := by
  have hf : f = e'.hom ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  rw [hf]
  infer_instance

private theorem finiteInsertion_naturality {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) {M N : Mod R} (f : M ⟶ N) :
    insertion c M ≫ (underlying S).map ((change c).map f) =
      (underlying R).map f ≫ insertion c N := by
  obtain ⟨am, h⟩ : ∃ am : change c ⊣ res c,
      ∀ M : Mod R, insertion c M = (underlying R).map (am.unit.app M) :=
    ⟨scalarAdj c, insertion_eq_unit c⟩
  rw [h, h]
  have hn := congrArg ((underlying R).map) (am.unit.naturality f)
  simp only [Functor.map_comp] at hn
  exact hn.symm

private theorem finiteScalarComposite_exists {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    ∃ e : change a ⋙ change b ≅ change c,
      ∀ M : Mod R, insertion a M ≫ insertion b ((change a).obj M) ≫
        (underlying T).map (e.hom.app M) = insertion c M := by
  let am := ((scalarAdj a).comp (scalarAdj b)).ofNatIsoRight (resCompIso a b c h)
  let e := am.leftAdjointUniq (scalarAdj c)
  refine ⟨e, ?_⟩
  intro M
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app am (scalarAdj c) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  ext U m
  have he := congrArg (fun f ↦ f.val.app U m) hh
  change ((resCompIso a b c h).hom.app ((change c).obj M)).val.app U
      ((e.hom.app M).val.app U
        (tensorSection b ((change a).obj M) U 1 (tensorSection a M U 1 m))) =
    tensorSection c M U 1 m at he
  rw [resCompIso_hom_apply] at he
  change (e.hom.app M).val.app U
      ((insertion b ((change a).obj M)).hom.app U ((insertion a M).hom.app U m)) =
    (insertion c M).hom.app U m
  have ha := (insertion_existsUnique a M).exists.choose_spec
  have hb := (insertion_existsUnique b ((change a).obj M)).exists.choose_spec
  have hc := (insertion_existsUnique c M).exists.choose_spec
  change ∀ U m, (insertion a M).hom.app U m = tensorSection a M U 1 m at ha
  change ∀ U m, (insertion b ((change a).obj M)).hom.app U m =
    tensorSection b ((change a).obj M) U 1 m at hb
  change ∀ U m, (insertion c M).hom.app U m = tensorSection c M U 1 m at hc
  rw [ha, hb, hc]
  exact he

include V adj hL

-- The proof forms two successive mates under four adjunctions.
private theorem finiteInverseScalar_exists {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    ∃ e : (F.algebra R).modules ⋙ change (F.rings.map a) ≅
        change a ⋙ (F.algebra S).modules,
      ∀ M : Mod R,
        (F.algebra R).moduleUnderlying.inv.app M ≫
            insertion (F.rings.map a) ((F.algebra R).modules.obj M) ≫
            (underlying (F.rings.obj S)).map (e.hom.app M) =
          L.map (insertion a M) ≫
            (F.algebra S).moduleUnderlying.inv.app ((change a).obj M) := by
  -- Keep the adjunctions abstract so their concrete tensor constructions stay hidden.
  obtain ⟨amA, hA⟩ : ∃ am : change a ⊣ res a,
      ∀ M : Mod R, insertion a M = (underlying R).map (am.unit.app M) :=
    ⟨scalarAdj a, insertion_eq_unit a⟩
  obtain ⟨amB, hB⟩ : ∃ am : change (F.rings.map a) ⊣ res (F.rings.map a),
      ∀ M : Mod (F.rings.obj R), insertion (F.rings.map a) M =
        (underlying (F.rings.obj R)).map (am.unit.app M) :=
    ⟨scalarAdj (F.rings.map a), insertion_eq_unit (F.rings.map a)⟩
  obtain ⟨PR, eR, amR, hR⟩ := WeilConjectures.SemilinearSections.normalizedModuleAdjunction_exists
    R (F.rings.obj R) L V adj (F.algebra R)
  obtain ⟨PS, eS, amS, hS⟩ := WeilConjectures.SemilinearSections.normalizedModuleAdjunction_exists
    S (F.rings.obj S) L V adj (F.algebra S)
  -- The mate construction only uses the forward restriction comparison.
  obtain ⟨ri, hri⟩ : ∃ ri : res a ⋙ (F.algebra R).modules ⟶
      (F.algebra S).modules ⋙ res (F.rings.map a),
      ∀ N : Mod S, (underlying (F.rings.obj R)).map (ri.app N) =
        (restrictionUnderlying F a N).hom :=
    ⟨inverseRestriction F a, fun _ ↦ rfl⟩
  -- The right mate becomes an underlying-sheaf isomorphism by normalization.
  let pr : PS ⋙ res a ⟶ res (F.rings.map a) ⋙ PR :=
    (mateEquiv amS amR (TwoSquare.mk _ _ _ _ ri))
  have hpr (N : Mod (F.rings.obj S)) :
      (underlying R).map (pr.app N) ≫
          eR.hom.app ((res (F.rings.map a)).obj N) = eS.hom.app N := by
    let f := ri.app (PS.obj N) ≫
      (res (F.rings.map a)).map (amS.counit.app N)
    have hm : amR.homEquiv _ _ f = pr.app N := by
      apply (amR.homEquiv _ _).symm.injective
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact (mateEquiv_counit amS amR (TwoSquare.mk _ _ _ _ ri) N).symm
    have hf : (F.algebra R).moduleUnderlying.inv.app ((res a).obj (PS.obj N)) ≫
        (underlying (F.rings.obj R)).map f =
      (F.algebra S).moduleUnderlying.inv.app (PS.obj N) ≫
        (underlying (F.rings.obj S)).map (amS.counit.app N) := by
      dsimp only [f]
      rw [Functor.map_comp, hri]
      change (F.algebra R).moduleUnderlying.inv.app _ ≫
        ((restrictionUnderlying F a (PS.obj N)).hom ≫
          (underlying (F.rings.obj S)).map (amS.counit.app N)) = _
      simp only [restrictionUnderlying, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv, ← Category.assoc, Iso.inv_hom_id_app,
        Category.id_comp]
    have hc : amS.homEquiv (PS.obj N) N (amS.counit.app N) = 𝟙 _ := by
      apply (amS.homEquiv _ _).symm.injective
      rw [Equiv.symm_apply_apply]
      exact (Adjunction.homEquiv_symm_id amS N).symm
    exact (congrArg (fun k ↦ (underlying R).map k ≫
      eR.hom.app ((res (F.rings.map a)).obj N)) hm.symm).trans
      ((hR _ _ f).trans ((congrArg (adj.homEquiv _ _) hf).trans
        ((hS _ _ (amS.counit.app N)).symm.trans
          ((congrArg (fun k ↦ (underlying S).map k ≫ eS.hom.app N) hc).trans
            ((congrArg (fun k ↦ k ≫ eS.hom.app N) ((underlying S).map_id _)).trans
              (Category.id_comp _))))))
  have hpri (N : Mod (F.rings.obj S)) : IsIso (pr.app N) := by
    have : IsIso ((underlying R).map (pr.app N)) :=
      finiteInsertion_isIso _ (eR.app _) (eS.app N) (hpr N)
    exact isIso_of_reflects_iso _ (underlying R)
  have : ∀ N, IsIso (pr.app N) := hpri
  have := NatIso.isIso_of_isIso_app pr
  -- Iterated mates identify the desired left mate as its conjugate.
  let b : (F.algebra R).modules ⋙ change (F.rings.map a) ⟶
      change a ⋙ (F.algebra S).modules :=
    ((mateEquiv amA amB).symm
      (TwoSquare.mk _ _ _ _ ri))
  have he : conjugateEquiv (amA.comp amS)
      (amR.comp amB) b = pr := by
    let β := (mateEquiv amA amB).symm
      (TwoSquare.mk _ _ _ _ ri)
    have h := iterated_mateEquiv_conjugateEquiv
      amA amB amR amS β
    simpa only [β, b, pr, Equiv.apply_symm_apply] using h.symm
  have : IsIso (conjugateEquiv (amA.comp amS)
      (amR.comp amB) b) := by rw [he]; infer_instance
  have : IsIso b := conjugateEquiv_of_iso (amA.comp amS)
    (amR.comp amB) b
  refine ⟨asIso b, ?_⟩
  intro M
  have hu := unit_mateEquiv_symm amA amB
    (TwoSquare.mk _ _ _ _ ri) M
  change (F.algebra R).modules.map (amA.unit.app M) ≫
      ri.app ((change a).obj M) =
    amB.unit.app ((F.algebra R).modules.obj M) ≫
      (res (F.rings.map a)).map (b.app M) at hu
  have h := congrArg (fun f ↦ (F.algebra R).moduleUnderlying.inv.app M ≫
    (underlying (F.rings.obj R)).map f) hu
  simp only [Functor.map_comp] at h
  rw [hri, ← hB] at h
  change (F.algebra R).moduleUnderlying.inv.app M ≫
      (underlying (F.rings.obj R)).map
        ((F.algebra R).modules.map (amA.unit.app M)) ≫
      (F.algebra R).moduleUnderlying.hom.app
        ((res a).obj ((change a).obj M)) ≫
      (F.algebra S).moduleUnderlying.inv.app ((change a).obj M) =
    (F.algebra R).moduleUnderlying.inv.app M ≫
      insertion (F.rings.map a) ((F.algebra R).modules.obj M) ≫
      (underlying (F.rings.obj S)).map (b.app M) at h
  have hn : L.map (insertion a M) ≫
      (F.algebra R).moduleUnderlying.inv.app ((res a).obj ((change a).obj M)) =
    (F.algebra R).moduleUnderlying.inv.app M ≫
      (underlying (F.rings.obj R)).map
        ((F.algebra R).modules.map (amA.unit.app M)) := by
    exact (congrArg (fun k ↦ L.map k ≫ (F.algebra R).moduleUnderlying.inv.app
      ((res a).obj ((change a).obj M))) (hA M)).trans
        ((F.algebra R).moduleUnderlying.inv.naturality (amA.unit.app M))
  exact h.symm.trans (finiteInsertion_iso_cancel
    ((F.algebra R).moduleUnderlying.app ((res a).obj ((change a).obj M))) hn)

/-- Existence of the normalized ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(auxiliary; not a blueprint node).
The map is obtained by transporting the finite quotient tensor comparison through
inverse image; pure tensors with coefficient one give the displayed normalization. -/
theorem ordinaryFinitePull_exists
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))),
      ∀ M : Mod (constant J A),
        pullInsertion F (constantMap F A) M ≫
            insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
            (underlying (finite J' A I n)).map (e.hom.app M) =
          L.map (insertion (quotient J A I n) M) ≫
            pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
              ((change (quotient J A I n)).obj M) := by
  have hq : constantMap F A ≫ quotient J' A I n =
      F.rings.map (quotient J A I n) ≫ constantMap F (A ⧸ I ^ (n + 1)) :=
    (F.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).symm
  obtain ⟨d, hd⟩ := finiteInverseScalar_exists J (F := F) V adj (quotient J A I n)
  obtain ⟨s, hs⟩ := finiteScalarComposite_exists J' (constantMap F A) (quotient J' A I n)
    (F.rings.map (quotient J A I n) ≫ constantMap F (A ⧸ I ^ (n + 1))) hq
  obtain ⟨t, ht⟩ := finiteScalarComposite_exists J' (F.rings.map (quotient J A I n))
    (constantMap F (A ⧸ I ^ (n + 1))) _ rfl
  let e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
      change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))) :=
    Functor.isoWhiskerLeft (F.algebra (constant J A)).modules s ≪≫
      Functor.isoWhiskerLeft (F.algebra (constant J A)).modules t.symm ≪≫
      Functor.isoWhiskerRight d (change (constantMap F (A ⧸ I ^ (n + 1))))
  refine ⟨e, ?_⟩
  intro M
  let N := (F.algebra (constant J A)).modules.obj M
  let B := finite J' A I n
  have ht' :
      insertion (F.rings.map (quotient J A I n) ≫
          constantMap F (A ⧸ I ^ (n + 1))) N ≫ (underlying B).map (t.inv.app N) =
        insertion (F.rings.map (quotient J A I n)) N ≫
          insertion (constantMap F (A ⧸ I ^ (n + 1)))
            ((change (F.rings.map (quotient J A I n))).obj N) := by
    rw [← ht N]
    change (insertion (F.rings.map (quotient J A I n)) N ≫
      insertion (constantMap F (A ⧸ I ^ (n + 1)))
        ((change (F.rings.map (quotient J A I n))).obj N) ≫
      (underlying B).map (t.hom.app N)) ≫ (underlying B).map (t.inv.app N) = _
    simp only [Category.assoc, ← (underlying B).map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id]
  have hn :
      insertion (constantMap F (A ⧸ I ^ (n + 1)))
          ((change (F.rings.map (quotient J A I n))).obj N) ≫
        (underlying B).map
          ((change (constantMap F (A ⧸ I ^ (n + 1)))).map (d.hom.app M)) =
      (underlying (F.rings.obj (finite J A I n))).map (d.hom.app M) ≫
        insertion (constantMap F (A ⧸ I ^ (n + 1)))
          ((F.algebra (finite J A I n)).modules.obj ((change (quotient J A I n)).obj M)) := by
    exact finiteInsertion_naturality J' (constantMap F (A ⧸ I ^ (n + 1)))
      (d.hom.app M)
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [pullInsertion, pull, Functor.comp_obj]
  simp only [Category.assoc]
  exact finiteInsertion_chain (hs N) ht' hn (hd M)
end CategoryTheory.ConstantCompletion
