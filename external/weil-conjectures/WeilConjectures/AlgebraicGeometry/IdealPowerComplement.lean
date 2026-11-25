/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk

/-! # IdealPowerComplement

Source: Stacks Project, Properties, Lemma 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The complement of the proper-stalk locus is open, and every ideal power restricts
isomorphically to the structure sheaf there. No quasi-compactness hypothesis is needed.

Proof: On an affine open, quasi-coherence identifies the ideal inclusion with the
inclusion of an ideal J of the ring of sections. Its stalk image at a prime is J localized
at that prime, so the surjective-stalk locus is the union of D(f) for f in J. These affine
open loci agree on intersections because they express the same stalk condition, hence
form an open U. On U the original inclusion is an isomorphism: it is a monomorphism
and surjective on every stalk. Multiplication by the unit ideal has image the whole
module. Induction on the recursive idealSheafPower therefore makes each power
inclusion an isomorphism on U, including the identity at n = 0. Restricting further to
any W contained in U and taking sections gives the asserted bijection.

Source: Stacks Project, Properties, Lemma 01PQ and its reduction to Lemma 01PM.
(blueprint: lem-weil-pbc-ideal-power-complement). -/
theorem ideal_power_complement
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] :
    ∃ U : X.Opens,
      (∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) ∧
      (∀ (n : ℕ) (W : X.Opens), W ≤ U →
        Function.Bijective ((idealSheafPower ι n).2.app W)) := by
  classical
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let P : TopCat.Presheaf Ab X.toTopCat := I.presheaf
  let Q : TopCat.Presheaf Ab X.toTopCat := O.presheaf
  let f : P ⟶ Q := ι.mapPresheaf
  let U : X.Opens := ⨆ W : {W : X.Opens // ∃ b : Γ(I, W), ι.app W b = (1 : Γ(X, W))}, W.1
  have hlocal (x : X) :
      x ∈ U ↔ ∃ (W : X.Opens), x ∈ W ∧ ∃ b : Γ(I, W), ι.app W b = (1 : Γ(X, W)) := by
    simp only [U, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨⟨W, b, hb⟩, hx⟩
      exact ⟨W, hx, b, hb⟩
    · rintro ⟨W, hx, b, hb⟩
      exact ⟨⟨W, b, hb⟩, hx⟩
  have hsurj (x : X) : x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom := by
    change x ∈ U ↔ Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab x).map f)
    constructor
    · intro hx s
      obtain ⟨W, hxW, b, hb⟩ := (hlocal x).mp hx
      obtain ⟨V, hxV, s, rfl⟩ := Q.exists_germ_eq s
      have hxWV : x ∈ W ⊓ V := ⟨hxW, hxV⟩
      let b' : Γ(I, W ⊓ V) := P.map (homOfLE inf_le_left).op b
      let s' : Γ(X, W ⊓ V) := Q.map (homOfLE inf_le_right).op s
      have hb' : ι.app (W ⊓ V) b' = (1 : Γ(X, W ⊓ V)) := by
        have hh := ConcreteCategory.congr_hom
          (f.naturality (homOfLE inf_le_left : W ⊓ V ⟶ W).op) b
        change ι.app (W ⊓ V) b' = Q.map (homOfLE inf_le_left).op (ι.app W b) at hh
        rw [hh, hb]
        change X.presheaf.map (homOfLE inf_le_left).op 1 = 1
        exact map_one _
      refine ⟨P.germ (W ⊓ V) x hxWV (s' • b'), ?_⟩
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      change Q.germ (W ⊓ V) x hxWV (ι.app (W ⊓ V) (s' • b')) = _
      rw [Modules.Hom.app_smul, hb']
      change Q.germ (W ⊓ V) x hxWV (s' * (1 : Γ(X, W ⊓ V))) = _
      rw [mul_one]
      exact Q.germ_res_apply (homOfLE inf_le_right) x hxWV s
    · intro hs
      obtain ⟨b, hb⟩ := hs (Q.germ ⊤ x (by trivial) (1 : Γ(X, ⊤)))
      obtain ⟨W, hxW, b, rfl⟩ := P.exists_germ_eq b
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hb
      obtain ⟨V, hxV, iVW, iVT, he⟩ := Q.germ_eq x hxW (by trivial) _ _ hb
      apply (hlocal x).mpr
      refine ⟨V, hxV, P.map iVW.op b, ?_⟩
      have hh := ConcreteCategory.congr_hom (f.naturality iVW.op) b
      change ι.app V (P.map iVW.op b) = Q.map iVW.op (ι.app W b) at hh
      change Q.map iVW.op (ι.app W b) = Q.map iVT.op (1 : Γ(X, ⊤)) at he
      rw [hh, he]
      change X.presheaf.map iVT.op 1 = 1
      exact map_one _
  refine ⟨U, hsurj, ?_⟩
  intro n W hW
  let p := idealSheafPower ι n
  have hp : Mono p.2 := by
    dsimp [p]
    induction n using Nat.twoStepInduction with
    | zero => dsimp [idealSheafPower]; infer_instance
    | one => exact inferInstanceAs (Mono ι)
    | more n _ ih =>
      let := ih
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      change Mono (idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫
        (idealSheafPower ι (n + 1)).2)
      dsimp [idealModuleProductι]
      infer_instance
  let := hp
  have hstalk (x : X) (hx : x ∈ W) :
      Function.Bijective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map p.2).hom := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    have hinj : Function.Injective (S.map p.2).hom := by
      change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map p.2.mapPresheaf)
      apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      intro V
      have : Mono p.2.val := (SheafOfModules.forget _).map_mono p.2
      exact (ModuleCat.mono_iff_injective (p.2.val.app (op V))).mp inferInstance
    refine ⟨hinj, ?_⟩
    by_cases hn : n = 0
    · subst n
      change Function.Surjective (S.map (𝟙 O)).hom
      rw [S.map_id]
      exact Function.surjective_id
    · obtain ⟨e, he, _, _, _, _, hpowers⟩ := ideal_module_product_stalk ι O x
      let J : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map ι ≫ e.hom).hom
      have hJ : J = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        change Function.Surjective (e.hom.hom.comp (S.map ι).hom)
        exact (ModuleCat.epi_iff_surjective e.hom).mp inferInstance |>.comp
          ((hsurj x).mp (hW hx))
      have hrange : LinearMap.range (S.map p.2 ≫ e.hom).hom = ⊤ := by
        have hh := (hpowers n (Nat.one_le_iff_ne_zero.mpr hn)).1
        change LinearMap.range (S.map p.2 ≫ e.hom).hom = J ^ n at hh
        rw [hh, hJ, Ideal.top_pow]
      have hh := LinearMap.range_eq_top.mp hrange
      intro s
      obtain ⟨t, ht⟩ := hh (e.hom.hom s)
      refine ⟨t, ?_⟩
      apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
      exact ht
  let fs : (SheafOfModules.toSheaf X.ringCatSheaf).obj p.1 ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj O :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map p.2
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective fs W hstalk


end AlgebraicGeometry.Scheme
