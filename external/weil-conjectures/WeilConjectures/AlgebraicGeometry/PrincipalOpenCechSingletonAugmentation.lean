/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # PrincipalOpenCechSingletonAugmentation

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-singleton-augmentation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem augmentation_transport_d
    {A : Type u} [CommRing A]
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U W : (Spec (.of A)).Opens) (hWU : W ≤ U)
    (a b c d : ℤ) (e : a = c) (e' : b = d) :
    (modulesSpecToSheaf.map (eqToHom (congrArg I.X e))).hom.app (op U) ≫
        (modulesSpecToSheaf.obj (I.X c)).obj.map (homOfLE hWU).op ≫
        (modulesSpecToSheaf.map (I.d c d)).hom.app (op W) =
      (modulesSpecToSheaf.map (I.d a b)).hom.app (op U) ≫
        (modulesSpecToSheaf.map (eqToHom (congrArg I.X e'))).hom.app (op U) ≫
        (modulesSpecToSheaf.obj (I.X d)).obj.map (homOfLE hWU).op := by
  subst c d
  change (𝟙 _ ≫ _) = (_ ≫ 𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact (modulesSpecToSheaf.map (I.d a b)).hom.naturality (homOfLE hWU).op

private theorem augmentation_transport_restrict
    {A : Type u} [CommRing A]
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U W Z : (Spec (.of A)).Opens) (hWU : W ≤ U) (hZW : Z ≤ W)
    (a b c : ℤ) (e : a = b) (e' : b = c) :
    (modulesSpecToSheaf.map (eqToHom (congrArg I.X e))).hom.app (op U) ≫
        (modulesSpecToSheaf.obj (I.X b)).obj.map (homOfLE hWU).op ≫
        (modulesSpecToSheaf.map (eqToHom (congrArg I.X e'))).hom.app (op W) ≫
        (modulesSpecToSheaf.obj (I.X c)).obj.map (homOfLE hZW).op =
      (modulesSpecToSheaf.map (eqToHom (congrArg I.X (e.trans e')))).hom.app (op U) ≫
        (modulesSpecToSheaf.obj (I.X c)).obj.map (homOfLE (hZW.trans hWU)).op := by
  subst b c
  change (𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _) = (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact ((modulesSpecToSheaf.obj (I.X a)).obj.map_comp
    (homOfLE hWU).op (homOfLE hZW).op).symm

-- The pair calculation contains dependent transports of the section modules.
/-- A separate construction step for the finite subset Čech argument.
Source: Stacks Project, Cohomology, Tag 08C1, equation (20.40.0.1).
(blueprint: lem-sc-principal-open-cech-singleton-augmentation).

Proof: Define the degree-n linear map by σ₁ followed by restriction and degree transport
on singleton coordinates, and zero on larger coordinates. On singleton coordinates
the chain equation is the supplied section differential equation, naturality of
restriction, and equality induction for the transports. On two-element subsets the
two restrictions from singleton rows are the same composite restriction with
opposite signs, hence cancel. On larger subsets all incoming singleton coordinates
are zero. These coordinate equations give the consecutive chain equations;
CochainComplex.ofHom, or the analogous general-complex hom constructor, gives α₁.
The argument includes empty covers, empty intersections and repeated opens. -/
theorem principalOpenCech_singleton_augmentation_exists
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ))
      (K₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ₁ : ∀ n : ℤ, K₁.X n ≅ (modulesSpecToSheaf.obj (I.X n)).obj.obj (op V))
      (T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val)))),
      (∀ (n : ℤ) (s : T₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ (n + 1)).hom (T₁.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (I.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ₁ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ₁ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K₁.X n),
        (σ₁ (n + 1)).hom (K₁.d n (n + 1) s) =
          (modulesSpecToSheaf.map (I.d n (n + 1))).hom.app (op V) ((σ₁ n).hom s)) →
      ∃ α₁ : K₁ ⟶ T₁,
      (∀ (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ n).hom (α₁.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
              (op V) ((σ₁ n).hom s)) else 0) := by
  classical
  intro V D hle hls he hes K₁ σ₁ T₁ τ₁ hT₁ hK
  let a (n : ℤ) : K₁.X n ⟶ T₁.X n :=
    ModuleCat.ofHom
      { toFun := fun s ↦ (τ₁ n).inv (fun S ↦ if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
              (op V) ((σ₁ n).hom s)) else 0)
        map_add' := fun s t ↦ by
          rw [← map_add]
          congr 1
          funext S
          dsimp only [Pi.add_apply]
          split <;> simp only [map_add, add_zero]
        map_smul' := fun a s ↦ by
          rw [← map_smul]
          congr 1
          funext S
          dsimp only [Pi.smul_apply]
          split <;> simp only [map_smul, RingHom.id_apply, smul_zero] }
  have ha (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}) :
      (τ₁ n).hom (a n s) S = if h : S.val.card = 1 then
        (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
          (homOfLE (hls S h)).op
          ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
            (op V) ((σ₁ n).hom s)) else 0 := by
    change ((τ₁ n).hom ((τ₁ n).inv _)) S = _
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
    rfl
  have ha_one (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty})
      (h : S.val.card = 1) :
      (τ₁ n).hom (a n s) S =
        (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
          (homOfLE (hls S h)).op
          ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
            (op V) ((σ₁ n).hom s)) := by rw [ha, dite_eq_left h]
  have ha_large (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty})
      (h : 1 < S.val.card) : (τ₁ n).hom (a n s) S = 0 := by
    rw [ha, dite_eq_right (ne_of_gt h)]
  have hcomm (n : ℤ) : a n ≫ T₁.d n (n + 1) = K₁.d n (n + 1) ≫ a (n + 1) := by
    apply (cancel_mono (τ₁ (n + 1)).hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext S
    change (τ₁ (n + 1)).hom (T₁.d n (n + 1) (a n s)) S =
      (τ₁ (n + 1)).hom (a (n + 1) (K₁.d n (n + 1) s)) S
    rw [hT₁]
    by_cases h1 : S.val.card = 1
    · rw [ha_one _ _ _ h1, ha_one _ _ _ h1, hK]
      have hz : (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
          (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
            (modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
              (homOfLE (hle S.val j.val)).op
              ((modulesSpecToSheaf.map
                (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                  (op (D (S.val.erase j.val))) ((τ₁ n).hom (a n s)
                    ⟨S.val.erase j.val, h⟩)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        split
        next h =>
          have hc := Finset.card_erase_add_one j.property
          have hp := h.card_pos
          omega
        next => rfl
      have hp : S.val.card - 1 = 0 := by omega
      rw [hz, add_zero, hp, pow_zero, one_smul]
      exact ConcreteCategory.congr_hom
        (augmentation_transport_d I V (D S.val) (hls S h1) n (n + 1) _ _
          (hes S h1 n) (hes S h1 (n + 1))) ((σ₁ n).hom s)
    · have hlarge : 1 < S.val.card := by
        have := S.property.card_pos
        omega
      rw [ha_large _ _ _ hlarge, ha_large _ _ _ hlarge]
      simp only [map_zero, smul_zero, zero_add]
      by_cases h2 : S.val.card = 2
      · obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.mp h2
        have hs : ∃ x y : Fin r, x < y ∧ S.val = {x, y} := by
          rcases lt_or_gt_of_ne hxy with hlt | hgt
          · exact ⟨x, y, hlt, hS⟩
          · exact ⟨y, x, hgt, hS.trans (Finset.pair_comm x y)⟩
        obtain ⟨x, y, hxy, hS⟩ := hs
        rcases S with ⟨S, hne⟩
        dsimp at hS
        subst S
        let x' : ({x, y} : Finset (Fin r)) := ⟨x, by simp⟩
        let y' : ({x, y} : Finset (Fin r)) := ⟨y, by simp⟩
        have hu : (Finset.univ : Finset ({x, y} : Finset (Fin r))) = {x', y'} := by
          ext z
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
          rcases Finset.mem_insert.mp z.property with hz | hz
          · exact Or.inl (Subtype.ext hz)
          · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hz))
        rw [hu, Finset.sum_pair (show x' ≠ y' from fun h ↦ hxy.ne
          (congrArg Subtype.val h))]
        dsimp only [x', y']
        have hex : ({x, y} : Finset (Fin r)).erase x = {y} := by simp [hxy.ne]
        have hey : ({x, y} : Finset (Fin r)).erase y = {x} := by
          rw [Finset.pair_comm]
          simp [hxy.ne']
        have hnx : (({x, y} : Finset (Fin r)).erase x).Nonempty := by simp [hex]
        have hny : (({x, y} : Finset (Fin r)).erase y).Nonempty := by simp [hey]
        have hcx : (({x, y} : Finset (Fin r)).erase x).card = 1 := by simp [hex]
        have hcy : (({x, y} : Finset (Fin r)).erase y).card = 1 := by simp [hey]
        rw [dite_eq_left hnx, dite_eq_left hny, ha_one _ _ _ hcx, ha_one _ _ _ hcy]
        have hx := ConcreteCategory.congr_hom
          (augmentation_transport_restrict I V _ _ (hls ⟨_, hnx⟩ hcx) (hle {x, y} x) n _ _
            (hes ⟨_, hnx⟩ hcx n) (he {x, y} x (by simp) n)) ((σ₁ n).hom s)
        have hy := ConcreteCategory.congr_hom
          (augmentation_transport_restrict I V _ _ (hls ⟨_, hny⟩ hcy) (hle {x, y} y) n _ _
            (hes ⟨_, hny⟩ hcy n) (he {x, y} y (by simp) n)) ((σ₁ n).hom s)
        simp only [ModuleCat.comp_apply] at hx hy
        rw [hx, hy]
        have ht : n = n + 1 + 1 - (({x, y} : Finset (Fin r)).card : ℤ) := by
          rw [show ({x, y} : Finset (Fin r)).card = 2 from h2]
          omega
        have hpa : (({x, y} : Finset (Fin r)).filter (fun z ↦ z < x)).card = 0 := by
          simp [Finset.filter_insert, Finset.filter_singleton, hxy.not_gt]
        have hpb : (({x, y} : Finset (Fin r)).filter (fun z ↦ z < y)).card = 1 := by
          simp [Finset.filter_insert, Finset.filter_singleton, hxy]
        rw [hpa, hpb, pow_zero, one_smul, pow_one, neg_one_smul]
        exact add_neg_cancel _
      · apply Finset.sum_eq_zero
        intro j _
        split
        next h =>
          have hj : 1 < (S.val.erase j.val).card := by
            have := Finset.card_erase_add_one j.property
            omega
          rw [ha_large _ _ _ hj]
          simp only [map_zero, smul_zero]
        next => rfl
  exact ⟨CochainComplex.ofHom a hcomm, ha⟩


end AlgebraicGeometry
