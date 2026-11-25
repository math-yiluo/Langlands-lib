/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # PrincipalOpenCechCoefficientMap

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-coefficient-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem coordinateMap_transport
    {A : Type u} [CommRing A]
    {J I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ}
    (g : J ⟶ I) (m k : ℤ) (e : m = k) (U : (Spec (.of A)).Opens) :
    (modulesSpecToSheaf.map (g.f m)).hom.app (op U) ≫
        (modulesSpecToSheaf.map (eqToHom (congrArg I.X e))).hom.app (op U) =
      (modulesSpecToSheaf.map (eqToHom (congrArg J.X e))).hom.app (op U) ≫
        (modulesSpecToSheaf.map (g.f k)).hom.app (op U) := by
  subst k
  simp only [eqToHom_refl]
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

/-- A separate construction step for the finite subset Čech argument.
Source: Stacks Project, Cohomology, Tag 08C1, equation (20.40.0.1).
(blueprint: lem-sc-principal-open-cech-coefficient-map).

Proof: Define the degree-n linear map by τ, coordinatewise section evaluation of
 g in degree n+1-card(S), and τ₁ inverse. To prove the chain equation, transport
it to coordinates using τ₁. Substitute both supplied signed differential formulas.
The vertical terms agree by the chain equation for g. In each horizontal summand,
naturality of modulesSpecToSheaf.map (g.f _) commutes with restriction. Equality
induction on the supplied degree equality commutes g with the degree transport.
Linearity distributes g across the finite sum and scalar signs. Thus the consecutive
chain equations hold, and the homological-complex hom constructor gives b.
Its coordinates are the prescribed ones by τ₁ inverse-hom cancellation.
All equations are vacuous for the empty index set. -/
theorem principalOpenCech_coefficient_map_exists
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (g : J ⟶ I) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (T : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val)))),
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
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
      ∃ b : T ⟶ T₁,
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ n).hom (b.f n s) S =
          (modulesSpecToSheaf.map (g.f (n + 1 - (S.val.card : ℤ)))).hom.app
            (op (D S.val)) ((τ n).hom s S)) := by
  classical
  intro D T τ hle he T₁ τ₁ hT hT₁
  let φ (n : ℤ) : T.X n ⟶ T₁.X n :=
    ModuleCat.ofHom
      { toFun := fun s ↦ (τ₁ n).inv (fun S ↦
          (modulesSpecToSheaf.map (g.f (n + 1 - (S.val.card : ℤ)))).hom.app
            (op (D S.val)) ((τ n).hom s S))
        map_add' := fun s t ↦ by
          rw [map_add]
          simp only [Pi.add_apply, map_add]
          rw [← map_add]
          rfl
        map_smul' := fun a s ↦ by
          rw [map_smul]
          simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
          rw [← map_smul]
          rfl }
  have hφ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}) :
      (τ₁ n).hom (φ n s) S =
        (modulesSpecToSheaf.map (g.f (n + 1 - (S.val.card : ℤ)))).hom.app
          (op (D S.val)) ((τ n).hom s S) := by
    change ((τ₁ n).hom ((τ₁ n).inv _)) S = _
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
    rfl
  have hcomm (n : ℤ) : φ n ≫ T₁.d n (n + 1) = T.d n (n + 1) ≫ φ (n + 1) := by
    apply (cancel_mono (τ₁ (n + 1)).hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply funext
    intro S
    change (τ₁ (n + 1)).hom (T₁.d n (n + 1) (φ n s)) S =
      (τ₁ (n + 1)).hom (φ (n + 1) (T.d n (n + 1) s)) S
    rw [hT₁, hφ, hφ, hT]
    let ψ := (modulesSpecToSheaf.map
      (g.f (n + 1 + 1 - (S.val.card : ℤ)))).hom.app (op (D S.val))
    change _ = ψ _
    rw [ψ.hom.map_add, ψ.hom.map_smul, map_sum ψ.hom]
    apply congrArg₂ (· + ·)
    · apply congrArg (_ • ·)
      have hg := congrArg (fun q ↦ (modulesSpecToSheaf.map q).hom.app (op (D S.val)))
        (g.comm (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))
      change
        (modulesSpecToSheaf.map (g.f (n + 1 - (S.val.card : ℤ)))).hom.app
            (op (D S.val)) ≫
          (modulesSpecToSheaf.map
            (I.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
              (op (D S.val)) =
        (modulesSpecToSheaf.map
          (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
            (op (D S.val)) ≫ ψ at hg
      exact ConcreteCategory.congr_hom hg ((τ n).hom s S)
    · apply Finset.sum_congr rfl
      intro j _
      split
      next h =>
        rw [ψ.hom.map_smul, hφ]
        apply congrArg (_ • ·)
        have hcast :
            (modulesSpecToSheaf.map
              (g.f (n + 1 - ((S.val.erase j.val).card : ℤ)))).hom.app
                (op (D (S.val.erase j.val))) ≫
              (modulesSpecToSheaf.map
                (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                  (op (D (S.val.erase j.val))) =
            (modulesSpecToSheaf.map
              (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                (op (D (S.val.erase j.val))) ≫
              (modulesSpecToSheaf.map (g.f (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D (S.val.erase j.val))) := by
          exact coordinateMap_transport g _ _ (he S.val j.val j.property n) _
        have hres := (modulesSpecToSheaf.map
          (g.f (n + 1 + 1 - (S.val.card : ℤ)))).hom.naturality
            (homOfLE (hle S.val j.val)).op
        have hc := ConcreteCategory.congr_hom hcast
          ((τ n).hom s ⟨S.val.erase j.val, h⟩)
        have hr := ConcreteCategory.congr_hom hres
          ((modulesSpecToSheaf.map
            (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
              (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
        simp only [ModuleCat.comp_apply] at hc hr
        exact (congrArg
          ((modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hle S.val j.val)).op) hc).trans hr.symm
      next h => exact ψ.hom.map_zero.symm
  exact ⟨CochainComplex.ofHom φ hcomm, hφ⟩


end AlgebraicGeometry
