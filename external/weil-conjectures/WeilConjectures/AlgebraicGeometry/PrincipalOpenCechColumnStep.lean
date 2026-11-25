/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetRowPrimitive

/-! # Single-column cancellation in subset Čech coordinates

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-column-step).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Eliminate one highest positive Čech column by a total boundary.

Source: Stacks Project, Cohomology, Tag 08C1, first paragraph, using the
finite-row argument of Homology Lemma 12.25.4.
(blueprint: lem-sc-principal-open-cech-column-step).

Proof: Put q = n - k. The coordinates of t of cardinality k+1 form a
horizontal Čech k-cochain with coefficients J.X q. At every subset of
cardinality k+2 the vertical contribution to d(t) vanishes by the support
hypothesis, and the horizontal contribution vanishes by the hypothesis on
d(t). This cochain is therefore horizontally closed.
Apply injective module Čech acyclicity to the cover D(f_i) of its union V;
this theorem applies to any open V, not only the whole spectrum. The
alternating comparison restricts the row to increasing tuples. Identify
each increasing tuple with its range, whose basic product open is the
intersection of its basic opens. Vanishing cohomology in degree k (k > 0)
then gives a horizontal primitive in degree k-1. Place it in the cardinality-k
coordinates of u and set every other coordinate to zero. Its horizontal
differential cancels the cardinality-(k+1) coordinates of t; its signed
vertical differential only changes cardinality-k coordinates. Above k+1
both t and d(u) vanish. The deletion rank is precisely the number of elements
less than the deleted index, so the signed coordinate formulas agree.
The integer transports are the stated he equalities. If k+1 exceeds r,
the cochain to eliminate is zero and u=0 suffices. Empty or repeated basic
opens cause no change to Čech exactness. -/
theorem principalOpenCech_column_step
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (T : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ)),
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
      ∀ (n : ℤ) (k : ℕ), 1 ≤ k → Injective (J.X (n - (k : ℤ))) → ∀ t : T.X n,
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          k + 1 < S.val.card → (τ n).hom t S = 0) →
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          1 < S.val.card → (τ (n + 1)).hom (T.d n (n + 1) t) S = 0) →
        ∃ u : T.X (n - 1), ∀ S : {S : Finset (Fin r) // S.Nonempty},
          k < S.val.card → (τ n).hom (t - T.d (n - 1) n u) S = 0 := by
  classical
  dsimp
  intro T τ hle he hdiff n k hk hInject t htop hdt
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Int.add_sub_cancel]
  have hclosed : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 2 →
      (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X ((m + 1) + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property (m + 1))))).hom.app
                    (op (PrimeSpectrum.basicOpen (∏ i ∈ S.val.erase j.val, f i)))
                      ((τ (m + 1)).hom t ⟨S.val.erase j.val, h⟩))
          else 0) = 0 := by
    intro S hS
    have htS := htop S (by omega)
    have hdS := hdt S (by omega)
    have hh := hdiff (m + 1) t S
    rw [htS, map_zero, smul_zero, zero_add, hdS] at hh
    exact hh.symm
  obtain ⟨b, hbSupport, hbRow⟩ :=
    principalOpenCech_subset_row_primitive A r f J hle he m k hk hInject
      ((τ (m + 1)).hom t) hclosed
  let u : T.X m := (τ m).inv b
  have hu : (τ m).hom u = b := by
    exact ConcreteCategory.congr_hom (Iso.inv_hom_id (τ m)) b
  refine ⟨u, ?_⟩
  intro S hS
  have hd := hdiff m u S
  rw [hu] at hd
  have hbS : b S = 0 := hbSupport S (by omega)
  rw [hbS, map_zero, smul_zero, zero_add] at hd
  have hdS : (τ (m + 1)).hom (T.d m (m + 1) u) S = (τ (m + 1)).hom t S := by
    by_cases heq : S.val.card = k + 1
    · exact hd.trans (hbRow S heq)
    · have hlarge : k + 1 < S.val.card := by omega
      rw [htop S hlarge]
      rw [hd]
      apply Finset.sum_eq_zero
      intro j hj
      split_ifs with hjnon
      · rw [hbSupport ⟨S.val.erase j.val, hjnon⟩ (by
          have hecard := Finset.card_erase_of_mem j.property
          change (S.val.erase j.val).card ≠ k
          omega), map_zero, map_zero, smul_zero]
      · rfl
  rw [map_sub]
  change (τ (m + 1)).hom t S - (τ (m + 1)).hom (T.d m (m + 1) u) S = 0
  exact sub_eq_zero.mpr hdS.symm


end AlgebraicGeometry
