/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.PrincipalOpenInjectiveSubsetExact

/-! # Positive-degree exactness of a subset Čech row

Source: Stacks Project, Cohomology, Tags 01EP, 01FM and 08C1.
(blueprint: lem-sc-principal-open-cech-subset-row-primitive).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev rowSections (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (q : ℤ) (U : (Spec (.of A)).Opens) :=
  (modulesSpecToSheaf.obj (J.X q)).obj.obj (op U)

private noncomputable def rowCast (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    {q q' : ℤ} (h : q = q') (U : (Spec (.of A)).Opens) :
    rowSections A J q U →ₗ[A] rowSections A J q' U :=
  ((modulesSpecToSheaf.map (eqToHom (congrArg J.X h))).hom.app (op U)).hom

private theorem rowCast_refl (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (q : ℤ) (U : (Spec (.of A)).Opens) (x : rowSections A J q U) :
    rowCast A J rfl U x = x := by
  simp only [rowCast, eqToHom_refl]
  rfl

private theorem rowCast_injective (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    {q q' : ℤ} (h : q = q') (U : (Spec (.of A)).Opens) :
    Function.Injective (rowCast A J h U) := by
  subst q'
  intro x y hxy
  simpa only [rowCast_refl] using hxy

private theorem rowCast_inverse (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    {q q' : ℤ} (h : q = q') (U : (Spec (.of A)).Opens)
    (x : rowSections A J q U) :
    rowCast A J h.symm U (rowCast A J h U x) = x := by
  subst q'
  simp only [rowCast_refl]

private theorem rowCast_comp (A : Type u) [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    {a b q : ℤ} (h : a = q) (hb : b = a) (hbq : b = q)
    {U V : (Spec (.of A)).Opens} (i : U ⟶ V) (x : rowSections A J b V) :
    rowCast A J h U
        ((modulesSpecToSheaf.obj (J.X a)).obj.map i.op (rowCast A J hb V x)) =
      (modulesSpecToSheaf.obj (J.X q)).obj.map i.op (rowCast A J hbq V x) := by
  subst q
  subst b
  simp [rowCast_refl]

/-- Positive-degree exactness of the subset Čech row, with integer transports.

Source: Stacks Project, Cohomology, Tags 01EP, 01FM and 08C1 (first paragraph).
(blueprint: lem-sc-principal-open-cech-subset-row-primitive).

Proof: Put q=n+1-k. Cast the coefficients on subsets of size k+1 to the
fixed module J.X q and set all other coefficients to zero. Apply the cast on
size k+2 to the assumed cocycle equation. It preserves sums and scalar signs;
the cast commutes with restriction and with the supplied deletion cast he.
Every deletion has size k+1, so this is a fixed-coefficient subset cocycle.
The fixed-coefficient exactness theorem gives a primitive: full Čech acyclicity
for the injective module comes from Tag 01EP, while the comparison to increasing
tuples and their finite ranges comes from Tag 01FM. The latter works for any
family of opens and has no cover hypothesis. Cast the primitive coefficients
back on subsets of size k and extend by zero at all other cardinalities.
On size k+1 every deletion has size k. Cast the desired equation to J.X q;
restriction naturality and inverse casts identify it with the primitive equation.
The cast is injective, giving the desired equation before transport.
All casts are functorial eqToHom maps, whose identities follow by equality
elimination and proof irrelevance. No differential of J or total complex is used.
Empty or repeated opens, the empty index set and degrees above r-1 are included. -/
theorem principalOpenCech_subset_row_primitive
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (k : ℕ), 1 ≤ k → Injective (J.X (n + 1 - (k : ℤ))) →
      ∀ c : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))),
      (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 2 →
        (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property (n + 1))))).hom.app
                    (op (D (S.val.erase j.val))) (c ⟨S.val.erase j.val, h⟩))
          else 0) = 0) →
      ∃ b : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
          (op (D S.val))),
        (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card ≠ k → b S = 0) ∧
        (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 1 →
          (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) (b ⟨S.val.erase j.val, h⟩))
          else 0) = c S) := by
  classical
  dsimp only
  intro hle he n k hk hInject c hc
  let D : Finset (Fin r) → (Spec (.of A)).Opens :=
    fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
  let q : ℤ := n + 1 - (k : ℤ)
  have cq (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = k + 1) :
      n + 1 + 1 - (S.val.card : ℤ) = q := by dsimp [q]; omega
  let c' : ∀ S : {S : Finset (Fin r) // S.Nonempty}, rowSections A J q (D S.val) :=
    fun S ↦ if h : S.val.card = k + 1 then rowCast A J (cq S h) (D S.val) (c S)
      else 0
  have hc' : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 2 →
      (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
        (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
          (modulesSpecToSheaf.obj (J.X q)).obj.map (homOfLE (hle S.val j.val)).op
            (c' ⟨S.val.erase j.val, h⟩) else 0) = 0 := by
    intro S hS
    have hq : n + 1 + 1 + 1 - (S.val.card : ℤ) = q := by dsimp [q]; omega
    have hh := congrArg (rowCast A J hq (D S.val)) (hc S hS)
    rw [map_sum, map_zero] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : (S.val.erase j.val).card = k + 1 := by
      rw [Finset.card_erase_of_mem j.property, hS]
      omega
    split_ifs with h
    · dsimp only [c']
      rw [dite_eq_left hj, map_smul]
      exact congrArg (fun z ↦ (-1 : A) ^
        ((S.val.filter (fun i ↦ i < j.val)).card) • z)
        (rowCast_comp A J hq (he S.val j.val j.property (n + 1))
          (cq ⟨S.val.erase j.val, h⟩ hj) (homOfLE (hle S.val j.val))
          (c ⟨S.val.erase j.val, h⟩)).symm
    · simp
  obtain ⟨b', hb'⟩ := principalOpen_injective_subset_exact A r f (J.X q)
    hle k hk hInject c' hc'
  have bq (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = k) :
      q = n + 1 - (S.val.card : ℤ) := by dsimp [q]; omega
  let b : ∀ S : {S : Finset (Fin r) // S.Nonempty},
      rowSections A J (n + 1 - (S.val.card : ℤ)) (D S.val) :=
    fun S ↦ if h : S.val.card = k then rowCast A J (bq S h) (D S.val) (b' S)
      else 0
  refine ⟨b, ?_, ?_⟩
  · intro S hS
    exact dite_eq_right hS
  · intro S hS
    have hq : n + 1 + 1 - (S.val.card : ℤ) = q := cq S hS
    apply rowCast_injective A J hq (D S.val)
    rw [map_sum]
    have hh := hb' S hS
    change _ = c' S at hh
    rw [show c' S = rowCast A J hq (D S.val) (c S) from dite_eq_left hS] at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (S.val.erase j.val).card = k := by
      rw [Finset.card_erase_of_mem j.property, hS]
      omega
    split_ifs with h
    · dsimp only [b]
      rw [dite_eq_left hj, map_smul]
      have hbq : n + 1 - ((S.val.erase j.val).card : ℤ) = q :=
        (bq ⟨S.val.erase j.val, h⟩ hj).symm
      have hcast : rowCast A J hbq (D (S.val.erase j.val))
          (rowCast A J (bq ⟨S.val.erase j.val, h⟩ hj) (D (S.val.erase j.val))
            (b' ⟨S.val.erase j.val, h⟩)) = b' ⟨S.val.erase j.val, h⟩ :=
        rowCast_inverse A J (bq ⟨S.val.erase j.val, h⟩ hj) _ _
      exact congrArg (fun z ↦ (-1 : A) ^
        ((S.val.filter (fun i ↦ i < j.val)).card) • z)
        ((rowCast_comp A J hq (he S.val j.val j.property n) hbq
          (homOfLE (hle S.val j.val))
          (rowCast A J (bq ⟨S.val.erase j.val, h⟩ hj) (D (S.val.erase j.val))
            (b' ⟨S.val.erase j.val, h⟩))).trans
          (congrArg ((modulesSpecToSheaf.obj (J.X q)).obj.map
            (homOfLE (hle S.val j.val)).op) hcast))
    · simp

end AlgebraicGeometry
