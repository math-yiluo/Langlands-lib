/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechColumnStep
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSingletonGluing

/-! # principal-open Čech augmentation for injective terms

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-injective-terms).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The singleton restrictions detect equality by sheaf separatedness. -/
private theorem principalOpenCech_component_injective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∀ n : ℤ, Function.Injective (α.f n) := by
  dsimp only
  intro K T σ τ α hls hes hα n s t hst
  apply (ModuleCat.mono_iff_injective (σ n).hom).mp inferInstance
  let U : Fin r → (Spec (.of A)).Opens := fun i ↦ PrimeSpectrum.basicOpen (f i)
  apply (modulesSpecToSheaf.obj (J.X n)).eq_of_locally_eq U
  intro i
  have h := congrArg (fun z ↦ (τ n).hom z ⟨{i}, Finset.singleton_nonempty i⟩) hst
  rw [hα, hα] at h
  let S : {S : Finset (Fin r) // S.Nonempty} := ⟨{i}, Finset.singleton_nonempty i⟩
  have hcard : S.val.card = 1 := Finset.card_singleton i
  rw [dite_eq_left hcard, dite_eq_left hcard] at h
  let e := modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S hcard n)))
  have hs := ConcreteCategory.congr_hom (e.hom.naturality
    (homOfLE (hls S hcard)).op) ((σ n).hom s)
  have ht := ConcreteCategory.congr_hom (e.hom.naturality
    (homOfLE (hls S hcard)).op) ((σ n).hom t)
  simp only [ConcreteCategory.comp_apply] at hs ht
  change _ = _ at h
  rw [← hs, ← ht] at h
  have hinj := (ModuleCat.mono_iff_injective (e.hom.app
    (op (PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j))))).mp inferInstance
  have hh := hinj h
  have hopen : PrimeSpectrum.basicOpen (f i) =
      PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j) := by simp [S]
  have hh' := congrArg (fun z ↦ ((modulesSpecToSheaf.obj (J.X n)).obj.map
    (eqToHom hopen).op) z) hh
  simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp,
    ← op_comp] at hh'
  have heq : eqToHom hopen ≫ homOfLE (hls S hcard) =
      TopologicalSpace.Opens.leSupr U i :=
    Subsingleton.elim _ _
  rw [heq] at hh'
  simpa only [ConcreteCategory.comp_apply] using hh' 

/-- An elementwise boundary lift detects injectivity on homology. -/
private theorem homology_mono_of_boundary_lift
    {A : Type u} [CommRing A] {K T : CochainComplex (ModuleCat.{u} A) ℤ}
    (α : K ⟶ T) (n : ℤ)
    (hlift : ∀ (s : K.X n) (t : T.X ((ComplexShape.up ℤ).prev n)),
      α.f n s = T.d ((ComplexShape.up ℤ).prev n) n t →
        ∃ x : K.X ((ComplexShape.up ℤ).prev n),
          K.d ((ComplexShape.up ℤ).prev n) n x = s) :
    Mono (HomologicalComplex.homologyMap α n) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  have hp : T.pOpcycles n (α.f n (K.iCycles n c)) = 0 := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.homology_π_ι (K := T) n)
      ((HomologicalComplex.cyclesMap α n) c)
    have hc := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i α n) c
    have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality α n) c
    simp only [ConcreteCategory.comp_apply] at h hc hn
    rw [← hc, ← h, ← hn, hz, map_zero]
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (T.sc n) _).mp hp
  have ht' : α.f n (K.iCycles n c) = T.d ((ComplexShape.up ℤ).prev n) n t := by
    exact ht.symm
  obtain ⟨x, hx⟩ := hlift (K.iCycles n c) t ht'
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [map_zero]
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homology_π_ι (K := K) n) c
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  apply (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc n) _).mpr
  exact ⟨x, hx⟩

/-- The finite subset Čech augmentation for a complex with injective terms
induces monomorphisms on homology, without any boundedness or K-injectivity assumption.

Source: Stacks Project, Cohomology, Tag 08C1, finite exact augmented row argument.
(blueprint: lem-sc-principal-open-cech-injective-terms).

Proof: Each I.X n is injective as a sheaf of modules and hence flasque. The augmented
Čech row for the finite cover of V is exact: sheaf separation gives injectivity at
sections, gluing identifies the degree-zero kernel, and injective-module Čech
acyclicity gives exactness in positive degrees. Restrict the tuple model to increasing
tuples, using the alternating Čech comparison, and identify increasing tuples with
finite subsets. Their deletion positions are exactly the displayed filter-cardinality
signs. These identifications give row exactness for the formulas in the statement.
Given a section cocycle whose augmentation is the boundary of t, start at the largest
Čech column of t. Its horizontal differential is zero because the boundary has no
components above column zero. Row exactness produces a horizontal primitive in the
preceding column. Subtract its total differential from t. This preserves the total
boundary and removes that column, changing only the preceding column. Iterate down
through the r finite columns. At column zero, exactness identifies the remaining
primitive as the augmentation of a section. The chain-map identity and injectivity
of the augmented row show that the given section is its vertical boundary. Thus the
kernel of each homology map is zero. The zero-module interpretation of sections on
the empty open proves the r=0 case; repeated and empty opens do not change exactness.
The proof uses injectivity of the terms, never K-injectivity of the complex. -/
theorem principalOpenCech_homology_mono_of_injective_terms
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hJ : ∀ n : ℤ, Injective (J.X n)) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
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
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∀ n : ℤ, Mono (HomologicalComplex.homologyMap α n) := by
  classical
  dsimp only
  intro K T σ τ α hle hls he hes hK hT hα n
  have hinj := principalOpenCech_component_injective A r f J K T σ τ α hls hes hα
  have reduce : ∀ (q : ℤ) (m : ℕ) (t : T.X q),
      (∀ S : {S : Finset (Fin r) // S.Nonempty},
        m + 1 < S.val.card → (τ q).hom t S = 0) →
      (∀ S : {S : Finset (Fin r) // S.Nonempty},
        1 < S.val.card → (τ (q + 1)).hom (T.d q (q + 1) t) S = 0) →
      ∃ t' : T.X q, T.d q (q + 1) t' = T.d q (q + 1) t ∧
        ∀ S : {S : Finset (Fin r) // S.Nonempty},
          1 < S.val.card → (τ q).hom t' S = 0 := by
    intro q m
    induction m with
    | zero =>
      intro t ht _
      exact ⟨t, rfl, ht⟩
    | succ m ih =>
      intro t ht hdt
      obtain ⟨u, hu⟩ := principalOpenCech_column_step A r f J T τ hle he hT
        q (m + 1) (by omega) (hJ (q - ((m + 1 : ℕ) : ℤ))) t ht hdt
      have hd : T.d q (q + 1) (t - T.d (q - 1) q u) = T.d q (q + 1) t := by
        rw [map_sub]
        have hz := ConcreteCategory.congr_hom (T.d_comp_d (q - 1) q (q + 1)) u
        simp only [ConcreteCategory.comp_apply] at hz
        change T.d q (q + 1) (T.d (q - 1) q u) = 0 at hz
        rw [hz, sub_zero]
      obtain ⟨t', ht', hs⟩ := ih (t - T.d (q - 1) q u) hu (by rw [hd]; exact hdt)
      exact ⟨t', ht'.trans hd, hs⟩
  apply homology_mono_of_boundary_lift α n
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change n - 1 + 1 = n; omega)
  change ∀ (s : K.X n) (t : T.X ((ComplexShape.up ℤ).prev n)),
    α.f n s = T.d ((ComplexShape.up ℤ).prev n) n t →
      ∃ x : K.X ((ComplexShape.up ℤ).prev n), K.d ((ComplexShape.up ℤ).prev n) n x = s
  rw [hprev]
  intro s t ht
  have hn : n - 1 + 1 = n := by omega
  have hdt : ∀ S : {S : Finset (Fin r) // S.Nonempty},
      1 < S.val.card → (τ (n - 1 + 1)).hom (T.d (n - 1) (n - 1 + 1) t) S = 0 := by
    rw [hn, ← ht]
    intro S hS
    rw [hα, dite_eq_right (by omega)]
  obtain ⟨t', hsame, hs⟩ := reduce (n - 1) r t (by
    intro S hS
    have hcard : S.val.card ≤ r := by
      simpa using Finset.card_le_univ S.val
    omega) hdt
  obtain ⟨x, hx⟩ := principalOpenCech_singleton_gluing A r f J K T σ τ α
    hle hls he hes hT hα (n - 1) t' hs (by rw [hsame]; exact hdt)
  refine ⟨x, hinj n ?_⟩
  have hc := ConcreteCategory.congr_hom (α.comm (n - 1) n) x
  simp only [ConcreteCategory.comp_apply] at hc
  rw [← hc, hx]
  rw [hn] at hsame
  exact hsame.trans ht.symm

end AlgebraicGeometry
