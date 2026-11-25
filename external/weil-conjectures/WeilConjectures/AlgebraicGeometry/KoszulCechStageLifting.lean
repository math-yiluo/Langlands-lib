/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Finite-stage lifting for the Koszul-to-Čech cocone

Source: Stacks, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-stage-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Clear denominators separately, then enlarge every power to a common positive exponent.
private theorem finite_affine_denominators
    (A : Type u) [CommRing A] (ι : Type) [Finite ι]
    (G : ι → SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    (hG : ∀ i, (G i).IsQuasicoherent) (g : ι → A)
    (s : ∀ i, (affineOpenSections A (PrimeSpectrum.basicOpen (g i))).obj (G i)) :
    ∃ (e : ℕ) (m : ∀ i, (affineOpenSections A ⊤).obj (G i)), ∀ i,
      g i ^ (e + 1) • s i =
        (modulesSpecToSheaf.obj (G i)).obj.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen (g i) ≤ ⊤)).op (m i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hs (i : ι) : ∃ (d : ℕ) (m : (affineOpenSections A ⊤).obj (G i)),
      g i ^ d • s i = (modulesSpecToSheaf.obj (G i)).obj.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (g i) ≤ ⊤)).op m := by
    have : (G i).IsQuasicoherent := hG i
    have hl := (isIso_fromTildeΓ_iff_isLocalizing (R := .of A) (G i)).mp
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) (G i)) (g i)
    have : IsLocalizedModule.Away (g i)
        ((modulesSpecToSheaf.obj (G i)).obj.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen (g i) ≤ ⊤)).op).hom := hl
    exact IsLocalizedModule.Away.surj _ (g i) (s i)
  choose d m hd using hs
  let e := Finset.univ.sup d
  have hde (i : ι) : d i ≤ e + 1 :=
    (Finset.le_sup (f := d) (Finset.mem_univ i)).trans (Nat.le_succ e)
  refine ⟨e, fun i ↦ g i ^ (e + 1 - d i) • m i, ?_⟩
  intro i
  rw [map_smul, ← hd i, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hde i)]

-- Prescribe all exterior-basis values in every nonpositive source degree.
private theorem koszul_basis_values
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (e : ℕ) (n : ℤ)
    (m : ∀ J : {J : Finset (Fin r) // J.Nonempty}, M.X (n + 1 - (J.val.card : ℤ))) :
    ∃ z : CochainComplex.HomComplex.Cochain
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M n,
      ∀ J : {J : Finset (Fin r) // J.Nonempty},
        (z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
          (koszulCech_evaluation_degree r J.val n))
            (koszulCechBasis A r f e J.val J.property) = m J := by
  classical
  let L := koszulOpenTail A r f e
  have hk (p : ℤ) (h : p ≤ 0) :
      ComplexShape.embeddingDownNat.f (-p).toNat = p := by
    simp only [ComplexShape.embeddingDownNat_f, Int.toNat_of_nonneg (by omega : 0 ≤ -p)]
    omega
  have hq (k : ℕ) (p q : ℤ)
      (hkp : ComplexShape.embeddingDownNat.f k = p) (hpq : p + n = q)
      (J : Set.powersetCard (Fin r) (k + 1)) : n + 1 - (J.val.card : ℤ) = q := by
    have hc : J.val.card = k + 1 := J.property
    simp only [ComplexShape.embeddingDownNat_f] at hkp
    omega
  have hJ (k : ℕ) (J : Set.powersetCard (Fin r) (k + 1)) : J.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [J.property]
    omega
  let v (k : ℕ) (p q : ℤ) (hkp : ComplexShape.embeddingDownNat.f k = p)
      (hpq : p + n = q) : (L.extend ComplexShape.embeddingDownNat).X p ⟶ M.X q :=
    (L.extendXIso ComplexShape.embeddingDownNat hkp).hom ≫
      ModuleCat.ofHom (((Finsupp.basisSingleOne (R := A) (ι := Fin r)).exteriorPower
        (k + 1)).constr A (fun J ↦
          (eqToHom (congrArg M.X (hq k p q hkp hpq J))) (m ⟨J.val, hJ k J⟩)))
  let z := CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦
    if h : p ≤ 0 then v (-p).toNat p q (hk p h) hpq else 0)
  refine ⟨z, ?_⟩
  intro J
  have hj : 0 < J.val.card := Finset.card_pos.mpr J.property
  have hp : 1 - (J.val.card : ℤ) ≤ 0 := by omega
  have ht : (-(1 - (J.val.card : ℤ))).toNat = J.val.card - 1 := by omega
  dsimp only [z]
  rw [CochainComplex.HomComplex.Cochain.mk_v, dite_eq_left hp]
  simp only [ht]
  dsimp only [v, L]
  simp only [koszulCechBasis, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  let sJ : Set.powersetCard (Fin r) (J.val.card - 1 + 1) :=
    ⟨J.val, koszulCech_basis_card r J.val J.property⟩
  have hb : (Finsupp.basisSingleOne (R := A) (ι := Fin r)).exteriorPower
      (J.val.card - 1 + 1) sJ =
      exteriorPower.ιMulti A (J.val.card - 1 + 1)
        (fun i ↦ Finsupp.single (J.val.orderEmbOfFin
          (koszulCech_basis_card r J.val J.property) i) (1 : A)) := by
    rw [exteriorPower.basis_apply]
    rfl
  rw [← hb]
  simp only [ModuleCat.hom_ofHom]
  have hb' := (Finsupp.basisSingleOne (R := A) (ι := Fin r)).exteriorPower
    (J.val.card - 1 + 1) |>.constr_basis A
      (fun J_1 ↦ (eqToHom (congrArg M.X
        (hq (J.val.card - 1) (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
          (koszulCech_basis_degree r J.val J.property)
          (koszulCech_evaluation_degree r J.val n) J_1))) (m ⟨J_1.val, hJ _ J_1⟩)) sJ
  exact hb'.trans (by simp only [sJ, eqToHom_refl, ModuleCat.id_apply])

/-- Every total Čech cochain is the image of a cochain at one positive Koszul exponent.
Source: Stacks, Tag 08D0, proof's localization description, and Tag 08D1,
finite total-degree diagonals (blueprint: lem-sc-koszul-cech-stage-lifting).

Proof: Transport the target through principalCechObjIso. For each nonempty subset J,
put p = card(J)-1 and q = n-p. Quasi-coherence on Spec(A) identifies its section on
D(g_J), where g_J is the product of the f_j, with the localization of global
sections of F.X q. Write that section, after multiplication by the inverse of
Int.negOnePow(p*q+p*(p-1)/2), as m_J/g_J^d_J. There are finitely many J, so choose
E >= 1 and E >= d_J for all J. Replace m_J by g_J^(E-d_J) m_J. At stage e = E-1,
define each linear map on the ordered exterior basis by these numerators. Terms
outside the tail's finite support are zero. The free exterior bases therefore give
a homogeneous module Hom cochain, and koszulCechHomObjIso transports it to the
specified diagram. The cocone formula gives exactly the chosen sections: g_J is
invertible on D(g_J), so the formula can be divided by g_J^E. Transport back through
principalCechObjIso. For r=0 the target has no coordinates, and the zero cochain at
stage 0 suffices; for zero or nilpotent g_J its localized section module is zero.
This argument uses cochains, with no cycle or boundedness condition on F. -/
theorem koszulCechCocone_stage_lifting
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) (n : ℤ)
    (y : ((principalCechFunctor r f).obj F).X n) :
    ∃ (e : ℕ) (z : ((koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).obj
        e).X n),
      (((koszulCechCocone A r f F).ι.app e ≫
        eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n) z = y := by
  classical
  let M := (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
  let t : principalCechTerms r f F n := (principalCechObjIso r f F).hom.f n y
  let σ (J : {J : Finset (Fin r) // J.Nonempty}) := Int.negOnePow
    ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
      ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))
  obtain ⟨e, m, hm⟩ := finite_affine_denominators A
    {J : Finset (Fin r) // J.Nonempty}
    (fun J ↦ F.X (n + 1 - (J.val.card : ℤ)))
    (fun J ↦ hF _) (fun J ↦ ∏ j ∈ J.val, f j) (fun J ↦ (σ J)⁻¹ • t J)
  obtain ⟨z, hz⟩ := koszul_basis_values A r f M e n m
  let zi := (koszulCechHomObjIso A r f M e).inv.f n z
  refine ⟨e, zi, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((principalCechObjIso r f F).hom.f n)).injective
  change (((koszulCechHomObjIso A r f M e).inv ≫
    (koszulCechCocone A r f F).ι.app e ≫
    eqToHom (koszulCechCocone_exists A r f F).choose_spec.1 ≫
    (principalCechObjIso r f F).hom).f n) z = t
  funext J
  have hreg : IsSMulRegular
      ((affineOpenSections A (principalCechIntersection r f J.val)).obj
        (F.X (n + 1 - (J.val.card : ℤ)))).carrier (∏ j ∈ J.val, f j) := by
    exact Scheme.Modules.isSMulRegular_of_le_basicOpen
      (M := F.X (n + 1 - (J.val.card : ℤ)))
      (U := principalCechIntersection r f J.val) le_rfl
  apply hreg.pow (e + 1)
  dsimp only
  have hc := (koszulCechCocone_exists A r f F).choose_spec.2 e n z J
    (koszulCechCocone_exists A r f F).choose_spec.1
  change (∏ j ∈ J.val, f j) ^ (e + 1) • _ = _ at hc
  rw [hz J] at hc
  refine hc.trans ?_
  change σ J • _ = _
  have hs := congrArg (fun x ↦ σ J • x) (hm J).symm
  simp only [smul_comm (σ J), inv_smul_smul] at hs
  exact hs

end AlgebraicGeometry
