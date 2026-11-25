/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Data.Fintype.Order

/-! # Eventual vanishing in the kernel of the Koszul-to-Čech cocone

Source: Stacks, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-stage-kernel)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem affine_section_torsion
    (A : Type u) [CommRing A]
    (G : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    (hG : G.IsQuasicoherent) (g : A) (m : (affineOpenSections A ⊤).obj G)
    (hm : (modulesSpecToSheaf.obj G).obj.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen g ≤ ⊤)).op m = 0) :
    ∃ k : ℕ, g ^ k • m = 0 := by
  have := hG
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing G).mp
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G) g
  have := hloc
  let ρ := ((modulesSpecToSheaf.obj G).obj.map (PrimeSpectrum.basicOpen g).leTop.op).hom
  have hm' : ρ m = 0 := hm
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff
    (R := CommRingCat.of A) (Submonoid.powers g) ρ).mp hm'
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff s.val g).mp s.property
  exact ⟨k, hk ▸ hs⟩

private theorem extended_evaluation_zero_iff
    (A : Type u) [CommRing A] (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      (K.extend ComplexShape.embeddingDownNat) M n)
    (m : ℕ) (x : K.X m) (c : A) (p q : ℤ)
    (hp : ComplexShape.embeddingDownNat.f m = p) (hpq : p + n = q) :
    c • (z.v (ComplexShape.embeddingDownNat.f m)
      (ComplexShape.embeddingDownNat.f m + n) rfl)
        ((K.extendXIso ComplexShape.embeddingDownNat rfl).inv x) = 0 ↔
    c • (z.v p q hpq) ((K.extendXIso ComplexShape.embeddingDownNat hp).inv x) = 0 := by
  subst p
  subst q
  rfl

private theorem koszul_transition_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℕ) (h : a ≤ b) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat) M n)
    (hz : ∀ (J : Finset (Fin r)) (hJ : J.Nonempty),
      (∏ j ∈ J, f j) ^ (b - a) •
        (z.v (1 - (J.card : ℤ)) (n + 1 - (J.card : ℤ))
          (koszulCech_evaluation_degree r J n)) (koszulCechBasis A r f a J hJ) = 0) :
    (CochainComplex.HomComplex.Cochain.ofHom
      (HomologicalComplex.extendMap (koszulOpenTransition A r f a b h)
        ComplexShape.embeddingDownNat)).comp z (zero_add n) = 0 := by
  classical
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  simp only [CochainComplex.HomComplex.Cochain.zero_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  by_cases hp : ∃ m : ℕ, ComplexShape.embeddingDownNat.f m = p
  · obtain ⟨m, rfl⟩ := hp
    rw [HomologicalComplex.extendMap_f _ _ rfl]
    apply (cancel_epi ((koszulOpenTail A r f b).extendXIso
      ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f m = _)).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, comp_zero]
    apply ModuleCat.hom_ext
    apply ((Finsupp.basisSingleOne (R := A) (ι := Fin r)).exteriorPower (m + 1)).ext
    rintro ⟨J, hc⟩
    change J.card = m + 1 at hc
    have hJ : J.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
    have hm : J.card - 1 = m := by omega
    have hdeg : ComplexShape.embeddingDownNat.f m = 1 - (J.card : ℤ) := by
      simp only [ComplexShape.embeddingDownNat_f]
      omega
    have hq : q = n + 1 - (J.card : ℤ) := by
      simp only [ComplexShape.embeddingDownNat_f] at hpq
      omega
    subst q
    let B := (Finsupp.basisSingleOne (R := A) (ι := Fin r)).exteriorPower (m + 1)
    have hd (i : Fin r) : koszulOpenDiagonal A r f (b - a) (Finsupp.single i 1) =
        f i ^ (b - a) • Finsupp.single i 1 := by
      simp [koszulOpenDiagonal, Finsupp.smul_single]
    have hprod : (∏ i : Fin (m + 1), f (J.orderEmbOfFin hc i)) =
        ∏ j ∈ J, f j := by
      simpa only [Finset.map_orderEmbOfFin_univ, RelEmbedding.coe_toEmbedding] using
        (Finset.prod_map Finset.univ (J.orderEmbOfFin hc).toEmbedding f).symm
    have hB : exteriorPower.map (m + 1) (koszulOpenDiagonal A r f (b - a)) (B ⟨J, hc⟩) =
        (∏ j ∈ J, f j) ^ (b - a) • B ⟨J, hc⟩ := by
      dsimp only [B]
      rw [exteriorPower.basis_apply]
      dsimp only [exteriorPower.ιMulti_family]
      rw [exteriorPower.map_apply_ιMulti]
      simp only [Finsupp.coe_basisSingleOne]
      change (exteriorPower.ιMulti A (m + 1))
        (fun i ↦ koszulOpenDiagonal A r f (b - a)
          (Finsupp.single (J.orderEmbOfFin hc i) 1)) = _
      simp_rw [hd]
      rw [AlternatingMap.map_smul_univ]
      have hprod' : (∏ i : Fin (m + 1), f (J.orderEmbOfFin hc i) ^ (b - a)) =
          (∏ j ∈ J, f j) ^ (b - a) := by
        rw [Finset.prod_pow]
        exact congrArg (fun t : A ↦ t ^ (b - a)) hprod
      rw [hprod']
      rfl
    change (z.v (ComplexShape.embeddingDownNat.f m)
        (ComplexShape.embeddingDownNat.f m + n) _)
      (((koszulOpenTail A r f a).extendXIso ComplexShape.embeddingDownNat rfl).inv
        (exteriorPower.map (m + 1) (koszulOpenDiagonal A r f (b - a)) (B ⟨J, hc⟩))) = 0
    rw [hB, map_smul, map_smul]
    have hh := hz J hJ
    simp only [koszulCechBasis] at hh
    simp only [B, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      Finsupp.coe_basisSingleOne, Set.powersetCard.ofFinEmbEquiv_symm_apply,
      Function.comp_def]
    clear hB hprod B
    subst m
    exact (extended_evaluation_zero_iff A (koszulOpenTail A r f a) M n z
      (J.card - 1) _ ((∏ j ∈ J, f j) ^ (b - a))
      (1 - (J.card : ℤ)) (n + 1 - (J.card : ℤ)) hdeg
      (koszulCech_evaluation_degree r J n)).mpr hh
  · rw [HomologicalComplex.extendMap_f_eq_zero _ _ p (by simpa using hp), zero_comp]

/-- A finite-stage cochain with zero Čech image becomes zero at a later stage.
Source: Stacks, Tag 08D0, proof's localization equality criterion, and Tag 08D1,
finite total-degree diagonals (blueprint: lem-sc-koszul-cech-stage-kernel).

Proof: Transport z through koszulCechHomObjIso and evaluate on the ordered exterior
basis indexed by nonempty subsets J. Put g_J = product of f_j over J. Transport
the zero-image hypothesis through principalCechObjIso. The cocone's formula and
invertibility of its sign imply that every global-section coordinate m_J restricts
to zero on D(g_J). By affine quasi-coherence this restriction is localization at
g_J; the localization zero criterion gives a power g_J^k_J annihilating m_J.
Choose k at least every k_J, possible since there are finitely many nonempty J.
The specified transition from e to b = e+k multiplies the J-coordinate by g_J^k,
so every coordinate at b is zero. The ordered exterior bases detect equality of
the linear cochain components; the other tail terms are zero. Hence the cochain
at b is zero. The diagram's object identifications transport this equality to
its actual map. For r=0 there are no coordinates and z is already zero (b=e);
for r=1 this is the usual localization zero criterion; nilpotent generators and
F=0 require no exception. No assumption that z is a cycle is used. -/
theorem koszulCechCocone_stage_kernel
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) (n : ℤ) (e : ℕ)
    (z : ((koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).obj
        e).X n)
    (hz : (((koszulCechCocone A r f F).ι.app e ≫
      eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n) z = 0) :
    ∃ (b : ℕ) (h : e ≤ b),
      (((koszulCechHomDiagram A r f
        (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).map
          (homOfLE h)).f n) z = 0 := by
  classical
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let D := koszulCechHomDiagram A r f M
  let w : CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M n :=
    ((koszulCechHomObjIso A r f M e).hom.f n) z
  have hw : ((koszulCechHomObjIso A r f M e).inv.f n) w = z := by
    change (((koszulCechHomObjIso A r f M e).hom ≫
      (koszulCechHomObjIso A r f M e).inv).f n) z = z
    simp
  have hzero : (((koszulCechHomObjIso A r f M e).inv ≫
      (koszulCechCocone A r f F).ι.app e ≫
      eqToHom (koszulCechCocone_exists A r f F).choose_spec.1 ≫
      (principalCechObjIso r f F).hom).f n) w = 0 := by
    change ((principalCechObjIso r f F).hom.f n)
      ((((koszulCechCocone A r f F).ι.app e ≫
        eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n)
          (((koszulCechHomObjIso A r f M e).inv.f n) w)) = 0
    rw [hw, hz, map_zero]
  have ht : ∀ J : {J : Finset (Fin r) // J.Nonempty}, ∃ k : ℕ,
      (∏ j ∈ J.val, f j) ^ k •
        (w.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
          (koszulCech_evaluation_degree r J.val n))
          (koszulCechBasis A r f e J.val J.property) = 0 := by
    intro J
    have heq := (koszulCechCocone_exists A r f F).choose_spec.2 e n w J
      (koszulCechCocone_exists A r f F).choose_spec.1
    change (∏ j ∈ J.val, f j) ^ (e + 1) •
      (((koszulCechHomObjIso A r f M e).inv ≫
        (koszulCechCocone A r f F).ι.app e ≫
        eqToHom (koszulCechCocone_exists A r f F).choose_spec.1 ≫
        (principalCechObjIso r f F).hom).f n) w J = _ at heq
    rw [hzero] at heq
    change (∏ j ∈ J.val, f j) ^ (e + 1) •
      (0 : (affineOpenSections A (principalCechIntersection r f J.val)).obj
        (F.X (n + 1 - (J.val.card : ℤ)))) = _ at heq
    rw [smul_zero] at heq
    have hres := (smul_eq_zero_iff_eq _).mp heq.symm
    exact affine_section_torsion A (F.X _) (hF _) (∏ j ∈ J.val, f j) _ hres
  choose k hk using ht
  obtain ⟨K, hK⟩ := Finite.exists_le k
  have hcoord : ∀ (J : Finset (Fin r)) (hJ : J.Nonempty),
      (∏ j ∈ J, f j) ^ ((e + K) - e) •
        (w.v (1 - (J.card : ℤ)) (n + 1 - (J.card : ℤ))
          (koszulCech_evaluation_degree r J n)) (koszulCechBasis A r f e J hJ) = 0 := by
    intro J hJ
    rw [Nat.add_sub_cancel_left, ← Nat.sub_add_cancel (hK ⟨J, hJ⟩), pow_add,
      mul_smul, hk ⟨J, hJ⟩, smul_zero]
  have hpre := koszul_transition_zero A r f M e (e + K) (Nat.le_add_right e K) n w hcoord
  refine ⟨e + K, Nat.le_add_right e K, ?_⟩
  have hmap := (koszulCechHomDiagram_exists A r f M).choose_spec.2
    e (e + K) (Nat.le_add_right e K) n w
    ((koszulCechHomDiagram_exists A r f M).choose_spec.1 e)
    ((koszulCechHomDiagram_exists A r f M).choose_spec.1 (e + K))
  rw [hpre] at hmap
  change ((koszulCechHomObjIso A r f M (e + K)).hom.f n)
    (((D.map (homOfLE (Nat.le_add_right e K))).f n)
      (((koszulCechHomObjIso A r f M e).inv.f n) w)) = 0 at hmap
  rw [hw] at hmap
  exact (ConcreteCategory.bijective_of_isIso
    ((koszulCechHomObjIso A r f M (e + K)).hom.f n)).injective
      (by simpa only [map_zero] using hmap)

end AlgebraicGeometry
