import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceStatement
import Langlands.BushnellKutzko.SimpleIntertwiningProof
import Langlands.BushnellKutzko.StratumEquivalenceCritical
import Langlands.BushnellKutzko.TameCorestrictionProof
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Tame-corestriction congruence for equivalent simple strata -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

section CentralCoset

variable {K : Type uF} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {V : Type uV} [AddCommGroup V] [Module K V]

set_option maxHeartbeats 600000 in
/-- The coset part of BK93 (2.4.11), in two-sided difference form. -/
private theorem central_of_coset_intertwines (C : LatticeChain 𝒪[K] K V) (m : ℤ)
    (b : Module.End K V)
    (h : ∀ g : (Module.End K V)ˣ, ∃ p ∈ C.endFiltration m, ∃ q ∈ C.endFiltration m,
      (g : Module.End K V) * b - b * g = (g : Module.End K V) * p + q * g) :
    ∃ c : K, b - algebraMap K (Module.End K V) c ∈ C.endFiltration m := by
  classical
  let _ : Nontrivial V := C.nontrivial_space
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨r, B, hB⟩ := C.exists_basis_splits hπ
  have hproj (i : Fin r) : elementaryEnd B i i 1 ∈ C.endFiltration 0 :=
    C.elementaryEnd_diag_mem_order hπ hB i
  have hentry {y : Module.End K V} (hy : y ∈ C.endFiltration m) (i j : Fin r) :
      elementaryEnd B i j (entry B y i j) ∈ C.endFiltration m := by
    rw [← elementaryEnd_mul_mul]
    simpa using C.mul_mem_endFiltration (C.mul_mem_endFiltration (hproj i) hy) (hproj j)
  have hunit : IsUnit (π - 1) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hsub
    have hmem : π ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
    exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_one : IsUnit (1 : 𝒪[K])))
      (by simpa using sub_mem hmem hsub)
  obtain ⟨w, hw⟩ := hunit
  -- Scaling one basis vector eliminates each off-diagonal entry modulo the filtration.
  have hoff (i j : Fin r) (hij : i ≠ j) :
      elementaryEnd B i j (entry B b i j) ∈ C.endFiltration m := by
    let a (k : Fin r) := if k = i then (π : K) else 1
    have ha (k : Fin r) : IsUnit (a k) := by
      by_cases hk : k = i
      · simpa [a, hk] using (isUnit_iff_ne_zero.mpr (coe_uniformizer_ne_zero hπ))
      · simp [a, hk]
    let f := B.equiv (B.isUnitSMul ha) (Equiv.refl _)
    let g := LinearMap.GeneralLinearGroup.ofLinearEquiv f
    have hg_apply (k : Fin r) : (g : Module.End K V) (B k) = a k • B k := by
      change f (B k) = _
      simp [f, Module.Basis.equiv_apply, Module.Basis.isUnitSMul_apply]
    have hg_form : (g : Module.End K V) = 1 + ((π : K) - 1) • elementaryEnd B i i 1 := by
      apply B.ext
      intro k
      rw [hg_apply]
      by_cases hk : k = i
      · subst k
        simp only [a, ite_eq_left rfl, LinearMap.add_apply, Module.End.one_apply,
          LinearMap.smul_apply, elementaryEnd_apply_basis, one_smul, ite_true]
        symm
        calc
          _ = (1 + ((π : K) - 1)) • B i := by rw [add_smul, one_smul]
          _ = _ := by simp
      · simp [a, hk, Ne.symm hk, elementaryEnd_apply_basis]
    have hg0 : (g : Module.End K V) ∈ C.endFiltration 0 := by
      rw [hg_form]
      exact add_mem (C.order.one_mem) ((C.endFiltration 0).smul_mem (π - 1) (hproj i))
    obtain ⟨p, hp, q, hq, heq⟩ := h g
    have hgcomm : (g : Module.End K V) * b - b * g ∈ C.endFiltration m := by
      rw [heq]
      exact add_mem (by simpa using C.mul_mem_endFiltration hg0 hp)
        (by simpa using C.mul_mem_endFiltration hq hg0)
    have hgj : (g : Module.End K V) (B j) = B j := by
      rw [hg_apply]
      simp [a, Ne.symm hij]
    have hgi (v : V) : B.coord i ((g : Module.End K V) v) = (π : K) * B.coord i v := by
      rw [hg_form]
      simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
        elementaryEnd_apply, one_mul, map_add, map_smul, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      ring
    have he : entry B ((g : Module.End K V) * b - b * g) i j =
        ((π : K) - 1) * entry B b i j := by
      change B.coord i (((g : Module.End K V) * b - b * g) (B j)) = _ * B.coord i (b (B j))
      simp only [LinearMap.sub_apply, map_sub, Module.End.mul_apply, hgj, hgi]
      ring
    have hw_mem : (w : 𝒪[K]) • elementaryEnd B i j (entry B b i j) ∈ C.endFiltration m := by
      have ht := hentry hgcomm i j
      rw [he] at ht
      rw [hw, Subring.smul_def]
      change ((π : K) - 1) • elementaryEnd B i j (entry B b i j) ∈ C.endFiltration m
      simpa only [elementaryEnd, mul_smul] using ht
    simpa only [smul_smul, Units.inv_mul, one_smul] using
      (C.endFiltration m).smul_mem (↑w⁻¹ : 𝒪[K]) hw_mem
  -- A transposition compares two diagonal coefficients even if it does not preserve the chain.
  have hdiag (i j : Fin r) :
      elementaryEnd B i i (entry B b j j - entry B b i i) ∈ C.endFiltration m := by
    let e := Equiv.swap i j
    let f := B.equiv B e
    let g := LinearMap.GeneralLinearGroup.ofLinearEquiv f
    have he : e j = i := Equiv.swap_apply_right i j
    have hg (k : Fin r) : (g : Module.End K V) (B k) = B (e k) := by
      change f (B k) = _
      exact B.equiv_apply k B e
    have hg' : (g : Module.End K V) (B j) = B i := (hg j).trans (congrArg B he)
    have hcoord : (B.coord i).comp (g : Module.End K V) = B.coord j := by
      apply B.ext
      intro k
      have hk : e k = i ↔ k = j := by rw [← he, e.injective.eq_iff]
      simp only [LinearMap.comp_apply, hg, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, hk]
    have hcoord' (v : V) : B.coord i ((g : Module.End K V) v) = B.coord j v :=
      LinearMap.congr_fun hcoord v
    obtain ⟨p, hp, q, hq, heq⟩ := h g
    have hd : entry B b j j - entry B b i i = entry B p j j + entry B q i i := by
      have hc := congrArg (fun y : Module.End K V => entry B y i j) heq
      change B.coord i (((g : Module.End K V) * b - b * g) (B j)) =
        B.coord i (((g : Module.End K V) * p + q * g) (B j)) at hc
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add,
        Module.End.mul_apply, hg', hcoord', entry, Module.Basis.coord_apply] using hc
    have hp' : elementaryEnd B i i (entry B p j j) ∈ C.endFiltration m := by
      by_cases hz : entry B p j j = 0
      · simp [hz, elementaryEnd_zero]
      have h' := (C.elementaryEnd_mem_iff hπ hB j j hz m).mp (hentry hp j j)
      exact (C.elementaryEnd_mem_iff hπ hB i i hz m).mpr (by omega)
    rw [hd]
    simpa only [elementaryEnd, add_smul] using add_mem hp' (hentry hq i i)
  let i₀ := Classical.choice B.index_nonempty
  refine ⟨entry B b i₀ i₀, ?_⟩
  rw [← sum_elementaryEnd_entry B (b - algebraMap K (Module.End K V) (entry B b i₀ i₀))]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have hsub : entry B (b - algebraMap K (Module.End K V) (entry B b i₀ i₀)) i j =
      entry B b i j - if j = i then entry B b i₀ i₀ else 0 := by
    simp [entry, Module.algebraMap_end_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hsub]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    simpa only [elementaryEnd, ← neg_smul, neg_sub] using neg_mem (hdiag i i₀)
  · rw [ite_eq_right (Ne.symm hij), sub_zero]
    exact hoff i j hij

end CentralCoset

section Intertwining

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV}
  [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

private theorem neighborhood_bounds (T : Stratum 𝒪[F] F V) (hT : T.IsSimple)
    (w : Aˣ) (hw : w ∈ T.simpleIntertwiningNeighborhood) :
    (w : A) - 1 ∈ T.chain.endFiltration 1 ∧
      (↑w⁻¹ : A) - 1 ∈ T.chain.endFiltration 1 ∧
      adjointMap F T.b (w : A) ∈ T.chain.endFiltration (-T.r) := by
  rcases hw with ⟨_, rfl⟩ | ⟨k, hk, hw⟩
  · simp [StratumEquivalence.adjointMap_apply]
  have hkr : k < -T.r := WithBot.coe_lt_coe.mp (hk ▸ hT.2)
  let d := -(T.r + k)
  have hdk : d + k = -T.r := by dsimp [d]; omega
  have hprod : centralizerLattice T.chain T.b d * adjointLattice T.chain T.b k ≤
      T.chain.endFiltration d ⊓ (T.chain.endFiltration (-T.r)).comap (adjointMap 𝒪[F] T.b) := by
    rw [Submodule.mul_le]
    intro p hp q hq
    change p ∈ T.chain.endFiltration d ∧ T.b * p - p * T.b = 0 at hp
    change q ∈ T.chain.endFiltration 0 ∧ T.b * q - q * T.b ∈ T.chain.endFiltration k at hq
    change p * q ∈ T.chain.endFiltration d ∧ T.b * (p * q) - (p * q) * T.b ∈
      T.chain.endFiltration (-T.r)
    refine ⟨by simpa using T.chain.mul_mem_endFiltration hp.1 hq.1, ?_⟩
    rw [show T.b * (p * q) - (p * q) * T.b =
      (T.b * p - p * T.b) * q + p * (T.b * q - q * T.b) by noncomm_ring,
      hp.2, zero_mul, zero_add]
    simpa only [hdk] using T.chain.mul_mem_endFiltration hp.1 hq.2
  obtain ⟨hwf, hwc⟩ := hprod hw
  have hw₁ : (w : A) - 1 ∈ T.chain.endFiltration 1 :=
    T.chain.endFiltration_antitone (by dsimp [d]; omega) hwf
  obtain ⟨g, hg, hgw⟩ := T.chain.exists_mem_unitFiltration (n := 1) le_rfl hw₁
  have heq : g = w := Units.ext (by rw [hgw, add_sub_cancel])
  subst g
  refine ⟨hw₁, (T.chain.mem_unitFiltration.mp ((T.chain.unitFiltration 1).inv_mem hg)).2.2, ?_⟩
  change adjointMap F T.b ((w : A) - 1) ∈ T.chain.endFiltration (-T.r) at hwc
  simpa [map_sub, StratumEquivalence.adjointMap_apply] using hwc

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]
  {E : Type*} [Field E] [ValuativeRel E] [Algebra F E] [Module E V] [IsScalarTower F E V]

local notation "B" => Module.End E V

/-- The forward intertwining calculation for the derived coset. -/
private theorem corestriction_coset_intertwines (S T : Stratum 𝒪[F] F V)
    (hT : T.IsSimple) (hST : S.Equivalent T) (β : E) (hβ : subfieldEmbedding F E V β = S.b)
    (s : TameCorestriction 𝒪[F] F E V) (C : LatticeChain 𝒪[E] E V)
    (hmap : ∀ {z : A}, z ∈ T.chain.endFiltration (1 - T.r) → s z ∈ C.endFiltration (1 - T.r))
    (x : Bˣ) : ∃ p ∈ C.endFiltration (1 - T.r), ∃ q ∈ C.endFiltration (1 - T.r),
      (x : B) * s (S.b - T.b) - s (S.b - T.b) * x = (x : B) * p + q * x := by
  let restrict : B →* A :=
    { toFun := fun z => z.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := Units.map restrict x
  have hg : (g : A) = (x : B).restrictScalars F := rfl
  have hga : S.b * (g : A) = (g : A) * S.b := by
    rw [← hβ, subfieldEmbedding_eq_restrictScalars, hg]
    apply LinearMap.ext
    intro v
    exact ((x : B).map_smul β v).symm
  have hcoset : S.b ∈ T.coset := StratumEquivalence.sub_mem_of_equivalent hST
  have hgI : g ∈ T.formalSelfIntertwining := by
    refine ⟨S.b, hcoset, ?_⟩
    rw [mul_assoc, hga, ← mul_assoc, Units.inv_mul, one_mul]
    exact hcoset
  rw [simpleIntertwining F V T hT] at hgI
  obtain ⟨z, hz, v, hv, hgv⟩ := Set.mem_mul.mp hgI
  obtain ⟨u, hu, y, hy, hzy⟩ := Set.mem_mul.mp hz
  have hfactor : (g : A) = (u : A) * (y : A) * (v : A) := by
    rw [← hgv, ← hzy, Units.val_mul, Units.val_mul]
  have hleft : (↑u⁻¹ : A) * (g : A) = (y : A) * (v : A) := by
    rw [hfactor, ← mul_assoc (↑u⁻¹ : A), ← mul_assoc (↑u⁻¹ : A), Units.inv_mul, one_mul]
  have hright : (g : A) * (↑v⁻¹ : A) = (u : A) * (y : A) := by
    rw [hfactor, mul_assoc ((u : A) * (y : A)), Units.mul_inv, mul_one]
  have had_mul (b l r : A) : adjointMap F b (l * r) =
      adjointMap F b l * r + l * adjointMap F b r := by
    simp only [StratumEquivalence.adjointMap_apply]
    noncomm_ring
  have hy₀ : adjointMap F T.b (y : A) = 0 := sub_eq_zero.mpr hy
  let L := adjointMap F T.b (u : A) * (↑u⁻¹ : A)
  let R := (↑v⁻¹ : A) * adjointMap F T.b (v : A)
  have hcomm : adjointMap F T.b (g : A) = L * (g : A) + (g : A) * R := by
    calc
      _ = adjointMap F T.b (u : A) * ((y : A) * (v : A)) +
          ((u : A) * (y : A)) * adjointMap F T.b (v : A) := by
        rw [hfactor, had_mul, had_mul, hy₀, mul_zero, add_zero, mul_assoc]
      _ = _ := by
        dsimp only [L, R]
        rw [mul_assoc (adjointMap F T.b (u : A)), hleft, ← mul_assoc (g : A), hright]
  have hdiff (w : Aˣ) (hw : (w : A) - 1 ∈ T.chain.endFiltration 1) :
      adjointMap F T.b (w : A) - adjointMap F S.b (w : A) ∈ T.chain.endFiltration (1 - T.r) := by
    have hsub : T.b - S.b ∈ T.chain.endFiltration (-T.r) :=
      by simpa only [neg_sub] using neg_mem (StratumEquivalence.sub_mem_of_equivalent hST)
    rw [show adjointMap F T.b (w : A) - adjointMap F S.b (w : A) =
      (T.b - S.b) * ((w : A) - 1) - ((w : A) - 1) * (T.b - S.b) by
        simp only [StratumEquivalence.adjointMap_apply]; noncomm_ring]
    exact sub_mem (by simpa only [show -T.r + 1 = 1 - T.r by omega] using
        T.chain.mul_mem_endFiltration hsub hw)
      (T.chain.mul_mem_endFiltration hw hsub)
  have hmap_sub (z : A) (w : Aˣ)
      (hz : z - adjointMap F S.b (w : A) ∈ T.chain.endFiltration (1 - T.r)) :
      s z ∈ C.endFiltration (1 - T.r) := by
    have hm := hmap hz
    change s.toLinearMap (z - adjointMap F S.b (w : A)) ∈ C.endFiltration (1 - T.r) at hm
    simpa only [map_sub, TameCorestriction.toLinearMap_apply, ← hβ, s.adjointMap_eq_zero,
      sub_zero] using hm
  obtain ⟨hu₁, hui, hua⟩ := neighborhood_bounds T hT u hu
  obtain ⟨hv₁, hvi, hva⟩ := neighborhood_bounds T hT v hv
  have hL : s L ∈ C.endFiltration (1 - T.r) := by
    apply hmap_sub L u
    rw [show L - adjointMap F S.b (u : A) =
      (adjointMap F T.b (u : A) - adjointMap F S.b (u : A)) +
        adjointMap F T.b (u : A) * ((↑u⁻¹ : A) - 1) by dsimp only [L]; noncomm_ring]
    exact add_mem (hdiff u hu₁) (by
      simpa only [show -T.r + 1 = 1 - T.r by omega] using T.chain.mul_mem_endFiltration hua hui)
  have hR : s R ∈ C.endFiltration (1 - T.r) := by
    apply hmap_sub R v
    rw [show R - adjointMap F S.b (v : A) =
      (adjointMap F T.b (v : A) - adjointMap F S.b (v : A)) +
        ((↑v⁻¹ : A) - 1) * adjointMap F T.b (v : A) by dsimp only [R]; noncomm_ring]
    exact add_mem (hdiff v hv₁) (T.chain.mul_mem_endFiltration hvi hva)
  have hD : (g : A) * (S.b - T.b) - (S.b - T.b) * (g : A) = adjointMap F T.b (g : A) := by
    simp only [StratumEquivalence.adjointMap_apply, mul_sub, sub_mul, hga]
    noncomm_ring
  refine ⟨s R, hR, s L, hL, ?_⟩
  have hs_left (z : A) : s ((x : B).restrictScalars F * z) = (x : B) * s z :=
    s.map_mul_left (x : B) z
  have hs_right (z : A) : s (z * (x : B).restrictScalars F) = s z * (x : B) :=
    s.map_mul_right z (x : B)
  have h := congrArg s.toLinearMap (hD.trans hcomm)
  change s.toLinearMap ((g : A) * (S.b - T.b) - (S.b - T.b) * (g : A)) =
    s.toLinearMap (L * (g : A) + (g : A) * R) at h
  rw [map_sub, map_add] at h
  simp only [TameCorestriction.toLinearMap_apply, hg, hs_left, hs_right] at h
  exact h.trans (add_comm _ _)

end Intertwining

/-- Bushnell–Kutzko (2.4.1)(ii)(c), for every supplied tame corestriction. -/
theorem simpleStratumCorestrictionCongruence : SimpleStratumCorestrictionCongruenceStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ _ S T hchain _ hr hS hT hST h
  let E := elementAlgebra S.b
  let : Field E := h.toField
  intro s
  obtain ⟨_, hnormal⟩ := hS.1.1
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra S.b))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer := hnormal
  have hInt : ∀ a : E, IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E] := isIntegral_iff_mem_spectralInteger F E
  let C := S.chain.relativeLatticeChain hE hInt
  have hC (i : ℤ) (v : V) : v ∈ C.lattice i ↔ v ∈ S.chain.lattice i :=
    S.chain.mem_relativeLatticeChain hE hInt i v
  let β : E := ⟨S.b, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  have hmap {z : Module.End F V} (hz : z ∈ T.chain.endFiltration (1 - T.r)) :
      s z ∈ C.endFiltration (1 - T.r) := by
    have hi : s z ∈ s '' (S.chain.endFiltration (1 - T.r) : Set (Module.End F V)) :=
      ⟨z, hchain ▸ hz, rfl⟩
    rw [(tameCorestriction F V E).2.2 s S.chain hE (1 - T.r)] at hi
    change (s z).restrictScalars F ∈ S.chain.endFiltration (1 - T.r) at hi
    intro i v hv
    exact (hC _ _).mpr (hi i v ((hC _ _).mp hv))
  obtain ⟨δ, hδ⟩ := central_of_coset_intertwines C (1 - T.r) (s (S.b - T.b))
    (corestriction_coset_intertwines S T hT hST β rfl s C (fun {_} hz => hmap hz))
  refine ⟨δ, ?_⟩
  rw [subfieldEmbedding_eq_restrictScalars, ← hr]
  intro i v hv
  exact (hC _ _).mp (hδ i v ((hC _ _).mpr hv))

end Langlands.BushnellKutzko
