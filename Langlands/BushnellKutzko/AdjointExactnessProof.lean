import Langlands.BushnellKutzko.AdjointLatticeLifting
import Langlands.BushnellKutzko.RelativeFiltrationInversion

/-! # Adjoint lattice exactness -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE

private theorem quotientLatticeExact_of_lifts {A : Type*} [AddCommGroup A]
    (f g : A →+ A) {X D Y R Z T : AddSubgroup A}
    (hDX : D ≤ X) (hRY : R ≤ Y) (hTZ : T ≤ Z)
    (hf : Set.MapsTo f X Y) (hfR : ∀ x ∈ X, f x ∈ R ↔ x ∈ D)
    (hg : Set.MapsTo g Y Z) (hgT : Set.MapsTo g R T)
    (hgf : ∀ x, g (f x) = 0)
    (hY : ∀ z ∈ Z, ∃ y ∈ Y, g y = z) (hR : ∀ z ∈ T, ∃ y ∈ R, g y = z)
    (hX : ∀ y ∈ Y, g y = 0 → ∃ x ∈ X, f x = y) :
    QuotientLatticeExact f g X D Y R Z T := by
  refine ⟨hDX, hRY, hTZ, hf, fun x hx => (hfR x (hDX hx)).mpr hx, hg, hgT, hfR, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hY z hz
    exact ⟨y, hy, by simpa only [sub_self] using T.zero_mem⟩
  · intro y hy
    constructor
    · intro hgy
      obtain ⟨y₀, hy₀, heq⟩ := hR (g y) hgy
      obtain ⟨x, hx, hfx⟩ := hX (y - y₀) (Y.sub_mem hy (hRY hy₀))
        (by rw [map_sub, heq, sub_self])
      exact ⟨x, hx, by rwa [hfx, sub_sub_cancel]⟩
    · rintro ⟨x, _, hx⟩
      have ht : g (y - f x) ∈ T := hgT hx
      simpa only [map_sub, hgf, sub_zero] using ht

section Lattices

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (𝓛 : LatticeChain 𝒪[F] F V) (β : E)

local notation "A" => Module.End F V
local notation "B" => Module.End E V
local notation "ι" => LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)
local notation "b" => subfieldEmbedding F E V β
local notation "P" => 𝓛.endFiltration
local notation "Q" => centralizerLattice 𝓛 b
local notation "M" => mixedAdjointLattice 𝓛 b
local notation "a" => adjointMap F b

private theorem TameCorestriction.filtered_image
    (s : TameCorestriction 𝒪[F] F E V)
    (hβ : Algebra.adjoin F ({β} : Set E) = ⊤)
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) (j : ℤ) :
    Set.MapsTo (fun x => (s x).restrictScalars F) (P j) (Q j) ∧
      Set.SurjOn (fun x => (s x).restrictScalars F) (P j) (Q j) := by
  let g := (ι).comp s.toLinearMap
  change Set.MapsTo g (P j) (Q j) ∧ Set.SurjOn g (P j) (Q j)
  have hker := ker_adjointMap_eq_range_restrictScalars (V := V) β hβ
  have hgker (x : A) : a (g x) = 0 := by
    apply (LinearMap.mem_ker (f := a)).mp
    rw [hker]
    exact ⟨s x, rfl⟩
  have hmul {q : A} (hq : a q = 0) (x : A) : g (q * x) = q * g x := by
    have hq' : q ∈ (ι).range := hker ▸ LinearMap.mem_ker.mpr hq
    obtain ⟨u, rfl⟩ := hq'
    exact congrArg (fun v : B => v.restrictScalars F) (s.map_mul_left u x)
  have hgorder {x : A} (hx : x ∈ P 0) : g x ∈ P 0 := by
    rw [← 𝓛.mem_order_iff_mem_endFiltration] at hx ⊢
    have hmem : s x ∈ s.toFun '' (𝓛.order : Set A) := ⟨x, hx, rfl⟩
    rw [s.image_order 𝓛 hnormal] at hmem
    exact hmem
  constructor
  · intro x hx
    refine (mem_centralizerLattice_iff 𝓛).mpr ⟨?_, hgker x⟩
    rw [← add_zero j, ← centralizerLattice_mul_endFiltration 𝓛 b hinv j 0] at hx
    refine Submodule.mul_induction_on hx (C := fun y => g y ∈ P j) ?_ ?_
    · intro q hq y hy
      obtain ⟨hqP, hqa⟩ := (mem_centralizerLattice_iff 𝓛).mp hq
      rw [hmul hqa]
      simpa only [add_zero] using 𝓛.mul_mem_endFiltration hqP (hgorder hy)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  · intro q hq
    obtain ⟨hqP, hqa⟩ := (mem_centralizerLattice_iff 𝓛).mp hq
    have hone : (1 : B) ∈ {u : B | u.restrictScalars F ∈ 𝓛.order} := by
      change (1 : A) ∈ 𝓛.order
      exact one_mem 𝓛.order
    rw [← s.image_order 𝓛 hnormal] at hone
    obtain ⟨x₀, hx₀, heq⟩ := hone
    have hgx₀ : g x₀ = 1 := congrArg (fun u : B => u.restrictScalars F) heq
    refine ⟨q * x₀, ?_, by rw [hmul hqa, hgx₀, mul_one]⟩
    change q * x₀ ∈ P j
    simpa only [add_zero] using 𝓛.mul_mem_endFiltration hqP
      ((𝓛.mem_order_iff_mem_endFiltration).mp hx₀)

private theorem quotientLatticeExact_mixed
    (g : A →+ A) (m k r : ℤ) (hr : 0 ≤ r)
    (hg : ∀ j, Set.MapsTo g (P j) (Q j)) (hgs : ∀ j, Set.SurjOn g (P j) (Q j))
    (hga : ∀ x, g (a x) = 0)
    (ha : ∀ y ∈ P (m + k), g y = 0 → ∃ x ∈ M m k, a x = y) :
    QuotientLatticeExact (a) g (M m k).toAddSubgroup (M m (k + r)).toAddSubgroup
      (P (m + k)).toAddSubgroup (P (m + k + r)).toAddSubgroup
      (Q (m + k)).toAddSubgroup (Q (m + k + r)).toAddSubgroup := by
  have hkr : k ≤ k + r := by omega
  have hmk : P (m + k + r) ≤ P (m + k) := 𝓛.endFiltration_antitone (by omega)
  refine quotientLatticeExact_of_lifts (a).toAddMonoidHom g
    (mixedAdjointLattice_antitone 𝓛 b m hkr) hmk (inf_le_inf_right _ hmk)
    (fun x hx => ((mem_mixedAdjointLattice_iff 𝓛 b).mp hx).2) ?_
    (hg _) (hg _) hga (hgs _) (hgs _) ha
  intro x hx
  change a x ∈ P (m + k + r) ↔ x ∈ M m (k + r)
  have hxP := ((mem_mixedAdjointLattice_iff 𝓛 b).mp hx).1
  rw [mem_mixedAdjointLattice_iff, and_iff_right hxP, add_assoc]

private theorem quotientLatticeExact_mixed_unquotiented
    (g : A →+ A) (m k : ℤ)
    (hg : Set.MapsTo g (P (m + k)) (Q (m + k)))
    (hgs : Set.SurjOn g (P (m + k)) (Q (m + k))) (hga : ∀ x, g (a x) = 0)
    (ha : ∀ y ∈ P (m + k), g y = 0 → ∃ x ∈ M m k, a x = y) :
    QuotientLatticeExact (a) g (M m k).toAddSubgroup (Q m).toAddSubgroup
      (P (m + k)).toAddSubgroup ⊥ (Q (m + k)).toAddSubgroup ⊥ := by
  refine quotientLatticeExact_of_lifts (a).toAddMonoidHom g
    (centralizerLattice_le_mixedAdjointLattice 𝓛 b m k) bot_le bot_le
    (fun x hx => ((mem_mixedAdjointLattice_iff 𝓛 b).mp hx).2) ?_ hg ?_ hga hgs ?_ ha
  · intro x hx
    change a x ∈ (⊥ : AddSubgroup A) ↔ x ∈ Q m
    have hxP := ((mem_mixedAdjointLattice_iff 𝓛 b).mp hx).1
    rw [AddSubgroup.mem_bot, mem_centralizerLattice_iff, and_iff_right hxP]
  · intro x hx
    simp only [SetLike.mem_coe, AddSubgroup.mem_bot] at hx ⊢
    rw [hx, map_zero]
  · intro z hz
    rw [AddSubgroup.mem_bot] at hz
    exact ⟨0, AddSubgroup.zero_mem _, (map_zero g).trans hz.symm⟩

end Lattices

/-- Adjoint lattice intersection, the critical maximum and all four exact sequences
of BK93 (1.4.4), (1.4.7) and (1.4.10). -/
theorem adjointExactness :
    AdjointExactnessStatement.{uF, uV, uE} := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _ 𝓛 β hβ hnscalar hnormal
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hclear := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ
  have hperiod := 𝓛.maximalIdeal_smul_endFiltration_zero hϖ
  have hinv := one_mem_centralizerLattice_mul_neg 𝓛 hϖ β hnormal
  let b := subfieldEmbedding F E V β
  let C := criticalIndexSet 𝓛 b
  have hne : C.Nonempty := criticalIndexSet_nonempty_of_inverse 𝓛 β hnscalar
    hinv hϖ (fun x => hclear x 0) hperiod
  have hbdd : BddAbove C := criticalIndexSet_bddAbove 𝓛 b hϖ fun x => hclear x 0
  have hmax : IsGreatest C (sSup C) := ⟨Int.csSup_mem hne hbdd, fun _ hx => le_csSup hbdd hx⟩
  have hcrit : criticalExponent 𝓛 b = ((sSup C : ℤ) : WithBot ℤ) := by
    rw [criticalExponent, ite_eq_right (adjoin_subfieldEmbedding_ne_bot 𝓛 β hnscalar)]
  dsimp only
  refine ⟨iInf_adjointLattice 𝓛 b, hne, hbdd, ⟨sSup C, hmax, hcrit⟩, ?_⟩
  intro s m k r hk hr
  let a := adjointMap F b
  let g := (LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)).comp
    s.toLinearMap
  have hga (x : Module.End F V) : g (a x) = 0 := by
    change (s (a x)).restrictScalars F = 0
    rw [s.adjointMap_eq_zero β x]
    rfl
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hs := s.surjective_of_clearing 𝓛 hnormal hϖ0 fun x => hclear x 0
  have hg (j : ℤ) : Set.MapsTo g (𝓛.endFiltration j) (centralizerLattice 𝓛 b j) :=
    (s.filtered_image 𝓛 β hβ hnormal hinv j).1
  have hgs (j : ℤ) : Set.SurjOn g (𝓛.endFiltration j) (centralizerLattice 𝓛 b j) :=
    (s.filtered_image 𝓛 β hβ hnormal hinv j).2
  have hk₀ : sSup C ≤ k := WithBot.coe_le_coe.mp (hcrit ▸ hk)
  have hk' : ∀ j > k, j ∉ C := fun j hj hmem => (hk₀.trans_lt hj).not_ge (hmax.2 hmem)
  have ha (i : ℤ) : ∀ y ∈ 𝓛.endFiltration (i + k), g y = 0 →
      ∃ x ∈ mixedAdjointLattice 𝓛 b i k, a x = y := by
    intro y hy hgy
    apply exists_mixedAdjointLattice_lift 𝓛 b hinv hϖ hclear hk' hy
    have hsy : s.toLinearMap y = 0 := LinearMap.restrictScalars_injective F hgy
    exact (s.range_adjointMap_eq_ker β hβ hs).symm ▸ LinearMap.mem_ker.mpr hsy
  have hmixed (j : ℤ) : mixedAdjointLattice 𝓛 b m j =
      centralizerLattice 𝓛 b m * adjointLattice 𝓛 b j := by
    simpa only [add_zero, mixedAdjointLattice_zero] using
      (centralizerLattice_mul_mixedAdjointLattice 𝓛 b hinv m 0 j).symm
  have ha_eq : (adjointMap 𝒪[F] (subfieldEmbedding F E V β) : Module.End F V → Module.End F V) =
      (a : Module.End F V → Module.End F V) := funext (adjointMap_restrict_apply b)
  have hg_eq : (fun x => (s x).restrictScalars F) =
      (g.toAddMonoidHom : Module.End F V → Module.End F V) := rfl
  rw [ha_eq, hg_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mixedAdjointLattice_zero, zero_add] using
      quotientLatticeExact_mixed 𝓛 β g.toAddMonoidHom 0 k r (by omega) hg hgs hga (ha 0)
  · simpa only [mixedAdjointLattice_zero, zero_add] using
      quotientLatticeExact_mixed_unquotiented 𝓛 β g.toAddMonoidHom 0 k (hg _) (hgs _) hga (ha 0)
  · rw [← hmixed k]
    exact quotientLatticeExact_mixed_unquotiented 𝓛 β g.toAddMonoidHom m k (hg _) (hgs _) hga (ha m)
  · rw [← hmixed k, ← hmixed (k + 1)]
    exact quotientLatticeExact_mixed 𝓛 β g.toAddMonoidHom m k 1 (by omega) hg hgs hga (ha m)

end Langlands.BushnellKutzko
