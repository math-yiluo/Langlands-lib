import Langlands.Cohomology.Profinite.Cup.Connecting
import Langlands.Cohomology.Profinite.Duality.Pairing
import Langlands.GaloisCohomology.Field.CyclicCup
import Langlands.GaloisCohomology.Local.Duality.RootsOfUnity

/-!
# Cup products of characters with Kummer classes

For an open subgroup `U` of `Gal(Ksep/K)` with fixed field `E`, a character `χ : U → ℤ/n` and a
unit `a ∈ Eˣ`, the cup product of `χ` with the Kummer class `δa ∈ H¹(U, μ_n)` vanishes in
`H²(U, μ_n)` exactly when `a` is a norm from the fixed field of the kernel of `χ`
(`cupPairing_δ_unitsInvariantOpen_eq_zero_iff`). The proof compares the cup product with the cup
product of the Bockstein of `χ` (from `0 → ℤ → ℤ → ℤ/n → 0`) with `a`, whose standard cocycle
`(g, h) ↦ c_χ(g, h) • a` is a coboundary exactly when `a` is a norm
(`exists_coboundary_charCocycle_smul_iff_exists_norm` of the field layer).
-/

noncomputable section

open CategoryTheory MonoidalCategory IntermediateField

universe u

namespace Langlands.ProfiniteCohomology

open Langlands.GaloisCohomology GroupCoh

section Bockstein

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ)

abbrev intRepTriv : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)

def zmodReductionAdd : ULift.{u} ℤ →+ ULift.{u} (ZMod n) :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod n))).comp
    AddEquiv.ulift.toAddMonoidHom

def zmodReduction : intRepTriv G ⟶ zmodRep.{u} G n :=
  Rep.ofHom ⟨uliftIntLinearMap (zmodReductionAdd n), fun _ => rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem zmodReduction_hom_apply (m : ℤ) :
    (zmodReduction G n).hom (ULift.up m : intRepTriv G) = (ULift.up (m : ZMod n) : zmodRep.{u} G n) := by
  simp [zmodReduction, zmodReductionAdd]
  rfl

abbrev bockSeq : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) where
  X₁ := intRepTriv G
  X₂ := intRepTriv G
  X₃ := zmodRep.{u} G n
  f := n • 𝟙 (intRepTriv G)
  g := zmodReduction G n
  zero := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    obtain ⟨m⟩ := x
    change (zmodReduction G n).hom ((n • 𝟙 (intRepTriv G)).hom (ULift.up m)) = 0
    rw [nsmul_id_hom_apply]
    change (zmodReduction G n).hom (ULift.up (n • m) : intRepTriv G) = 0
    rw [zmodReduction_hom_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul]
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem bockSeq_shortExact (hn : n ≠ 0) : (bockSeq G n).ShortExact where
  exact := by
    refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
    obtain ⟨m⟩ := x
    have h0 : ((m : ℤ) : ZMod n) = 0 := by
      have := congrArg ULift.down ((zmodReduction_hom_apply G n m).symm.trans hx)
      exact this
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m n).1 h0
    refine ⟨(ULift.up c : intRepTriv G), ?_⟩
    change (n • 𝟙 (intRepTriv G)).hom (ULift.up c) = ULift.up m
    rw [nsmul_id_hom_apply]
    apply ULift.ext
    change n • c = m
    rw [hc, nsmul_eq_mul]
  mono_f := by
    refine (Rep.mono_iff_injective _).2 fun x y hxy => ?_
    obtain ⟨a⟩ := x
    obtain ⟨b⟩ := y
    change (n • 𝟙 (intRepTriv G)).hom (ULift.up a) = (n • 𝟙 (intRepTriv G)).hom (ULift.up b) at hxy
    rw [nsmul_id_hom_apply, nsmul_id_hom_apply] at hxy
    have h : n • a = n • b := congrArg ULift.down hxy
    rw [nsmul_eq_mul, nsmul_eq_mul] at h
    exact congrArg ULift.up (mul_left_cancel₀ (by exact_mod_cast hn) h)
  epi_g := by
    have : NeZero n := ⟨hn⟩
    refine (Rep.epi_iff_surjective _).2 fun y => ?_
    obtain ⟨z⟩ := y
    refine ⟨(ULift.up (z.val : ℤ) : intRepTriv G), ?_⟩
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((z.val : ℕ) : ℤ) : ZMod n) = z
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def intMulPairing (A : Rep.{u} (ULift.{u} ℤ) G) : intRepTriv G ⊗ A ⟶ A :=
  pairingHom (LinearMap.lsmul (ULift.{u} ℤ) A) fun σ m a => ((A.ρ σ).map_smul m a).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem intMulPairing_tmul (A : Rep.{u} (ULift.{u} ℤ) G) (m : ℤ) (a : A) :
    (intMulPairing G A).hom ((ULift.up m : intRepTriv G) ⊗ₜ[ULift.{u} ℤ] a :
      (intRepTriv G ⊗ A : Rep _ _)) = m • a := by
  have h : (ULift.up m : ULift.{u} ℤ) = ((m : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  refine (pairingHom_tmul (A := intRepTriv G) (B := A) (LinearMap.lsmul (ULift.{u} ℤ) A) _ _ _).trans ?_
  exact (LinearMap.lsmul_apply _ _).trans (by rw [h]; exact Int.cast_smul_eq_zsmul (ULift.{u} ℤ) m a)

variable {G n}

def zmodCocycleHom (z : cocycles (zmodRep.{u} G n) 1) : G → ZMod n :=
  fun g => (cochainOf _ (cocycleι _ 1 z) ![g]).down

theorem zmodCocycleHom_mul (z : cocycles (zmodRep.{u} G n) 1) (g h : G) :
    zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
  congrArg ULift.down
    (cochainOf_cocycleι_one_mul_of_trivial (zmodRep.{u} G n) (fun _ _ => rfl) z g h)

theorem isLocallyConstant_zmodCocycleHom (z : cocycles (zmodRep.{u} G n) 1) :
    IsLocallyConstant (zmodCocycleHom z) :=
  ((isLocallyConstant_cochainOf (cocycleι _ 1 z)).comp_continuous
    (continuous_pi fun i => by fin_cases i; exact continuous_id)).comp ULift.down

def bockInt (χ : G → ZMod n) (g h : G) : ℤ :=
  (((χ g).val + (χ h).val) / n : ℕ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem natCast_mul_bockInt [NeZero n] (χ : G → ZMod n)
    (hχ : ∀ g h : G, χ (g * h) = χ g + χ h) (g h : G) :
    (n : ℤ) * bockInt χ g h = (χ g).val + (χ h).val - (χ (g * h)).val := by
  rw [hχ, ZMod.val_add, bockInt]
  have e := Nat.div_add_mod ((χ g).val + (χ h).val) n
  generalize ((χ g).val + (χ h).val) / n = q at e ⊢
  generalize ((χ g).val + (χ h).val) % n = r at e ⊢
  have e' : ((n * q + r : ℕ) : ℤ) = (((χ g).val + (χ h).val : ℕ) : ℤ) := by rw [e]
  push_cast at e'
  linarith

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem charCocycle_eq_bockInt [NeZero n] (χ : G → ZMod n) (ψ : Additive G →+ AddCircle (1 : ℚ))
    (hψ : ∀ g : G, ψ (Additive.ofMul g) = QZ.toAddCircle (zmodToQZ n (χ g))) (g h : G) :
    charCocycle ψ (g, h) = bockInt χ g h := by
  have hn : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : ∀ x : G, reprIco (ψ (Additive.ofMul x)) = ((χ x).val : ℚ) / n := by
    intro x
    have hz : zmodToQZ n (χ x) = QZ.mk ((((χ x).val : ℤ) : ℚ) / n) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (χ x), ← Int.cast_natCast]
      exact zmodToQZ_intCast _
    rw [hψ, hz]
    have hmem : (((((χ x).val : ℕ) : ℤ) : ℚ) / n) ∈ Set.Ico (0 : ℚ) 1 := by
      constructor
      · positivity
      · rw [div_lt_one hn]
        exact_mod_cast ZMod.val_lt (χ x)
    rw [QZ.mk, AddEquiv.apply_symm_apply, reprIco_coe hmem]
    push_cast
    rfl
  unfold charCocycle bockInt
  simp only
  rw [hr, hr, ← add_div]
  have e := Nat.div_add_mod ((χ g).val + (χ h).val) n
  have hlt := Nat.mod_lt ((χ g).val + (χ h).val) (Nat.pos_of_ne_zero (NeZero.ne n))
  generalize ((χ g).val + (χ h).val) / n = q at e ⊢
  generalize ((χ g).val + (χ h).val) % n = r at e hlt
  have e' : ((χ g).val : ℚ) + (χ h).val = n * q + r := by
    have := congrArg (fun t : ℕ => (t : ℚ)) e
    push_cast at this
    linarith
  rw [Int.floor_eq_iff, e']
  push_cast
  constructor
  · rw [le_div_iff₀ hn]
    have : (0 : ℚ) ≤ r := by positivity
    nlinarith
  · rw [div_lt_iff₀ hn]
    have : (r : ℚ) < n := by exact_mod_cast hlt
    nlinarith

theorem exists_cocycle_cupPairing_δ_bockSeq (hn : n ≠ 0) (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep A] (z : cocycles (zmodRep.{u} G n) 1) (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w =
        cupPairing (intMulPairing G A) (show 2 + 0 = 2 from rfl)
          ((δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z)) ((zeroIso A).inv.hom a) ∧
      ∀ g h : G, cochainOf A (cocycleι A 2 w) ![g, h] = bockInt (zmodCocycleHom z) g h • (a : A) := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{u} ℤ))
  let x₂ : (cochains (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (coeffCochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  have hx₁v : ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
      bockInt (zmodCocycleHom z) g h := by
    intro g h
    have e : cochainOf (bockSeq G n).X₂ ((coeffCochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
        cochainOf (bockSeq G n).X₂ (((cochains (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
      congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
    rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
    have e2 := congrArg ULift.down e
    change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
      ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
        ((zmodCocycleHom z g).val : ℤ) at e2
    have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
    rw [nsmul_eq_mul] at e2
    apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
    rw [e2, e3]
    ring
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv A a
  refine ⟨HomologicalComplex.cyclesMap (coeffCochainsMap (intMulPairing G A)) 2
    (cupCocycles (show 2 + 0 = 2 from rfl) x₁ z0), ?_, fun g h => ?_⟩
  · rw [← hz0, hδ, cupPairing_cohomologyπ]
  · rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hz0c]
    have e1 : cochainOf _ (cocycleι _ 2 x₁) (fun i : Fin 2 => (![g, h] : Fin 2 → G) ⟨i, by omega⟩) =
        (ULift.up (bockInt (zmodCocycleHom z) g h) : intRepTriv G) := by
      rw [← hx₁v]
    have e2 : A.ρ (Fin.partialProd (![g, h] : Fin 2 → G) ⟨2, by omega⟩) (a : A) = a :=
      (Representation.mem_invariants _ _).1 a.2 _
    rw [e1, e2]
    exact intMulPairing_tmul G A _ a

end Bockstein

end Langlands.ProfiniteCohomology

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology ClassFieldTheory.Local GroupCoh

section Pairings

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [IsSepClosure K Ksep] in

theorem bockSeq_kummerSequenceRes_compat₁₂ (W : Subgroup Gal(Ksep/K)) :
    ((bockSeq W n).f ⊗ₘ 𝟙 (kummerSequenceRes (K := K) (Ksep := Ksep) n W).X₂) ≫
        intMulPairing W (kummerSequenceRes (K := K) (Ksep := Ksep) n W).X₂ =
      (𝟙 (bockSeq W n).X₁ ⊗ₘ (kummerSequenceRes (K := K) (Ksep := Ksep) n W).g) ≫
        intMulPairing W (kummerSequenceRes (K := K) (Ksep := Ksep) n W).X₃ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul m a =>
    obtain ⟨m⟩ := m
    show (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep))).hom
        ((n • 𝟙 (intRepTriv W)).hom (ULift.up m) ⊗ₜ[ULift.{u} ℤ] a) =
      (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep))).hom
        (ULift.up m ⊗ₜ[ULift.{u} ℤ] (kummerSequenceRes (K := K) (Ksep := Ksep) n W).g.hom a)
    have hnm : (n • 𝟙 (intRepTriv W)).hom (ULift.up m) = (ULift.up ((n : ℤ) * m) : intRepTriv W) := by
      rw [nsmul_id_hom_apply]
      ext
      simp
    rw [hnm, kummerSequenceRes_g_hom_apply, intMulPairing_tmul, intMulPairing_tmul, mul_zsmul',
      natCast_zsmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bockSeq_kummerSequenceRes_compat₂₃ (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (𝟙 (bockSeq W n).X₂ ⊗ₘ (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f) ≫
        intMulPairing W (kummerSequenceRes (K := K) (Ksep := Ksep) n W).X₂ =
      ((bockSeq W n).g ⊗ₘ 𝟙 (kummerSequenceRes (K := K) (Ksep := Ksep) n W).X₁) ≫
        (zmodMulPairing n (Rep.res W.subtype (rootsOfUnityModule K Ksep n))
          (nsmul_res_rootsOfUnityModule_eq_zero hn W) ≫ (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul m d =>
    obtain ⟨m⟩ := m
    show (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep))).hom
        (ULift.up m ⊗ₜ[ULift.{u} ℤ] (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f.hom d) =
      (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f.hom
        ((zmodMulPairing n (Rep.res W.subtype (rootsOfUnityModule K Ksep n))
          (nsmul_res_rootsOfUnityModule_eq_zero hn W)).hom
          ((zmodReduction W n).hom (ULift.up m) ⊗ₜ[ULift.{u} ℤ] d))
    rw [zmodReduction_hom_apply, zmodMulPairing_tmul, intMulPairing_tmul,
      zsmul_eq_zsmul_of_intCast_eq (nsmul_res_rootsOfUnityModule_eq_zero hn W)
        (ZMod.intCast_zmod_cast (m : ZMod n)) d, map_zsmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Pairings

section Key

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

theorem ne_zero_of_natCast_ne_zero' (hn : (n : K) ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact hn Nat.cast_zero

theorem cohomologyMap_cupPairing_zmodMul_δ (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{u} W n) 1)
    (y : cohomology (Rep.res W.subtype (unitsModule K Ksep)) 0) :
    (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f 2).hom
        (cupPairing (zmodMulPairing n (Rep.res W.subtype (rootsOfUnityModule K Ksep n))
          (nsmul_res_rootsOfUnityModule_eq_zero hn W)) (show 1 + 1 = 2 from rfl) x
          ((δ (kummerSequenceRes_shortExact n W hn) 0 1 rfl).hom y)) =
      cupPairing (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep))) (show 2 + 0 = 2 from rfl)
        ((δ (bockSeq_shortExact W n (ne_zero_of_natCast_ne_zero' hn)) 1 2 rfl).hom x) y := by
  have h := cupPairing_δ_eq (S := bockSeq W n) (T := kummerSequenceRes (K := K) (Ksep := Ksep) n W)
    (p := 1) (p' := 2) (q := 0) (q' := 1) (n := 2)
    (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep)))
    (intMulPairing W (Rep.res W.subtype (unitsModule K Ksep)))
    (zmodMulPairing n (Rep.res W.subtype (rootsOfUnityModule K Ksep n))
      (nsmul_res_rootsOfUnityModule_eq_zero hn W) ≫ (kummerSequenceRes (K := K) (Ksep := Ksep) n W).f)
    (bockSeq_kummerSequenceRes_compat₁₂ W) (bockSeq_kummerSequenceRes_compat₂₃ hn W)
    (bockSeq_shortExact W n (ne_zero_of_natCast_ne_zero' hn)) (kummerSequenceRes_shortExact n W hn)
    rfl rfl rfl rfl x y
  have h1 : ((-1 : ULift.{u} ℤ) ^ (1 + 1)) = 1 := by norm_num
  rw [h1] at h
  exact (cohomologyMap_cupPairing _ _ _ _ _).trans (h.trans (@one_smul _ _ _
    (cohomology (Rep.res W.subtype (unitsModule K Ksep)) 2).isModule.toMulAction _)).symm

end Key

section Units

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def unitsInvariantOpen (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) :
    (Rep.res W.subtype (unitsModule K Ksep)).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a),
    (Representation.mem_invariants _ _).2 fun σ =>
      congrArg Additive.ofMul (Units.ext ((mem_fixedField_iff _ _).1 (a : fixedField W).2 σ σ.2))⟩

omit [IsSepClosure K Ksep] in
theorem coe_unitsInvariantOpen (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) :
    ((unitsInvariantOpen W a : Rep.res W.subtype (unitsModule K Ksep)) : Additive Ksepˣ) =
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) :=
  rfl

omit [IsSepClosure K Ksep] in

theorem exists_unitsInvariantOpen_eq (W : Subgroup Gal(Ksep/K))
    (v : (Rep.res W.subtype (unitsModule K Ksep)).ρ.invariants) :
    ∃ a : (fixedField W)ˣ, unitsInvariantOpen W a = v := by
  have ha : ((Additive.toMul (v : Rep.res W.subtype (unitsModule K Ksep)) : Ksepˣ) : Ksep) ∈
      fixedField W :=
    (mem_fixedField_iff _ _).2 fun σ hσ =>
      congrArg (fun y : Additive Ksepˣ => ((Additive.toMul y : Ksepˣ) : Ksep))
        ((Representation.mem_invariants _ _).1 v.2 ⟨σ, hσ⟩)
  refine ⟨Units.mk0 ⟨_, ha⟩ fun h =>
    (Additive.toMul (v : Rep.res W.subtype (unitsModule K Ksep)) : Ksepˣ).ne_zero
      (congrArg Subtype.val h), Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))⟩

omit [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_pow (W : Subgroup Gal(Ksep/K)) (a : (fixedField W)ˣ) (m : ℕ) :
    unitsInvariantOpen W (a ^ m) = m • unitsInvariantOpen W a := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a ^ m)) =
    m • Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a)
  rw [map_pow, ofMul_pow]

theorem δ_unitsInvariantOpen_pow_eq_zero {n : ℕ} (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (b : (fixedField W)ˣ) :
    (δ (kummerSequenceRes_shortExact (Ksep := Ksep) n W hn) 0 1 rfl).hom
      ((zeroIso _).inv.hom (unitsInvariantOpen W (b ^ n))) = 0 := by
  refine (δ_zeroIso_inv_eq_zero_iff (kummerSequenceRes_shortExact (Ksep := Ksep) n W hn) _).2
    ⟨unitsInvariantOpen W b, Subtype.ext ?_⟩
  rw [unitsInvariantOpen_pow]
  exact kummerSequenceRes_g_hom_apply n W _

end Units

section Transport

theorem exists_coboundary_iff_of_mulEquiv {Γ Γ' X : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] [AddCommGroup X] (e : Γ' ≃* Γ) (he : Continuous e) (he' : Continuous e.symm)
    (ρ : Γ → X → X) (ρ' : Γ' → X → X) (hρ : ∀ g x, ρ (e g) x = ρ' g x)
    (c : Γ → Γ → X) (c' : Γ' → Γ' → X) (hc : ∀ g h, c (e g) (e h) = c' g h) :
    (∃ f : Γ → X, IsLocallyConstant f ∧ ∀ g h, c g h = ρ g (f h) - f (g * h) + f g) ↔
      ∃ f : Γ' → X, IsLocallyConstant f ∧ ∀ g h, c' g h = ρ' g (f h) - f (g * h) + f g := by
  constructor
  · rintro ⟨f, hf, hfc⟩
    refine ⟨fun g => f (e g), hf.comp_continuous he, fun g h => ?_⟩
    show c' g h = ρ' g (f (e h)) - f (e (g * h)) + f (e g)
    rw [← hc, hfc, map_mul, hρ]
  · rintro ⟨f, hf, hfc⟩
    refine ⟨fun g => f (e.symm g), hf.comp_continuous he', fun g h => ?_⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := e.surjective h
    show c (e g) (e h) = ρ (e g) (f (e.symm (e h))) - f (e.symm (e g * e h)) + f (e.symm (e g))
    rw [hc, hfc, ← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hρ]

end Transport


namespace Local

section Local

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem exists_δ_unitsInvariantOpen_eq (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 1) :
    ∃ a : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ,
      (δ (kummerSequenceRes_shortExact n (U : Subgroup Gal(Ksep/K)) hn) 0 1 rfl).hom
        ((zeroIso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)) = y := by
  obtain ⟨v, hv⟩ := exists_δ_zeroIso_inv_eq (kummerSequenceRes_shortExact n (U : Subgroup Gal(Ksep/K)) hn)
    (subsingleton_cohomology_one_res_unitsModule K Ksep U) y
  obtain ⟨a, rfl⟩ := exists_unitsInvariantOpen_eq (U : Subgroup Gal(Ksep/K)) v
  exact ⟨a, hv⟩

variable (n) in

def openChar (U : OpenSubgroup Gal(Ksep/K)) (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1) :
    Additive Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →ₜ+ QZ where
  toFun σ := zmodToQZ n (zmodCocycleHom z (galFixedFieldEquivOpen U (Additive.toMul σ)))
  map_zero' := by
    have h0 : zmodCocycleHom z 1 = 0 := by
      have h := zmodCocycleHom_mul z 1 1
      rw [mul_one] at h
      simpa using h
    simp only [toMul_zero, map_one, h0, map_zero]
  map_add' σ τ := by
    simp only [toMul_add, map_mul, zmodCocycleHom_mul, map_add]
  continuous_toFun :=
    (((isLocallyConstant_zmodCocycleHom z).comp_continuous
      ((continuous_galFixedFieldEquivOpen U).comp continuous_toMul)).comp (zmodToQZ n)).continuous

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem openChar_apply (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Additive Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    openChar n U z σ = zmodToQZ n (zmodCocycleHom z (galFixedFieldEquivOpen U (Additive.toMul σ))) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem res_unitsModule_ρ_galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K))
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) (x : Additive Ksepˣ) :
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)).ρ (galFixedFieldEquivOpen U σ) x =
      (unitsModuleZ (fixedField (U : Subgroup Gal(Ksep/K))) Ksep).ρ σ x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem cupPairing_δ_unitsInvariantOpen_eq_zero_iff (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (a : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ) :
    cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n))
        (nsmul_res_rootsOfUnityModule_eq_zero hn _)) (show 1 + 1 = 2 from rfl) (cohomologyπ _ 1 z)
        ((δ (kummerSequenceRes_shortExact n (U : Subgroup Gal(Ksep/K)) hn) 0 1 rfl).hom
          ((zeroIso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a))) = 0 ↔
      ∃ y : fixedField (charKer (charAdd (openChar n U z))),
        Algebra.norm (fixedField (U : Subgroup Gal(Ksep/K))) y =
          (a : fixedField (U : Subgroup Gal(Ksep/K))) := by
  have hn0 := ne_zero_of_natCast_ne_zero' hn
  have : NeZero n := ⟨hn0⟩
  rw [← exists_coboundary_charCocycle_smul_iff_exists_norm (openChar n U z) a,
    ← (injective_coeffMap_kummerSequenceRes_f_two hn U).eq_iff, map_zero,
    cohomologyMap_cupPairing_zmodMul_δ hn]
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupPairing_δ_bockSeq hn0
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) z
    (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)
  rw [← hw, cohomologyπ_two_eq_zero_iff]
  refine exists_coboundary_iff_of_mulEquiv (galFixedFieldEquivOpen U)
    (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) _ _
    (res_unitsModule_ρ_galFixedFieldEquivOpen U) _ _ fun g h => ?_
  rw [hwc, charCocycle_eq_bockInt (fun σ => zmodCocycleHom z (galFixedFieldEquivOpen U σ))
    (charAdd (openChar n U z)) (fun σ => rfl)]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem zmodCocycleHom_eq_zero_of_charKer_eq_top (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : charKer (charAdd (openChar n U z)) = ⊤) (g : (U : Subgroup Gal(Ksep/K))) :
    zmodCocycleHom z g = 0 := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  obtain ⟨σ, rfl⟩ := (galFixedFieldEquivOpen U).surjective g
  have hσ : σ ∈ charKer (charAdd (openChar n U z)) := h ▸ Subgroup.mem_top σ
  rw [mem_charKer, charAdd_apply, openChar_apply, AddEquiv.map_eq_zero_iff] at hσ
  exact zmodToQZ_injective (hσ.trans (map_zero _).symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem exists_cocycle_charKer_eq (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (ψ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →* Multiplicative (ZMod n))
    (hψ : IsOpen (ψ.ker : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))))) :
    ∃ z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1,
      charKer (charAdd (openChar n U z)) = ψ.ker := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  have hlc : IsLocallyConstant fun σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) => ψ σ := by
    intro s
    refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set _), ?_,
      hψ.preimage (continuous_const_mul x⁻¹), by simp⟩
    intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hy
    have hxy : ψ y = ψ x := (inv_mul_eq_one.1 hy).symm
    simpa [Set.mem_preimage, hxy] using hx
  let f : ↥(U : Subgroup Gal(Ksep/K)) → zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n :=
    fun g => ULift.up (Multiplicative.toAdd (ψ ((galFixedFieldEquivOpen U).symm g)))
  have hf : IsLocallyConstant f :=
    ((hlc.comp_continuous (continuous_galFixedFieldEquivOpen_symm U)).comp
      (fun m => (ULift.up (Multiplicative.toAdd m) : zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n)))
  have hmul : ∀ g h, f (g * h) = f g + f h := fun g h => by
    apply ULift.ext
    simp [f, toAdd_mul]
  refine ⟨cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul, ?_⟩
  have hz : ∀ g, zmodCocycleHom (cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul) g =
      Multiplicative.toAdd (ψ ((galFixedFieldEquivOpen U).symm g)) := fun g =>
    congrArg ULift.down (cochainOf_cocyclesOneOfHom _ (fun _ _ => rfl) f hf hmul ![g])
  ext σ
  rw [mem_charKer, charAdd_apply, openChar_apply, AddEquiv.map_eq_zero_iff, toMul_ofMul, hz,
    MulEquiv.symm_apply_apply, MonoidHom.mem_ker, ← toAdd_eq_zero]
  exact ⟨fun h => zmodToQZ_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

end Local

end Local

end Langlands.GaloisCohomology
