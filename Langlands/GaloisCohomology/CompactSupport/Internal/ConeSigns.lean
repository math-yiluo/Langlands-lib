import Langlands.GaloisCohomology.CompactSupport.Internal.LeibnizPairing

/-!
# Leibniz pairings on mapping cocones and their signs (internal)

Given Leibniz pairings on the two components of mapping cocones, compatible with the maps whose
cocones are taken, this file builds the induced Leibniz pairing on the cocones, with the cocone in
the left factor (`LeibnizPairing.coconeLeft`) or in the right factor (`coconeRight`); the shifted
component carries the sign `(-1)ʳ` in the right case. On classes coming from the connecting map
of the cocone, the left pairing is the connecting map of the pairing of the local terms
(`coconeLeft_homology_homologyδ`). The left and right pairings agree in homology on a class of one
cocone paired with the image of a class of the other (`coconeLeft_homology_eq_coconeRight_homology`):
their difference on products of cycles is a boundary, given by an explicit homotopy (`shiftBoth`).
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from CompactSupportCohomology/ConePairing.lean
section ConePairing

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Left

variable {L N' L' : CochainComplex (ModuleCat.{u} k) ℕ} (μL : LeibnizPairing L N' L')

/-- A pairing `L[-1] × N' → P'[-1]` induced by a pairing `L × N' → P'` (with the shift's degree
conventions). -/
noncomputable def shiftLeft : ∀ (r s n : ℕ), r + s = n →
    shiftNegOneX L r →ₗ[k] N'.X s →ₗ[k] shiftNegOneX L' n
  | 0, _, _, _ => 0
  | _ + 1, _, 0, _ => 0
  | r + 1, s, n + 1, _ => μL.μ (show r + s = n by omega)

theorem shiftLeft_succ {r s n : ℕ} (h : r + 1 + s = n + 1) (y : L.X r) (w : N'.X s) :
    μL.shiftLeft (r + 1) s (n + 1) h (shiftNegOneSucc L r y) w =
      shiftNegOneSucc L' n (μL.μ (by omega) y w) :=
  rfl

theorem shiftLeft_leibniz {r s n : ℕ} (h : r + s = n) (y : shiftNegOneX L r) (w : N'.X s) :
    (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y w) =
      μL.shiftLeft (r + 1) s (n + 1) (by omega) ((shiftNegOneD L r).hom y) w +
        (-1 : k) ^ r • μL.shiftLeft r (s + 1) (n + 1) (by omega) y ((N'.d s (s + 1)).hom w) := by
  cases r with
  | zero =>
    have e1 : μL.shiftLeft 0 s n h y w = 0 := rfl
    have e2 : (shiftNegOneD L 0).hom y = 0 := rfl
    have e3 : μL.shiftLeft 0 (s + 1) (n + 1) (by omega) y ((N'.d s (s + 1)).hom w) = 0 := rfl
    rw [e1, e2, e3, map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  | succ r =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    revert y
    intro (y : L.X r)
    change -(L'.d m (m + 1)).hom (μL.μ (show r + s = m by omega) y w) =
      μL.μ (show r + 1 + s = m + 1 by omega) (-(L.d r (r + 1)).hom y) w +
        (-1 : k) ^ (r + 1) • μL.μ (show r + (s + 1) = m + 1 by omega) y ((N'.d s (s + 1)).hom w)
    rw [μL.leibniz, map_neg, LinearMap.neg_apply, pow_succ, mul_neg_one, neg_smul, neg_add]

variable {K K' N : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'} (ρ : N ⟶ N')
  (μK : LeibnizPairing K N K')

/-- The pairing `Cocone(f) × N → Cocone(g)` (on the left factor) built from pairings on the two
components of the cocones. -/
noncomputable def coconeLeftμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z)) : K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) = _
      rw [map_add, map_add]
      rfl))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) = _
      rw [map_smul, map_smul]
      rfl))

theorem coconeLeftμ_apply {r s n : ℕ} (h : r + s = n) (x : K.X r) (y : shiftNegOneX L r)
    (z : N.X s) :
    coconeLeftμ μL ρ μK (f := f) (f' := f') h ((x, y) : K.X r × shiftNegOneX L r) z =
      ((μK.μ h x z, μL.shiftLeft r s n h y ((ρ.f s).hom z)) : K'.X n × shiftNegOneX L' n) :=
  rfl

/-- The Leibniz pairing `Cocone(f) × N → Cocone(g)` induced by compatible pairings `K × N → Q`, `L
× N' → P'` and a map `N → N'`. -/
noncomputable def coconeLeft (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftμ μL ρ μK h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z)) =
      μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        (-1 : k) ^ r • μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z))
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, hc, shiftLeft_leibniz,
      LinearMap.map_add₂, shiftLeft_succ]
    exact (add_assoc _ _ _).symm

variable (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

end Left

/-- The image of a cycle of `L` under the connecting map of the cocone is represented by a cycle of
the form `(0, c)`. -/
theorem _root_.Langlands.GaloisCohomology.mappingCoconeNat.exists_homologyδ_homologyπ
    {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) (r : ℕ) (c : L.cycles r) :
    ∃ c' : (mappingCoconeNat f).cycles (r + 1),
      (mappingCoconeNat.homologyδ f r).hom ((L.homologyπ r).hom c) =
        ((mappingCoconeNat f).homologyπ (r + 1)).hom c' ∧
      ((mappingCoconeNat f).iCycles (r + 1)).hom c' =
        (((0 : K.X (r + 1)), shiftNegOneSucc L r ((L.iCycles r).hom c)) :
          K.X (r + 1) × shiftNegOneX L (r + 1)) := by
  let w := ((shiftNegOne L).liftCycles (L.iCycles r ≫ shiftNegOneSuccHom L r) (r + 1 + 1)
    (CochainComplex.next ℕ (r + 1)) (iCycles_shiftNegOneSuccHom_d L r)).hom c
  refine ⟨(HomologicalComplex.cyclesMap (mappingCoconeNat.inr f) (r + 1)).hom w, ?_, ?_⟩
  · change (HomologicalComplex.homologyMap (mappingCoconeNat.inr f) (r + 1)).hom
      ((shiftNegOneHomologyHom L r).hom ((L.homologyπ r).hom c)) = _
    rw [hom_apply_hom_apply_of_comp_eq (homologyπ_shiftNegOneHomologyHom L r) c]
    exact homologyMap_homologyπ_apply _ _ _
  · rw [iCycles_cyclesMap_apply,hom_apply_hom_apply_of_comp_eq ((shiftNegOne L).liftCycles_i _ _ _ _) c]
    rfl

section LeftDelta

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

/-- On classes coming from the connecting map of the cocone, the cone pairing is the connecting
map of the pairing of the local terms. -/
theorem coconeLeft_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeft μL ρ μK hc).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
      (mappingCoconeNat.homologyδ f' n).hom
        (μL.homology h ξ ((HomologicalComplex.homologyMap ρ s).hom z)) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ r ξ
  obtain ⟨w, rfl⟩ := homologyπ_hom_surjective _ s z
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f r c
  rw [homologyMap_homologyπ_apply, homology_homologyπ]
  obtain ⟨c'', hc''1, hc''2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' n
    (μL.cycles h c ((HomologicalComplex.cyclesMap ρ s).hom w))
  rw [hc'1, hc''1, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cycles, hc'2, hc''2, iCycles_cycles, iCycles_cyclesMap_apply]
  exact Prod.ext (LinearMap.map_zero₂ _ _) rfl

end LeftDelta

section Right

variable {M' L L' : CochainComplex (ModuleCat.{u} k) ℕ} (μR : LeibnizPairing M' L L')

/-- A pairing `M' × L[-1] → P'[-1]` (shift in the right factor, with the sign `(-1)ʳ`). -/
noncomputable def shiftRight : ∀ (r s n : ℕ), r + s = n →
    M'.X r →ₗ[k] shiftNegOneX L s →ₗ[k] shiftNegOneX L' n
  | _, 0, _, _ => 0
  | _, _ + 1, 0, _ => 0
  | r, s + 1, n + 1, _ => μR.μ (show r + s = n by omega)

theorem shiftRight_succ {r s n : ℕ} (h : r + (s + 1) = n + 1) (u : M'.X r) (c : L.X s) :
    μR.shiftRight r (s + 1) (n + 1) h u (shiftNegOneSucc L s c) =
      shiftNegOneSucc L' n (μR.μ (by omega) u c) :=
  rfl

theorem shiftRight_leibniz {r s n : ℕ} (h : r + s = n) (u : M'.X r) (c : shiftNegOneX L s) :
    (shiftNegOneD L' n).hom (μR.shiftRight r s n h u c) =
      -μR.shiftRight (r + 1) s (n + 1) (by omega) ((M'.d r (r + 1)).hom u) c +
        (-1 : k) ^ r • μR.shiftRight r (s + 1) (n + 1) (by omega) u ((shiftNegOneD L s).hom c) := by
  cases s with
  | zero =>
    have e1 : μR.shiftRight r 0 n h u c = 0 := rfl
    have e2 : (shiftNegOneD L 0).hom c = 0 := rfl
    have e3 : μR.shiftRight (r + 1) 0 (n + 1) (by omega) ((M'.d r (r + 1)).hom u) c = 0 := rfl
    rw [e1, e2, e3, map_zero, map_zero, neg_zero, smul_zero, add_zero]
  | succ s =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    revert c
    intro (c : L.X s)
    change -(L'.d m (m + 1)).hom (μR.μ (show r + s = m by omega) u c) =
      -μR.μ (show r + 1 + s = m + 1 by omega) ((M'.d r (r + 1)).hom u) c +
        (-1 : k) ^ r • μR.μ (show r + (s + 1) = m + 1 by omega) u (-(L.d s (s + 1)).hom c)
    rw [μR.leibniz, map_neg, smul_neg, neg_add]

variable {M K K' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'} (ρ : M ⟶ M')
  (μK : LeibnizPairing M K K')

/-- The pairing `M × Cocone(f) → Cocone(g)` (on the right factor). -/
noncomputable def coconeRightμ {r s n : ℕ} (h : r + s = n) :
    M.X r →ₗ[k] (mappingCoconeNat f).X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun x (p : K.X s × shiftNegOneX L s) =>
      ((μK.μ h x p.1, (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) p.2) :
        K'.X n × shiftNegOneX L' n))
    (fun x x' p => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom (x + x')) p.2 = _
      rw [map_add, LinearMap.map_add₂, smul_add]
      rfl))
    (fun c x p => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom (c • x)) p.2 = _
      rw [map_smul, LinearMap.map_smul₂, smul_comm]
      rfl))
    (fun x p q => Prod.ext (map_add _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) (p.2 + q.2) = _
      rw [map_add, smul_add]
      rfl))
    (fun c x p => Prod.ext (map_smul _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) (c • p.2) = _
      rw [map_smul, smul_comm]
      rfl))

theorem coconeRightμ_apply {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : K.X s)
    (c : shiftNegOneX L s) :
    coconeRightμ μR ρ μK (f := f) (f' := f') h x ((y, c) : K.X s × shiftNegOneX L s) =
      ((μK.μ h x y, (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) c) :
        K'.X n × shiftNegOneX L' n) :=
  rfl

/-- The Leibniz pairing `M × Cocone(f) → Cocone(g)` induced by compatible pairings. -/
noncomputable def coconeRight (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : K.X s),
    (f'.f n).hom (μK.μ h x y) = μR.μ h ((ρ.f r).hom x) ((f.f s).hom y)) :
    LeibnizPairing M (mappingCoconeNat f) (mappingCoconeNat f') where
  μ h := coconeRightμ μR ρ μK h
  leibniz {r s n} h x p := by
    revert p
    intro (p : K.X s × shiftNegOneX L s)
    obtain ⟨y, c⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x y) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x y)) +
        (shiftNegOneD L' n).hom ((-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) c) =
      (-1 : k) ^ (r + 1) • μR.shiftRight (r + 1) s (n + 1) (by omega)
          ((ρ.f (r + 1)).hom ((M.d r (r + 1)).hom x)) c +
        (-1 : k) ^ r • ((-1 : k) ^ r • μR.shiftRight r (s + 1) (n + 1) (by omega) ((ρ.f r).hom x)
          (shiftNegOneSucc L s ((f.f s).hom y) + (shiftNegOneD L s).hom c))
    have hsq : (-1 : k) ^ r * (-1 : k) ^ r = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hs : (-1 : k) ^ (r + 1) = -(-1 : k) ^ r := by rw [pow_succ, mul_neg_one]
    have hpp : ∀ v : shiftNegOneX L' (n + 1), (-1 : k) ^ r • (-1 : k) ^ r • v = v := fun v => by
      rw [smul_smul, hsq, one_smul]
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm r (r + 1)) x, hc, map_smul, shiftRight_leibniz,
      map_add, shiftRight_succ]
    conv_lhs => rw [smul_add, smul_neg, hpp]
    conv_rhs => rw [hpp, hs, neg_smul]
    abel

end Right

end LeibnizPairing

end ConePairing

-- from CompactSupportCohomology/ConeSymmetry.lean
section ConeSymmetry

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

namespace LeibnizPairing

variable {LA LB LC : CochainComplex (ModuleCat.{u} k) ℕ} (μLL : LeibnizPairing LA LB LC)

/-- The homotopy between left and right cone pairings, in the shifted terms. -/
noncomputable def shiftBoth : ∀ (r s m : ℕ), r + s = m + 1 →
    shiftNegOneX LA r → shiftNegOneX LB s → shiftNegOneX LC m
  | r + 1, s + 1, m + 1, _ => fun b c => μLL.μ (show r + s = m by omega) b c
  | _, _, _, _ => fun _ _ => 0

variable {KA KB KC LA' LB' : CochainComplex (ModuleCat.{u} k) ℕ} {fA : KA ⟶ LA} {fB : KB ⟶ LB}
  (ρA : KA ⟶ LA') (ρB : KB ⟶ LB') (μL : LeibnizPairing LA LB' LC) (μR : LeibnizPairing LA' LB LC)
  (hLL : ∀ {r s n : ℕ} (h : r + s = n) (u : LA.X r) (y : KB.X s),
    μL.μ h u ((ρB.f s).hom y) = μLL.μ h u ((fB.f s).hom y))
  (hRR : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (w : LB.X s),
    μR.μ h ((ρA.f r).hom x) w = μLL.μ h ((fA.f r).hom x) w)

include hLL hRR in
theorem shiftLeft_sub_shiftRight {r s m : ℕ} (h : r + s = m + 1) (x : KA.X r)
    (b : shiftNegOneX LA r) (y : KB.X s) (c : shiftNegOneX LB s)
    (hx : shiftNegOneSucc LA r ((fA.f r).hom x) + (shiftNegOneD LA r).hom b = 0)
    (hy : shiftNegOneSucc LB s ((fB.f s).hom y) + (shiftNegOneD LB s).hom c = 0) :
    μL.shiftLeft r s (m + 1) h b ((ρB.f s).hom y) -
        (-1 : k) ^ r • μR.shiftRight r s (m + 1) h ((ρA.f r).hom x) c =
      (shiftNegOneD LC m).hom ((-1 : k) ^ r • μLL.shiftBoth r s m h b c) := by
  cases r with
  | zero =>
    have hx' : (fA.f 0).hom x = 0 := by
      have e : (shiftNegOneD LA 0).hom b = 0 := rfl
      rw [e, add_zero] at hx
      exact hx
    have e1 : μL.shiftLeft 0 s (m + 1) h b ((ρB.f s).hom y) = 0 := rfl
    have e2 : μLL.shiftBoth 0 s m h b c = 0 := rfl
    rw [e1, e2, smul_zero, map_zero, zero_sub, neg_eq_zero]
    clear e1 e2 hy
    cases s with
    | zero =>
      have e : μR.shiftRight 0 0 (m + 1) h = 0 := rfl
      rw [e, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
    | succ s =>
      revert c
      intro (c : LB.X s)
      change (-1 : k) ^ 0 • μR.μ (show 0 + s = m by omega) ((ρA.f 0).hom x) c = 0
      rw [hRR, hx', map_zero, LinearMap.zero_apply, smul_zero]
  | succ r =>
    cases s with
    | zero =>
      have hy' : (fB.f 0).hom y = 0 := by
        have e : (shiftNegOneD LB 0).hom c = 0 := rfl
        rw [e, add_zero] at hy
        exact hy
      have e1 : μR.shiftRight (r + 1) 0 (m + 1) h ((ρA.f (r + 1)).hom x) c = 0 := rfl
      have e2 : μLL.shiftBoth (r + 1) 0 m h b c = 0 := rfl
      rw [e1, e2, smul_zero, smul_zero, map_zero, sub_zero]
      clear e1 e2 hx
      revert b
      intro (b : LA.X r)
      change μL.μ (show r + 0 = m by omega) b ((ρB.f 0).hom y) = 0
      rw [hLL, hy', map_zero]
    | succ s =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨r + s, by omega⟩
      revert b hx c hy
      intro (b : LA.X r) hx (c : LB.X s) hy
      have hx' : (fA.f (r + 1)).hom x = (LA.d r (r + 1)).hom b := by
        have e : ((fA.f (r + 1)).hom x : LA.X (r + 1)) + -(LA.d r (r + 1)).hom b = 0 := hx
        exact add_neg_eq_zero.1 e
      have hy' : (fB.f (s + 1)).hom y = (LB.d s (s + 1)).hom c := by
        have e : ((fB.f (s + 1)).hom y : LB.X (s + 1)) + -(LB.d s (s + 1)).hom c = 0 := hy
        exact add_neg_eq_zero.1 e
      change μL.μ (show r + (s + 1) = m + 1 by omega) b ((ρB.f (s + 1)).hom y) -
          (-1 : k) ^ (r + 1) • μR.μ (show r + 1 + s = m + 1 by omega) ((ρA.f (r + 1)).hom x) c =
        -(LC.d m (m + 1)).hom ((-1 : k) ^ (r + 1) • μLL.μ (show r + s = m by omega) b c)
      have e2 : (-1 : k) ^ (r + 1) * (-1 : k) ^ r = -1 := by
        rw [← pow_add, show r + 1 + r = 2 * r + 1 by omega, pow_succ, pow_mul, neg_one_sq, one_pow,
          one_mul]
      rw [hLL, hRR, hx', hy', map_smul, μLL.leibniz, smul_add, smul_smul, e2, neg_one_smul,
        neg_add, neg_neg]
      abel

variable {fC : KC ⟶ LC} (μK : LeibnizPairing KA KB KC)
  (hL : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (y : KB.X s),
    (fC.f n).hom (μK.μ h x y) = μL.μ h ((fA.f r).hom x) ((ρB.f s).hom y))
  (hR : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (y : KB.X s),
    (fC.f n).hom (μK.μ h x y) = μR.μ h ((ρA.f r).hom x) ((fB.f s).hom y))

include hLL hRR in
/-- The left and right cone pairings differ by a boundary on products of cycles. -/
theorem coconeLeftμ_sub_coconeRightμ_eq_d {r s m : ℕ} (h : r + s = m + 1)
    (X : (mappingCoconeNat fA).X r) (Y : (mappingCoconeNat fB).X s)
    (hX : (mappingCoconeNatD fA r).hom X = 0) (hY : (mappingCoconeNatD fB s).hom Y = 0) :
    ∃ W : (mappingCoconeNat fC).X m,
      coconeLeftμ μL ρB μK (f := fA) (f' := fC) h X (((mappingCoconeNat.fst fB).f s).hom Y) -
        coconeRightμ μR ρA μK (f := fB) (f' := fC) h (((mappingCoconeNat.fst fA).f r).hom X) Y =
      (mappingCoconeNatD fC m).hom W := by
  obtain ⟨x0, b⟩ := X
  obtain ⟨y0, c⟩ := Y
  refine ⟨((0 : KC.X m), (-1 : k) ^ r • μLL.shiftBoth r s m h b c), Prod.ext ?_ ?_⟩
  · change μK.μ h x0 y0 - μK.μ h x0 y0 = (KC.d m (m + 1)).hom 0
    rw [sub_self, map_zero]
  · change μL.shiftLeft r s (m + 1) h b ((ρB.f s).hom y0) -
        (-1 : k) ^ r • μR.shiftRight r s (m + 1) h ((ρA.f r).hom x0) c =
      shiftNegOneSucc LC m ((fC.f m).hom 0) +
        (shiftNegOneD LC m).hom ((-1 : k) ^ r • μLL.shiftBoth r s m h b c)
    rw [map_zero, map_zero, zero_add]
    exact shiftLeft_sub_shiftRight μLL ρA ρB μL μR hLL hRR h x0 b y0 c (congrArg Prod.snd hX)
      (congrArg Prod.snd hY)

include hLL hRR in

/-- In homology, pairing a class of `Cocone(f_A)` with the image of a class of `Cocone(f_B)` on
the left equals pairing the image of the first with the second on the right. -/
theorem coconeLeft_homology_eq_coconeRight_homology {r s n : ℕ} (h : r + s = n)
    (x : (mappingCoconeNat fA).homology r) (y : (mappingCoconeNat fB).homology s) :
    (coconeLeft μL ρB μK hL).homology h x
        ((HomologicalComplex.homologyMap (mappingCoconeNat.fst fB) s).hom y) =
      (coconeRight μR ρA μK hR).homology h
        ((HomologicalComplex.homologyMap (mappingCoconeNat.fst fA) r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, homology_homologyπ,
    homology_homologyπ]
  rw [← sub_eq_zero, ← map_sub]
  cases n with
  | zero =>
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := ⟨by omega, by omega⟩
    have e : (coconeLeft μL ρB μK hL).cycles h x
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fB) 0).hom y) -
      (coconeRight μR ρA μK hR).cycles h
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fA) 0).hom x) y = 0 := by
      apply iCycles_hom_injective
      rw [map_sub, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
        iCycles_cyclesMap_apply, map_zero, sub_eq_zero]
      exact Prod.ext rfl rfl
    rw [e, map_zero]
  | succ m =>
    have hX := iCycles_d_apply (mappingCoconeNat fA) r (r + 1) x
    have hY := iCycles_d_apply (mappingCoconeNat fB) s (s + 1) y
    rw [mappingCoconeNat_d] at hX hY
    obtain ⟨W, hW⟩ := coconeLeftμ_sub_coconeRightμ_eq_d μLL ρA ρB μL μR hLL hRR μK h _ _ hX hY
    have e : (coconeLeft μL ρB μK hL).cycles h x
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fB) s).hom y) -
      (coconeRight μR ρA μK hR).cycles h
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fA) r).hom x) y =
        ((mappingCoconeNat fC).toCycles m (m + 1)).hom W := by
      apply iCycles_hom_injective
      rw [map_sub, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
        iCycles_cyclesMap_apply, iCycles_toCycles_hom_apply, mappingCoconeNat_d]
      exact hW
    rw [e, homologyπ_toCycles_hom_apply]

end LeibnizPairing

end ConeSymmetry

end Langlands.GaloisCohomology
