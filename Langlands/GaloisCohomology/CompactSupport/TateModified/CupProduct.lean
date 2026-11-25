import Langlands.GaloisCohomology.CompactSupport.TateModified.Basic
import Langlands.GaloisCohomology.CompactSupport.CupProduct
import Langlands.Cohomology.Profinite.Coinduced.Acyclic

/-!
# Cup products with Tate-modified compact support

The cup product `Ĥ_c^r(G, A) × Hˢ(G, B) → Ĥ_c^{r+s}(G, C)` (`tateCompactCup`): the pairing on the
modified cocone is the cone pairing of `Internal/ConeSigns.lean` corrected by a homotopy, because
the norm cochains are compatible with cup products only up to the homotopy `normHomotopy`. The
cup product is compatible with the connecting maps of two short exact sequences, as in
`CupProduct.lean`.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from RealPlaces/ConeHomotopy.lean
section ConeHomotopy

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Prod

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The product of two Leibniz pairings, on product complexes. -/
noncomputable def prod (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) :
    LeibnizPairing (prodComplex M₁ M₂) (prodComplex N₁ N₂) (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N₁.X s × N₂.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y.1) (μ₂.leibniz h x.2 y.2)

theorem prod_μ_apply (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ}
    (h : r + s = n) (x : (prodComplex M₁ M₂).X r) (y : (prodComplex N₁ N₂).X s) :
    (prod μ₁ μ₂).μ h x y = ((μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2) : P₁.X n × P₂.X n) :=
  rfl

/-- Two Leibniz pairings with the same right factor, as one pairing on the products of the left
factors and of the targets. -/
noncomputable def prodLeft (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) :
    LeibnizPairing (prodComplex M₁ M₂) N (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y, μ₂.μ h x.2 y)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y) (μ₂.leibniz h x.2 y)

theorem prodLeft_μ_apply (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) {r s n : ℕ}
    (h : r + s = n) (x : (prodComplex M₁ M₂).X r) (y : N.X s) :
    (prodLeft μ₁ μ₂).μ h x y = ((μ₁.μ h x.1 y, μ₂.μ h x.2 y) : P₁.X n × P₂.X n) :=
  rfl

end Prod

section DegZero

variable {E E' : ModuleCat.{u} k} {N : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The components of `LeibnizPairing.degZero`. -/
noncomputable def degZeroμ (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    ∀ (r s n : ℕ), r + s = n →
      (degZeroComplex E).X r →ₗ[k] N.X s →ₗ[k] (degZeroComplex E').X n
  | 0, 0, 0, _ => β
  | _, _, _, _ => 0

theorem degZeroμ_succ (β : E →ₗ[k] N.X 0 →ₗ[k] E') (r s n : ℕ) (h : r + (s + 1) = n) :
    degZeroμ β r (s + 1) n h = 0 := by
  cases r <;> cases n <;> rfl

/-- A bilinear map `E × N⁰ → E'` as a Leibniz pairing of complexes concentrated in degree `0` (on
the left and target). -/
noncomputable def degZero (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    LeibnizPairing (degZeroComplex E) N (degZeroComplex E') where
  μ {r s n} h := degZeroμ β r s n h
  leibniz {r s n} h x y := by
    rw [degZeroComplex_d, degZeroComplex_d, degZeroμ_succ]
    simp

end DegZero

section CoconeHtpy

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (η : ∀ {r s n : ℕ}, r + s = n → K.X r →ₗ[k] N.X s →ₗ[k] shiftNegOneX L' n)

/-- The cone pairing corrected by a homotopy `η` (used when the compatibility of the pairings
holds only up to homotopy). -/
noncomputable def coconeLeftHtpyμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) :
        K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (p.2 + q.2) ((ρ.f s).hom z) + η h (p.1 + q.1) z = _
      rw [LinearMap.map_add₂, LinearMap.map_add₂]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h q.2 ((ρ.f s).hom z) + η h q.1 z)
      abel))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (c • p.2) ((ρ.f s).hom z) + η h (c • p.1) z = _
      rw [LinearMap.map_smul₂, LinearMap.map_smul₂]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) + η h p.1 (z + z') = _
      rw [map_add, map_add, map_add]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z') + η h p.1 z')
      abel))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) + η h p.1 (c • z) = _
      rw [map_smul, map_smul, map_smul]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))

theorem coconeLeftHtpyμ_apply {r s n : ℕ} (h : r + s = n) (x : K.X r) (y : shiftNegOneX L r)
    (z : N.X s) :
    coconeLeftHtpyμ μL ρ μK η (f := f) (f' := f') h ((x, y) : K.X r × shiftNegOneX L r) z =
      ((μK.μ h x z, μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) :
        K'.X n × shiftNegOneX L' n) :=
  rfl

/-- The Leibniz pairing on mapping cocones when the compatibility of the component pairings holds
up to a homotopy `η`. -/
noncomputable def coconeLeftHtpy
    (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
      shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
        shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
          η (by omega) ((K.d r (r + 1)).hom x) z +
          (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftHtpyμ μL ρ μK η h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) =
      (μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        η (by omega) ((K.d r (r + 1)).hom x) z) +
        (-1 : k) ^ r • (μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z)) + η (by omega) x ((N.d s (s + 1)).hom z))
    have key := eq_sub_of_add_eq' (hη h x z)
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, map_add, key,
      shiftLeft_leibniz, LinearMap.map_add₂, shiftLeft_succ, smul_add]
    abel

variable (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
    shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
      η (by omega) ((K.d r (r + 1)).hom x) z +
      (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z))

theorem coconeLeftHtpy_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeftHtpy μL ρ μK η hη).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
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
  refine Prod.ext (LinearMap.map_zero₂ _ _) ?_
  change μL.shiftLeft (r + 1) s (n + 1) h' _ _ + η h' 0 _ = _
  rw [LinearMap.map_zero₂, add_zero]
  rfl

end CoconeHtpy

end LeibnizPairing

end ConeHomotopy

-- from RealPlaces/NormHomotopy.lean
section NormHomotopy

open CategoryTheory MonoidalCategory groupCohomology


section Tuple

variable {α : Type*}

/-- The tuple `(a, g₀, …, g_{m-1})` of length `s = m + 1`. -/
def consTuple {s m : ℕ} (h : s = m + 1) (a : α) (g : Fin m → α) : Fin s → α :=
  fun i => if hi : (i : ℕ) = 0 then a else g ⟨i - 1, by omega⟩

theorem consTuple_rfl {m : ℕ} (a : α) (g : Fin m → α) :
    consTuple (rfl : m + 1 = m + 1) a g = Fin.cons a g := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consTuple]
  · simp only [consTuple, Fin.val_succ, Nat.add_one_ne_zero, dite_false, Fin.cons_succ]
    congr 1

theorem continuous_consTuple [TopologicalSpace α] {s m : ℕ} (h : s = m + 1) (a : α) :
    Continuous (consTuple h a) := by
  refine continuous_pi fun i => ?_
  unfold consTuple
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

end Tuple

section Homotopy

variable {k F : Type u} [CommRing k] [Group F] [Fintype F] {X Y Z : Rep.{u} k F}
  (μ : X ⊗ Y ⟶ Z)

/-- The homotopy relating the norm and the cup product with a `0`-cochain, at the level of
functions. -/
noncomputable def normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X) (y : (Fin s → F) → Y) : (Fin m → F) → Z :=
  fun g => ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F))))

theorem normHomotopyFun_add_left {s m : ℕ} (h : s = m + 1) (e e' : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (e + e') y = normHomotopyFun μ h e y + normHomotopyFun μ h e' y := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.add_tmul, map_add,
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_left {s m : ℕ} (h : s = m + 1) (c : k) (e : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (c • e) y = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem normHomotopyFun_add_right {s m : ℕ} (h : s = m + 1) (e : X) (y y' : (Fin s → F) → Y) :
    normHomotopyFun μ h e (y + y') = normHomotopyFun μ h e y + normHomotopyFun μ h e y' := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.tmul_add, map_add,
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_right {s m : ℕ} (h : s = m + 1) (c : k) (e : X)
    (y : (Fin s → F) → Y) :
    normHomotopyFun μ h e (c • y) = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem sum_ρ_μ_tmul_ρ_inv (e : X) (b : Y) :
    ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
  have h1 : ∀ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := fun a => by
    have h2 : ((X ⊗ Y).ρ a) ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F))) =
        ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
      change TensorProduct.map (X.ρ a) (Y.ρ a) (e ⊗ₜ[k] Y.ρ a⁻¹ b) = _
      rw [TensorProduct.map_tmul, Representation.self_inv_apply]
    exact (Rep.hom_comm_apply μ a _).symm.trans (congrArg _ h2)
  rw [Finset.sum_congr rfl fun a _ => h1 a, ← map_sum, ← TensorProduct.sum_tmul]
  congr 2
  simp [Representation.norm]

theorem normHomotopyFun_d_add {m : ℕ} (e : X) (y : (Fin (m + 1) → F) → Y) :
    (inhomogeneousCochains.d Z m).hom (normHomotopyFun μ rfl e y) +
        normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) := by
  funext g
  have hdy : ∀ a : F, (inhomogeneousCochains.d Y (m + 1)).hom y (Fin.cons a⁻¹ g) =
      Y.ρ a⁻¹ (y g) - y (Fin.cons (a⁻¹ * g 0) fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          y (Fin.cons a⁻¹ (Fin.contractNth j (· * ·) g)) := by
    intro a
    rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons,
      Fin.val_zero, Fin.val_succ, zero_add, pow_one, neg_one_smul]
    have e2 : ∀ j : Fin (m + 1), (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := fun _ => rfl
    simp only [e2]
    abel
  have hsplit : normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) g =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) -
        Z.ρ (g 0) (normHomotopyFun μ rfl e y fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          normHomotopyFun μ rfl e y (Fin.contractNth j (· * ·) g) := by
    simp only [normHomotopyFun, consTuple_rfl]
    simp only [hdy, TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, map_add, map_sub, map_sum, map_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [sum_ρ_μ_tmul_ρ_inv μ e (y g), Finset.sum_comm (β := Z.V)]
    congr 2
    · refine (Fintype.sum_equiv (Equiv.mulLeft (g 0)) _ _ fun a => ?_).symm
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]
    · funext j
      rw [Finset.smul_sum]
  rw [Pi.add_apply, inhomogeneousCochains.d_hom_apply, hsplit]
  have hpow : ∀ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) = -(-1 : k) ^ ((j : ℕ) + 1) :=
    fun j => by rw [pow_succ, mul_neg_one]
  simp only [hpow, neg_smul, Finset.sum_neg_distrib]
  abel

theorem normHomotopyFun_d_zero (e : X) (z : (Fin 0 → F) → Y) :
    normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y 0).hom z) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F))) -
        Z.ρ.norm (μ.hom ((e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F)))) := by
  funext g
  set b := z g with hb
  have hzc : z = fun _ => b := funext fun g' => congrArg z (Subsingleton.elim g' g)
  rw [hzc]
  simp only [normHomotopyFun, inhomogeneousCochains.d_hom_apply, consTuple_rfl, Fin.cons_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one,
    neg_one_smul, ← sub_eq_add_neg,
    TensorProduct.tmul_sub, map_sub, Finset.sum_sub_distrib]
  rw [sum_ρ_μ_tmul_ρ_inv]
  congr 1
  simp [Representation.norm]

end Homotopy

section LocallyConstant

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F] {X Y Z : Rep.{u} k F} [IsSmoothRep X] [IsSmoothRep Y] [IsSmoothRep Z]
  (μ : X ⊗ Y ⟶ Z)

omit [IsTopologicalGroup F] [IsSmoothRep X] [IsSmoothRep Y] [IsSmoothRep Z] in
theorem isLocallyConstant_normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X)
    {y : (Fin s → F) → Y} (hy : IsLocallyConstant y) :
    IsLocallyConstant (normHomotopyFun μ h e y) := by
  have e1 : normHomotopyFun μ h e y = ∑ a : F, fun g =>
      Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F)))) := by
    funext g
    simp [normHomotopyFun, Finset.sum_apply]
  rw [e1]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
    (IsLocallyConstant.const 0) fun a _ =>
      (hy.comp_continuous (continuous_consTuple h a⁻¹)).comp
        (fun b : Y => Z.ρ a (μ.hom ((e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))))

/-- The homotopy relating the norm and the cup product with a `0`-cochain, as a bilinear map of
cochains. -/
noncomputable def normHomotopy {s m : ℕ} (h : s = m + 1) :
    X →ₗ[k] (cochains Y).X s →ₗ[k] (cochains Z).X m :=
  LinearMap.mk₂ k (fun e y => mkCochain Z (normHomotopyFun μ h e (cochainOf Y y))
      (isLocallyConstant_normHomotopyFun μ h e (isLocallyConstant_cochainOf y)))
    (fun e e' _ => cochainOf_injective (normHomotopyFun_add_left μ h e e' _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_left μ h c e _))
    (fun e _ _ => cochainOf_injective (normHomotopyFun_add_right μ h e _ _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_right μ h c e _))

omit [IsSmoothRep X] in
theorem cochainOf_normHomotopy {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochains Y).X s) :
    cochainOf Z (normHomotopy μ h e y) = normHomotopyFun μ h e (cochainOf Y y) :=
  rfl

omit [Fintype F] in

theorem cochainOf_cupPairingCochains_zeroCochain {n : ℕ} (x : X) (y : (cochains Y).X n)
    (g : Fin n → F) :
    cochainOf Z (cupPairingCochains μ (zero_add n) (zeroCochain X x) y) g =
      μ.hom ((x ⊗ₜ[k] cochainOf Y y g : (X ⊗ Y : Rep k F))) := by
  rw [cochainOf_cupPairingCochains]
  change μ.hom (cupCochain _ _ _ g) = _
  rw [cupCochain_apply]
  congr 2
  have hp : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  rw [hp, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  exact Fin.ext (zero_add _)

theorem d_normHomotopy_add {m : ℕ} (e : X) (y : (cochains Y).X (m + 1)) :
    ((cochains Z).d m (m + 1)).hom (normHomotopy μ rfl e y) +
        normHomotopy μ rfl e (((cochains Y).d (m + 1) (m + 1 + 1)).hom y) =
      cupPairingCochains μ (zero_add (m + 1)) (zeroCochain X (X.ρ.norm e)) y := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_d, cochainOf_normHomotopy, cochainOf_normHomotopy, cochainOf_d,
    normHomotopyFun_d_add]
  funext g
  rw [cochainOf_cupPairingCochains_zeroCochain]

theorem normHomotopy_d_zero (e : X) (z : (cochains Y).X 0) :
    normHomotopy μ rfl e (((cochains Y).d 0 1).hom z) =
      cupPairingCochains μ (zero_add 0) (zeroCochain X (X.ρ.norm e)) z -
        zeroCochain Z (Z.ρ.norm (μ.hom ((e ⊗ₜ[k] cochainOf Y z (fun i => i.elim0) :
          (X ⊗ Y : Rep k F))))) := by
  apply cochainOf_injective
  rw [cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_zero]
  funext g
  have hg : g = fun i => i.elim0 := Subsingleton.elim _ _
  subst hg
  rw [show ∀ a b : (cochains Z).X 0, cochainOf Z (a - b) = cochainOf Z a - cochainOf Z b
    from fun _ _ => rfl, Pi.sub_apply, cochainOf_cupPairingCochains_zeroCochain]
  rfl

end LocallyConstant

end NormHomotopy

-- from RealPlaces/HomologyMapProdFstProdLeftHomology.lean
section HomologyMapProdFstProdLeftHomology

open CategoryTheory Limits MonoidalCategory Langlands.ProfiniteCohomology.GroupCoh


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Pairing

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Aᵣ w)] [∀ w, IsSmoothRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w : F w →* G) C ⟶ Cᵣ w}

variable (B) in

/-- Restriction of the cochains of `B` to all local groups. -/
noncomputable def tateLocalResB :
    cochains B ⟶ tateLocalComplex (fun v => Rep.res (φ v : H v →* G) B)
      (fun w => Rep.res (ψ w : F w →* G) B) :=
  prodLift (localRes φ B _ fun _ => 𝟙 _) (localRes ψ B _ fun _ => 𝟙 _)

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w : F w →* G) B ⟶ Cᵣ w)

/-- The value of a `0`-cochain. -/
noncomputable def zeroCochainValue : (cochains B).X 0 →ₗ[k] B where
  toFun z := cochainOf B z (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pairing `A_w × C⁰(G, B) → C_w` in degree `0` at a finite group `F_w`. -/
noncomputable def tateExtraPairingAt (w : κ) : Aᵣ w →ₗ[k] (cochains B).X 0 →ₗ[k] Cᵣ w :=
  ((TensorProduct.mk k (Aᵣ w) (Rep.res (ψ w : F w →* G) B)).compr₂ (μᵣ w).hom.toLinearMap).compl₂
    (zeroCochainValue (B := B))

/-- The pairing `∏_w A_w × C⁰(G, B) → ∏_w C_w` in degree `0`. -/
noncomputable def tateExtraPairing :
    (∀ w, Aᵣ w) →ₗ[k] (cochains B).X 0 →ₗ[k] (∀ w, Cᵣ w) :=
  LinearMap.mk₂ k (fun e z w => tateExtraPairingAt ψ μᵣ w (e w) z)
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => map_add (tateExtraPairingAt ψ μᵣ w _) _ _)
    (fun _ _ _ => funext fun w => map_smul (tateExtraPairingAt ψ μᵣ w _) _ _)

omit [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] [∀ w, IsSmoothRep (Aᵣ w)]
  [∀ w, IsSmoothRep (Cᵣ w)] in
theorem tateExtraPairing_apply (e : ∀ w, Aᵣ w) (z : (cochains B).X 0) (w : κ) :
    tateExtraPairing ψ μᵣ e z w = (μᵣ w).hom ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
      (Aᵣ w ⊗ Rep.res (ψ w : F w →* G) B : Rep k (F w)))) :=
  rfl

/-- The cup product on the global term of the Tate-modified cocone. -/
noncomputable def tateGlobalCup :
    LeibnizPairing (tateGlobalComplex A Aᵣ) (cochains B) (tateGlobalComplex C Cᵣ) :=
  LeibnizPairing.prodLeft (cupLeibniz μ) (LeibnizPairing.degZero (tateExtraPairing ψ μᵣ))

/-- The cup product on the local term of the Tate-modified cocone. -/
noncomputable def tateLocalCup :
    LeibnizPairing (tateLocalComplex Aᵥ Aᵣ)
      (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) B) (fun w => Rep.res (ψ w : F w →* G) B))
      (tateLocalComplex Cᵥ Cᵣ) :=
  LeibnizPairing.prod (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w))

/-- The homotopy, at the finite groups, between the two composites in the cone pairing. -/
noncomputable def tateNormHomotopy {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochains B).X s →ₗ[k] (∀ w, (cochains (Cᵣ w)).X m) :=
  LinearMap.mk₂ k (fun e z w => normHomotopy (μᵣ w) h (e w)
      (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f s).hom z w))
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun e _ _ => funext fun w => by
      rw [map_add]
      exact map_add (normHomotopy (μᵣ w) h (e w)) _ _)
    (fun c e _ => funext fun w => by
      rw [map_smul]
      exact map_smul (normHomotopy (μᵣ w) h (e w)) c _)

/-- `tateNormHomotopy` placed in the local term. -/
noncomputable def tateCupHomotopyL {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochains B).X s →ₗ[k] (tateLocalComplex Cᵥ Cᵣ).X m :=
  -(tateNormHomotopy ψ μᵣ h).compr₂ (LinearMap.inr k
    ((piComplex fun v => cochains (Cᵥ v)).X m) ((piComplex fun w => cochains (Cᵣ w)).X m))

omit [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateCupHomotopyL_apply {s m : ℕ} (h : s = m + 1) (e : ∀ w, Aᵣ w)
    (z : (cochains B).X s) :
    tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) h e z = ((0, -tateNormHomotopy ψ μᵣ h e z) :
        (piComplex fun v => cochains (Cᵥ v)).X m ×
          (piComplex fun w => cochains (Cᵣ w)).X m) :=
  Prod.ext neg_zero rfl

/-- The homotopy making the cup products compatible with `tateCompactRes`. -/
noncomputable def tateCupHomotopy : ∀ (r s n : ℕ), r + s = n →
    (tateGlobalComplex A Aᵣ).X r →ₗ[k] (cochains B).X s →ₗ[k]
      shiftNegOneX (tateLocalComplex Cᵥ Cᵣ) n
  | 0, _, n + 1, h => (tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) (by omega : _ = n + 1)).comp
      (LinearMap.snd k _ ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0))
  | _, _, _, _ => 0

end Pairing

section Spec

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Aᵣ w)] [∀ w, IsSmoothRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w : F w →* G) C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w : F w →* G) B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
    resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w : F w →* G)).map μ ≫ cr w =
    resTensorHom (ψ w : F w →* G) (ar w) (𝟙 _) ≫ μᵣ w)

theorem normCochains_f_succ_apply' (n : ℕ) (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X (n + 1)) :
    ((normCochains Aᵣ).f (n + 1)).hom e = 0 :=
  rfl

omit [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateCupHomotopy_succ_left (r s n : ℕ) (h : r + 1 + s = n) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) (r + 1) s n h = 0 :=
  rfl

omit [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_zero (s : ℕ) (h : 0 + s = 0) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) 0 s 0 h = 0 :=
  rfl

omit [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_succ (s n : ℕ) (h : 0 + s = n + 1) (hs : s = n + 1)
    (x : (tateGlobalComplex A Aᵣ).X 0) (z : (cochains B).X s) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) 0 s (n + 1) h x z =
      tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) hs x.2 z :=
  rfl

include hμ hμr in

theorem tateCupHomotopy_spec {r s n : ℕ} (h : r + s = n) (x : (tateGlobalComplex A Aᵣ).X r)
    (z : (cochains B).X s) :
    shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n (((tateCompactRes φ ψ C Cᵥ c Cᵣ cr).f n).hom
        ((tateGlobalCup ψ μ μᵣ).μ h x z)) +
        (shiftNegOneD (tateLocalComplex Cᵥ Cᵣ) n).hom (tateCupHomotopy ψ μᵣ r s n h x z) =
      shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n ((tateLocalCup φ ψ μᵥ μᵣ).μ h
          (((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f r).hom x) (((tateLocalResB φ ψ B).f s).hom z)) +
        tateCupHomotopy ψ μᵣ (r + 1) s (n + 1) (by omega)
          (((tateGlobalComplex A Aᵣ).d r (r + 1)).hom x) z +
        (-1 : k) ^ r • tateCupHomotopy ψ μᵣ r (s + 1) (n + 1) (by omega) x
          (((cochains B).d s (s + 1)).hom z) := by
  rcases r with _ | r
  · rcases s with _ | t
    ·
      obtain rfl : n = 0 := by omega
      rw [tateCupHomotopy_zero_zero, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ 1 0 _ rfl, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply]
      erw [tateCupHomotopyL_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f 0).hom (cupPairingCochains μ h x.1 z) =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f 0).hom z) + 0
        rw [add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f 0).hom (cupPairingCochains μ h x.1 z) w +
            zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm (tateExtraPairing ψ μᵣ (show ∀ w, Aᵣ w from x.2) z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f 0).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (0 + 1)).hom (((cochains B).d 0 (0 + 1)).hom z) w)
        have hres := congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f (0 + 1)).hom
            (((cochains B).d 0 (0 + 1)).hom z) w =
            ((cochains (Rep.res (ψ w : F w →* G) B)).d 0 (0 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f 0).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ 0 _ w
        have hz0 : cochainOf (Rep.res (ψ w : F w →* G) B)
            (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f 0).hom z w)
            (fun i => i.elim0) = cochainOf B z (fun i => i.elim0) :=
          congrArg (cochainOf B z) (Subsingleton.elim _ _)
        rw [hres, LinearMap.map_add₂, hd, normHomotopy_d_zero, hz0]
        change _ + zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm ((μᵣ w).hom _)) = _
        abel
    ·
      obtain rfl : n = t + 1 := by omega
      rw [tateCupHomotopy_zero_succ ψ μᵣ (t + 1) t _ rfl, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ (t + 1 + 1) (t + 1) _ rfl, LinearMap.zero_apply,
        LinearMap.zero_apply, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
      erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply, prodComplex_d_hom_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f (t + 1)).hom (cupPairingCochains μ h x.1 z) +
            -((piComplex fun v => cochains (Cᵥ v)).d t (t + 1)).hom 0 =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f (t + 1)).hom z) + 0
        rw [map_zero, neg_zero, add_zero, add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -(((piComplex fun w => cochains (Cᵣ w)).d t (t + 1)).hom
              (-tateNormHomotopy ψ μᵣ (rfl : t + 1 = t + 1) x.2 z) w) = _
        erw [piComplex_d_hom_apply]
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -((cochains (Cᵣ w)).d t (t + 1)).hom
              (-normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
                (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1 + 1)).hom
              (((cochains B).d (t + 1) (t + 1 + 1)).hom z) w)
        have hres : ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w =
            cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w)
              (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f (t + 1)).hom z w) :=
          congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f
            (t + 1 + 1)).hom (((cochains B).d (t + 1) (t + 1 + 1)).hom z) w =
            ((cochains (Rep.res (ψ w : F w →* G) B)).d (t + 1) (t + 1 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f
                (t + 1)).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ (t + 1) _ w
        have key := d_normHomotopy_add (μᵣ w) ((show ∀ w, Aᵣ w from x.2) w)
          (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        rw [hres, LinearMap.map_add₂, hd, map_neg, neg_neg, ← key]
        change _ + (0 : (cochains (Cᵣ w)).X (t + 1)) + _ = _
        abel
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    rw [tateCupHomotopy_succ_left, tateCupHomotopy_succ_left, tateCupHomotopy_succ_left,
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero, smul_zero, add_zero,
      shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    refine Prod.ext ?_ ?_
    · exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
    · change ((localRes ψ C Cᵣ cr).f (m + 1)).hom (cupPairingCochains μ h x.1 z) +
          ((normCochains Cᵣ).f (m + 1)).hom
            (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) (r + 1) s (m + 1) h x.2 z) =
        (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w)).μ h
          (((localRes ψ A Aᵣ ar).f (r + 1)).hom x.1 + ((normCochains Aᵣ).f (r + 1)).hom x.2)
          (((localRes ψ B _ fun _ => 𝟙 _).f s).hom z)
      rw [normCochains_f_succ_apply', normCochains_f_succ_apply', add_zero, add_zero]
      exact localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z

end Spec

section ProdHomology

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_prodFst_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodFst P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₁.homology h ((HomologicalComplex.homologyMap (prodFst M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodFst N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

theorem LeibnizPairing.homologyMap_prodSnd_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodSnd P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap (prodSnd M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodSnd N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

end ProdHomology

section Cup

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Aᵣ w)] [∀ w, IsSmoothRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w : F w →* G) C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w : F w →* G) B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
    resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w : F w →* G)).map μ ≫ cr w =
    resTensorHom (ψ w : F w →* G) (ar w) (𝟙 _) ≫ μᵣ w)

/-- The Leibniz pairing `Ĉ_c•(G, A) × C•(G, B) → Ĉ_c•(G, C)`. -/
noncomputable def tateCompactCupLeibniz :
    LeibnizPairing (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar) (cochains B)
      (tateCompactCochains φ ψ C Cᵥ c Cᵣ cr) :=
  LeibnizPairing.coconeLeftHtpy (tateLocalCup φ ψ μᵥ μᵣ) (tateLocalResB φ ψ B)
    (tateGlobalCup ψ μ μᵣ) (fun {r s n} h => tateCupHomotopy ψ μᵣ r s n h)
    (fun h x z => tateCupHomotopy_spec φ ψ μ μᵥ μᵣ hμ hμr h x z)

/-- The cup product `Ĥ_c^r(G, A) × Hˢ(G, B) → Ĥ_c^{r+s}(G, C)` with Tate-modified compact support.
-/
noncomputable def tateCompactCup {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar r →ₗ[k] cohomology B s →ₗ[k]
      tateCompactCohomology φ ψ C Cᵥ c Cᵣ cr n :=
  (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h

theorem tateCompactCup_tateLocalToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : (∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) (z : cohomology B s) :
    tateCompactCup φ ψ μ μᵥ μᵣ hμ hμr h' ((tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar r).hom ξ) z =
      (tateLocalToCompact φ ψ C Cᵥ c Cᵣ cr n).hom
        ((fun v => cupPairing (μᵥ v) h (ξ.1 v)
            ((map (φ v) (𝟙 _) s).hom z)),
          (fun w => cupPairing (μᵣ w) h (ξ.2 w)
            ((map (ψ w) (𝟙 _) s).hom z))) := by
  change (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h'
      ((mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) r).hom
        ((tateLocalCohomologyIso Aᵥ Aᵣ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (tateCompactRes φ ψ C Cᵥ c Cᵣ cr) n).hom
      ((tateLocalCohomologyIso Cᵥ Cᵣ n).inv.hom _)
  refine (LeibnizPairing.coconeLeftHtpy_homology_homologyδ _ _ _ _ _ h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (tateLocalCohomologyIso Cᵥ Cᵣ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Cᵥ Cᵣ n).inv_hom_id]
  have hξ := hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Aᵥ Aᵣ r).inv_hom_id
    (show ModuleCat.of k ((∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) from ξ)
  rw [tateLocalCohomologyIso_hom_apply] at hξ
  rw [tateLocalCohomologyIso_hom_apply]
  have ρ1 : tateLocalResB φ ψ B ≫ prodFst _ _ =
      localRes φ B (fun v => Rep.res (φ v : H v →* G) B) (fun _ => 𝟙 _) := prodLift_prodFst _ _
  have ρ2 : tateLocalResB φ ψ B ≫ prodSnd _ _ =
      localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) (fun _ => 𝟙 _) := prodLift_prodSnd _ _
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodFst_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
    refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵥ v) h p q) (congrFun (congrArg Prod.fst hξ) v) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodFst _ _) s).symm z, ρ1]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMap (φ v)
        (𝟙 (Rep.res (φ v : H v →* G) B))) s) z) v
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodSnd_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun w => cupLeibniz (μᵣ w)) h _ _ w).trans ?_
    refine (cupLeibniz_homology (μᵣ w) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵣ w) h p q) (congrFun (congrArg Prod.snd hξ) w) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodSnd _ _) s).symm z, ρ2]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun w => cochainsMap (ψ w)
        (𝟙 (Rep.res (ψ w : F w →* G) B))) s) z) w

end Cup

end HomologyMapProdFstProdLeftHomology

-- from RealPlaces/CupSequence.lean
section CupSequence

open CategoryTheory Limits MonoidalCategory Langlands.ProfiniteCohomology.GroupCoh


section Compat

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F]

theorem normHomotopy_compat_left {X₁ X₂ Y₁ Y₂ Z : Rep.{u} k F} [IsSmoothRep Y₁] [IsSmoothRep Y₂]
    [IsSmoothRep Z] (μ₁ : X₁ ⊗ Y₁ ⟶ Z) (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (f : X₁ ⟶ X₂) (g : Y₂ ⟶ Y₁)
    (hc : (f ⊗ₘ 𝟙 Y₂) ≫ μ₂ = (𝟙 X₁ ⊗ₘ g) ≫ μ₁) {s m : ℕ} (h : s = m + 1) (e : X₁)
    (y : (cochains Y₂).X s) :
    normHomotopy μ₂ h (f.hom e) y = normHomotopy μ₁ h e (((coeffCochainsMap g).f s).hom y) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₁ ⊗ Y₂ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₂ y (consTuple h a⁻¹ σ) :
    (X₁ ⊗ Y₂ : Rep k F)))) hc

theorem normHomotopy_compat_right {X₂ X₃ Y₁ Y₂ Z : Rep.{u} k F} [IsSmoothRep Y₁]
    [IsSmoothRep Y₂] [IsSmoothRep Z] (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (μ₃ : X₃ ⊗ Y₁ ⟶ Z) (f : Y₁ ⟶ Y₂)
    (g : X₂ ⟶ X₃) (hc : (𝟙 X₂ ⊗ₘ f) ≫ μ₂ = (g ⊗ₘ 𝟙 Y₁) ≫ μ₃) {s m : ℕ} (h : s = m + 1) (e : X₂)
    (y : (cochains Y₁).X s) :
    normHomotopy μ₂ h e (((coeffCochainsMap f).f s).hom y) = normHomotopy μ₃ h (g.hom e) y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₂ ⊗ Y₁ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₁ y (consTuple h a⁻¹ σ) :
    (X₂ ⊗ Y₁ : Rep k F)))) hc

end Compat

section TwoSequences

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {SA : ShortComplex (Rep.{u} k G)} [IsSmoothRep SA.X₁] [IsSmoothRep SA.X₂]
  [IsSmoothRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsSmoothRep (SAᵥ v).X₁] [∀ v, IsSmoothRep (SAᵥ v).X₂] [∀ v, IsSmoothRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v : H v →* G)) ⟶ SAᵥ v)
  {SAᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))}
  [∀ w, IsSmoothRep (SAᵣ w).X₁] [∀ w, IsSmoothRep (SAᵣ w).X₂] [∀ w, IsSmoothRep (SAᵣ w).X₃]
  (sAr : ∀ w, SA.map (Rep.resFunctor (ψ w : F w →* G)) ⟶ SAᵣ w)
  {SB : ShortComplex (Rep.{u} k G)} [IsSmoothRep SB.X₁] [IsSmoothRep SB.X₂]
  [IsSmoothRep SB.X₃] {C : Rep.{u} k G} [IsSmoothRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsSmoothRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  {Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Cᵣ w)]
  {cr : ∀ w, Rep.res (ψ w : F w →* G) C ⟶ Cᵣ w}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v : H v →* G) SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v : H v →* G) SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v : H v →* G) SB.X₁ ⟶ Cᵥ v)
  (μ₁ᵣ : ∀ w, (SAᵣ w).X₁ ⊗ Rep.res (ψ w : F w →* G) SB.X₃ ⟶ Cᵣ w)
  (μ₂ᵣ : ∀ w, (SAᵣ w).X₂ ⊗ Rep.res (ψ w : F w →* G) SB.X₂ ⟶ Cᵣ w)
  (μ₃ᵣ : ∀ w, (SAᵣ w).X₃ ⊗ Rep.res (ψ w : F w →* G) SB.X₁ ⟶ Cᵣ w)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₁ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₂ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₃ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)
  (hμ₁ᵣ : ∀ w, (Rep.resFunctor (ψ w : F w →* G)).map μ₁ ≫ cr w =
    resTensorHom (ψ w : F w →* G) (sAr w).τ₁ (𝟙 _) ≫ μ₁ᵣ w)
  (hμ₂ᵣ : ∀ w, (Rep.resFunctor (ψ w : F w →* G)).map μ₂ ≫ cr w =
    resTensorHom (ψ w : F w →* G) (sAr w).τ₂ (𝟙 _) ≫ μ₂ᵣ w)
  (hμ₃ᵣ : ∀ w, (Rep.resFunctor (ψ w : F w →* G)).map μ₃ ≫ cr w =
    resTensorHom (ψ w : F w →* G) (sAr w).τ₃ (𝟙 _) ≫ μ₃ᵣ w)

include hμ₂ hμ₂ᵣ in

theorem tateCompactCup_tateCompactδ_add_tateCompactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v : H v →* G)).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v : H v →* G)).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (h₁₂ᵣ : ∀ w, ((SAᵣ w).f ⊗ₘ 𝟙 _) ≫ μ₂ᵣ w =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w : F w →* G)).map SB.g) ≫ μ₁ᵣ w)
    (h₂₃ᵣ : ∀ w, (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w : F w →* G)).map SB.f) ≫ μ₂ᵣ w =
      ((SAᵣ w).g ⊗ₘ 𝟙 _) ≫ μ₃ᵣ w)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSAᵣ : ∀ w, (SAᵣ w).ShortExact)
    (hSB : SB.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : tateCompactCohomology φ ψ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃)
      (fun w => (SAᵣ w).X₃) (fun w => (sAr w).τ₃) r)
    (y : cohomology SB.X₃ s) :
    tateCompactCup φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ h₁ ((tateCompactδ φ ψ sA sAr hSA hSAᵥ hSAᵣ r).hom x) y +
      (-1 : k) ^ r • tateCompactCup φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ SA SAᵥ sA SAᵣ sAr))
    (SN := cochainsShortComplex SB) (tateCompactCupLeibniz φ ψ μ₂ μ₂ᵥ μ₂ᵣ hμ₂ hμ₂ᵣ)
    (tateCompactCupLeibniz φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ) (tateCompactCupLeibniz φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ)
    ?_ ?_ (tateCompactCochains_shortExact φ ψ sA sAr hSA hSAᵥ hSAᵣ)
    (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₁ fun w => (SAᵣ w).X₁).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₁) fun w => (SAᵣ w).X₁) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₂ y (fun i => i.elim0) :
            ((SAᵣ w).X₁ ⊗ Rep.res (ψ w : F w →* G) SB.X₂ : Rep k (F w))))) (h₁₂ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).f).hom e) y =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₁ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((coeffCochainsMap SB.g).f (t + 1)).hom y)
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_left (μ₁ᵣ w) (μ₂ᵣ w) (SAᵣ w).f _ (h₁₂ᵣ w) rfl (e w) _
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).f) fun w => (SAᵣ w).f).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₂).f s).hom y) + 0 =
            (tateLocalCup φ ψ μ₁ᵥ μ₁ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₃).f s).hom (((coeffCochainsMap SB.g).f s).hom y)) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v : H v →* G))) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v : H v →* G) ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w : F w →* G))) (μ₁ᵣ w) (μ₂ᵣ w) (h₁₂ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₂ y (⇑(ψ w : F w →* G) ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₂ fun w => (SAᵣ w).X₂).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₂) fun w => (SAᵣ w).X₂) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₁ y (fun i => i.elim0) :
            ((SAᵣ w).X₂ ⊗ Rep.res (ψ w : F w →* G) SB.X₁ : Rep k (F w))))) (h₂₃ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((coeffCochainsMap SB.f).f (t + 1)).hom y) =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₃ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).g).hom e) y
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_right (μ₂ᵣ w) (μ₃ᵣ w)
            ((Rep.resFunctor (ψ w : F w →* G)).map SB.f) (SAᵣ w).g (h₂₃ᵣ w) rfl (e w)
            (((localRes ψ SB.X₁ (fun w => Rep.res (ψ w : F w →* G) SB.X₁) fun _ => 𝟙 _).f
              (t + 1)).hom y w)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₂).f s).hom (((coeffCochainsMap SB.f).f s).hom y)) + 0 =
            (tateLocalCup φ ψ μ₃ᵥ μ₃ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).g) fun w => (SAᵣ w).g).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₁).f s).hom y) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v : H v →* G))) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v : H v →* G) ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w : F w →* G))) (μ₂ᵣ w) (μ₃ᵣ w) (h₂₃ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₁ y (⇑(ψ w : F w →* G) ∘ τ)) σ

end TwoSequences

end CupSequence

end Langlands.GaloisCohomology
