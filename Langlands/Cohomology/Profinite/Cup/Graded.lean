import Langlands.Cohomology.Profinite.Coinduced.Acyclic
import Langlands.Cohomology.Profinite.Cup.Basic

/-!
# Graded commutativity of the cup product

For a compact group `G` and smooth representations `A`, `B`:
`(β_ A B)_* (x ∪ y) = (-1)^{pq} (y ∪ x)` for `x ∈ Hᵖ(G, A)`, `y ∈ H^q(G, B)`.

The proof follows the classical one: the reversal of inhomogeneous cochains
`f ↦ (x ↦ (-1)^{n(n+1)/2} (x₀⋯x_{n-1}) · f(x_{n-1}⁻¹, …, x₀⁻¹))` (`GroupCoh.revCochain`) commutes
with the differential and induces the identity on cohomology (by dimension shifting with the
acyclic coinduced modules), and it exchanges `f ∪ g` with `± β(g' ∪ f')`.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology

namespace Langlands.ProfiniteCohomology

namespace GroupCoh


section Signs

def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

theorem triangle_zero : triangle 0 = 0 := rfl

theorem triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := rfl

theorem triangle_add (p q : ℕ) : triangle (p + q) = triangle p + triangle q + p * q := by
  induction q with
  | zero => simp [triangle_zero]
  | succ q ih =>
    rw [← add_assoc, triangle_succ, ih, triangle_succ]
    ring

theorem neg_one_pow_eq_of_mod_two {R : Type*} [Monoid R] [HasDistribNeg R] {a b : ℕ}
    (h : a % 2 = b % 2) : (-1 : R) ^ a = (-1 : R) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    neg_one_sq, one_pow, one_pow, h]

end Signs

section Tuples

variable {G : Type*} [Group G] {n : ℕ}

def revInv (x : Fin n → G) : Fin n → G := fun i => (x i.rev)⁻¹

theorem revInv_apply (x : Fin n → G) (i : Fin n) : revInv x i = (x i.rev)⁻¹ := rfl

theorem partialProd_last_revInv (x : Fin n → G) :
    Fin.partialProd (revInv x) (Fin.last n) = (Fin.partialProd x (Fin.last n))⁻¹ := by
  induction n with
  | zero => simp [show Fin.last 0 = 0 from rfl]
  | succ n ih =>
    have h1 := Fin.partialProd_succ (revInv x) (Fin.last n)
    have h2 := Fin.partialProd_succ' x (Fin.last n)
    rw [Fin.succ_last] at h1 h2
    rw [h1, h2, ← Fin.partialProd_init]
    have : Fin.init (revInv x) = revInv (Fin.tail x) := by
      funext i
      simp only [Fin.init, Fin.tail, revInv_apply]
      congr 2
      ext
      simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [this, ih, revInv_apply, mul_inv_rev, Fin.rev_last]

theorem tail_revInv (x : Fin (n + 1) → G) : Fin.tail (revInv x) = revInv (Fin.init x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

theorem init_revInv (x : Fin (n + 1) → G) : Fin.init (revInv x) = revInv (Fin.tail x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

theorem contractNth_revInv (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.contractNth (Fin.castSucc j) (· * ·) (revInv x) =
      revInv (Fin.contractNth (Fin.castSucc j.rev) (· * ·) x) := by
  funext i
  simp only [Fin.contractNth, revInv_apply, Fin.val_castSucc, Fin.val_rev]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | omega
    | (exact congrArg (fun t => (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))
    | (rw [mul_inv_rev]
       exact congrArg₂ (fun s t => (x s)⁻¹ * (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega))
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))

theorem partialProd_last_contractNth (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.partialProd (Fin.contractNth (Fin.castSucc j) (· * ·) x) (Fin.last n) =
      Fin.partialProd x (Fin.last (n + 1)) := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp [Fin.le_def]

theorem contractNth_last (x : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) x = Fin.init x := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl

theorem tail_revInv' (x : Fin (n + 1) → G) :
    (fun i : Fin n => revInv x i.succ) = revInv (Fin.init x) :=
  tail_revInv x

theorem init_revInv' (x : Fin (n + 1) → G) :
    Fin.init (revInv x) = revInv (fun i : Fin n => x i.succ) :=
  init_revInv x

end Tuples

theorem add_add_eq_add_add {M : Type*} [AddCommMonoid M] {a s c b t d : M} (h₁ : a = d)
    (h₂ : c = b) (h₃ : s = t) : a + (s + c) = b + (t + d) := by
  subst h₁ h₂ h₃
  abel

section Cochains

variable {k G : Type u} [CommRing k] [Group G]

def revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) : (Fin n → G) → A :=
  fun x => (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x))

theorem revCochain_apply {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) (x : Fin n → G) :
    revCochain n f x =
      (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x)) :=
  rfl

theorem d_revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) :
    (inhomogeneousCochains.d A n).hom (revCochain n f) =
      revCochain (n + 1) ((inhomogeneousCochains.d A n).hom f) := by
  funext x
  have hP : Fin.partialProd x (Fin.last (n + 1)) =
      x 0 * Fin.partialProd (fun i : Fin n => x i.succ) (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ']
    rfl
  have hP' : Fin.partialProd x (Fin.last (n + 1)) =
      Fin.partialProd (Fin.init x) (Fin.last n) * x (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ, Fin.partialProd_init]
  simp only [inhomogeneousCochains.d_hom_apply, revCochain_apply, Fin.sum_univ_castSucc,
    Fin.val_last, Fin.val_castSucc, contractNth_last, contractNth_revInv,
    partialProd_last_contractNth, tail_revInv', init_revInv', map_add, map_sum, map_smul,
    smul_add, Finset.smul_sum]
  refine add_add_eq_add_add ?_ ?_ ?_
  · rw [← Module.End.mul_apply, ← map_mul, ← hP, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · rw [revInv_apply, Fin.rev_zero, ← Module.End.mul_apply, ← map_mul, hP', mul_inv_cancel_right,
      smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ, Fin.val_rev]
    have := j.isLt
    omega

variable (A : Rep k G)

def revₗ (n : ℕ) : ((Fin n → G) → A) →ₗ[k] ((Fin n → G) → A) where
  toFun := revCochain n
  map_add' f g := by
    funext x
    simp only [revCochain_apply, Pi.add_apply, map_add, smul_add]
  map_smul' c f := by
    funext x
    simp only [revCochain_apply, Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

end Cochains

section Cup

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

theorem braiding_hom_tmul (X Y : Rep k G) (a : X) (b : Y) :
    (β_ X Y).hom.hom ((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G))) = b ⊗ₜ[k] a :=
  rfl

theorem revCochain_cupCochain (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by
  subst h'
  have hpre : (fun i : Fin p => revInv x ⟨i, by omega⟩) =
      revInv (fun j : Fin p => x ⟨q + j, by omega⟩) := by
    funext i
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hsuf : (fun j : Fin q => revInv x ⟨p + j, by omega⟩) =
      revInv (fun i : Fin q => x ⟨i, by omega⟩) := by
    funext j
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hP₁ : Fin.partialProd (revInv x) ⟨p, by omega⟩ =
      (Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p))⁻¹ := by
    rw [← partialProd_prefix (revInv x) (m := p) (by omega) le_rfl, hpre, ← partialProd_last_revInv]
    rfl
  have hP : Fin.partialProd x (Fin.last (q + p)) =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) *
        Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p) := by
    have := partialProd_add x (fun j : Fin p => x ⟨q + j, by omega⟩) (p := q) (q := p)
      le_rfl (fun _ => rfl) le_rfl
    rw [← partialProd_prefix x (m := q) (by omega) le_rfl] at this
    exact this
  have hP₂ : Fin.partialProd x ⟨q, by omega⟩ =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) :=
    (partialProd_prefix x (m := q) (by omega) le_rfl).symm
  rw [revCochain_apply, cupCochain_apply, cupCochain_apply, revCochain_apply, revCochain_apply,
    hpre, hsuf, hP₁, hP₂, map_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    map_smul, braiding_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, hP, mul_inv_cancel_right, smul_smul, ← pow_add, ← pow_add,
    triangle_add]
  congr 2
  ring

end Cup

end GroupCoh

section Profinite

open GroupCoh

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_revInv (n : ℕ) : Continuous (revInv : (Fin n → G) → Fin n → G) :=
  continuous_pi fun i => (continuous_apply _).inv

theorem isLocallyConstant_revCochain {A : Rep.{u} k G} [IsSmoothRep A] (n : ℕ)
    {f : (Fin n → G) → A} (hf : IsLocallyConstant f) : IsLocallyConstant (revCochain n f) :=
  (isLocallyConstant_ρ_apply A ((continuous_apply _).comp (continuous_partialProd n))
    (hf.comp_continuous (continuous_revInv n))).comp _

/-- The reversal of locally constant cochains, as an endomorphism of the complex. -/
def revHom (A : Rep.{u} k G) [IsSmoothRep A] : cochains A ⟶ cochains A where
  f n := ModuleCat.ofHom ((revₗ A n).restrict fun _ hf => isLocallyConstant_revCochain n hf)
  comm' i _ (hij : i + 1 = _) := by
    subst hij
    rw [cochains_d]
    ext f : 2
    apply Subtype.ext
    exact d_revCochain i f.1

theorem revHom_naturality {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (φ : A ⟶ B) :
    revHom A ≫ coeffCochainsMap φ = coeffCochainsMap φ ≫ revHom B := by
  ext n f : 3
  apply Subtype.ext
  funext x
  change φ.hom (revCochain n f.1 x) = revCochain n (fun y => φ.hom (f.1 y)) x
  rw [revCochain_apply, revCochain_apply, map_smul, Rep.hom_comm_apply]

theorem revHom_f_zero (A : Rep.{u} k G) [IsSmoothRep A] : (revHom A).f 0 = 𝟙 _ := by
  ext f : 2
  apply Subtype.ext
  funext x
  change revCochain 0 f.1 x = f.1 x
  rw [revCochain_apply, triangle_zero, pow_zero, one_smul, show Fin.last 0 = 0 from rfl,
    Fin.partialProd_zero, map_one, Module.End.one_apply]
  exact congrArg f.1 (Subsingleton.elim _ _)

theorem homologyMap_eq_id_of_f_eq_id {ι V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {c : ComplexShape ι} {K : HomologicalComplex V c} (φ : K ⟶ K) (i : ι) [K.HasHomology i]
    (h : φ.f i = 𝟙 _) : HomologicalComplex.homologyMap φ i = 𝟙 _ := by
  have hc : HomologicalComplex.cyclesMap φ i = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, h, Category.comp_id,
      Category.id_comp]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, Category.id_comp,
    Category.comp_id]

/-- The reversal of cochains induces the identity on cohomology. -/
theorem homologyMap_revHom [CompactSpace G] (n : ℕ) (A : Rep.{u} k G) [IsSmoothRep A] :
    HomologicalComplex.homologyMap (revHom A) n = 𝟙 _ := by
  induction n generalizing A with
  | zero => exact homologyMap_eq_id_of_f_eq_id _ 0 (revHom_f_zero A)
  | succ n ih =>
    have hS := coindShortComplex_shortExact A
    let Φ : cochainsShortComplex (coindShortComplex A) ⟶
        cochainsShortComplex (coindShortComplex A) :=
      { τ₁ := revHom _
        τ₂ := revHom _
        τ₃ := revHom _
        comm₁₂ := revHom_naturality _
        comm₂₃ := revHom_naturality _ }
    have key := HomologicalComplex.HomologySequence.δ_naturality Φ
      (cochainsShortComplex_shortExact hS) (cochainsShortComplex_shortExact hS) n (n + 1) rfl
    have h3 : HomologicalComplex.homologyMap Φ.τ₃ n = 𝟙 _ := ih _
    rw [h3, Category.id_comp] at key
    have : Epi (δ hS n (n + 1) rfl) := epi_coindδ A n
    refine (cancel_epi (δ hS n (n + 1) rfl)).1 ?_
    exact key.trans (Category.comp_id _).symm

theorem cochainOf_cocycleι_cyclesMap_revHom {A : Rep.{u} k G} [IsSmoothRep A] {n : ℕ}
    (z : cocycles A n) :
    cochainOf A (cocycleι A n (HomologicalComplex.cyclesMap (revHom A) n z)) =
      revCochain n (cochainOf A (cocycleι A n z)) :=
  congrArg (fun ψ => cochainOf A (ψ.hom z)) (HomologicalComplex.cyclesMap_i (revHom A) n)

theorem cohomologyπ_cyclesMap_revHom [CompactSpace G] {A : Rep.{u} k G} [IsSmoothRep A] {n : ℕ}
    (z : cocycles A n) :
    cohomologyπ A n (HomologicalComplex.cyclesMap (revHom A) n z) = cohomologyπ A n z := by
  have h := congr(($(HomologicalComplex.homologyπ_naturality (revHom A) n)).hom z)
  rw [homologyMap_revHom, Category.comp_id] at h
  exact h.symm

variable [CompactSpace G] {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] {p q n : ℕ}

theorem cup_eq_neg_one_pow_smul_coeffMap_braiding (h : p + q = n) (h' : q + p = n)
    (x : cohomology A p) (y : cohomology B q) :
    cup h x y = (-1 : k) ^ (p * q) • coeffMap (β_ B A).hom n (cup h' y x) := by
  induction x using cohomology_induction_on with | h z => ?_
  induction y using cohomology_induction_on with | h w => ?_
  have key : HomologicalComplex.cyclesMap (revHom (A ⊗ B)) n (cupCocycles h z w) =
      (-1 : k) ^ (p * q) • HomologicalComplex.cyclesMap (coeffCochainsMap (β_ B A).hom) n
        (cupCocycles h' (HomologicalComplex.cyclesMap (revHom B) q w)
          (HomologicalComplex.cyclesMap (revHom A) p z)) := by
    apply cocycles_ext
    rw [cochainOf_cocycleι_cyclesMap_revHom, map_smul, cochainOf_smul,
      cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cocycleι_cupCocycles,
      cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant,
      cochainOf_cocycleι_cyclesMap_revHom, cochainOf_cocycleι_cyclesMap_revHom]
    funext x
    exact revCochain_cupCochain h h' _ _ x
  rw [cup_cohomologyπ, ← cohomologyπ_cyclesMap_revHom (cupCocycles h z w), key, map_smul,
    ← cohomologyπ_coeffMap_apply, ← cup_cohomologyπ, cohomologyπ_cyclesMap_revHom,
    cohomologyπ_cyclesMap_revHom]

/-- Graded commutativity of the cup product. -/
theorem coeffMap_braiding_cup (h : p + q = n) (h' : q + p = n) (x : cohomology A p)
    (y : cohomology B q) :
    coeffMap (β_ A B).hom n (cup h x y) = (-1 : k) ^ (p * q) • cup h' y x := by
  rw [cup_eq_neg_one_pow_smul_coeffMap_braiding h' h y x, smul_smul, ← pow_add, mul_comm q p,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

end Profinite

end Langlands.ProfiniteCohomology
