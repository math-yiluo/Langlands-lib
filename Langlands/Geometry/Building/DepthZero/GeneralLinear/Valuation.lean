import Langlands.Geometry.Building.DepthZero.GeneralLinear.Central
import Langlands.Geometry.Building.KPApartment
import Langlands.GroupScheme.ConjugacyBaseChange

/-!
# Valuations of the root datum of the diagonal torus of `GL_N`

Let `A` be apartment data (`KPApartmentData`) for the diagonal torus of `GL_N` over a
nonarchimedean local field `F`, normalized by the order `ω = localFieldOrder F`. A point `x` of
the apartment is a valuation `φ = x.val` of the root datum. This module computes it:

* the root group of `e_k − e_l` consists of all transvections `1 + t E_{kl}`
  (`transvectionPoint_mem_rootGroupPoints`);
* `φ_{kl}(1 + t E_{kl}) = ord(t) + c_{kl}(x)` for `t ≠ 0`, with `c_{kl}(x) = rootValue x k l`
  the value at `t = 1` (`val_transvectionPoint`, from the split-torus part of axiom V 6);
* `c_{lk} = −c_{kl}` (`rootValue_swap`, axiom V 5) and `c_{ik} = c_{ij} + c_{jk}`
  (`rootValue_add`, axiom V 3), so `c_{kl}(x) = y_k − y_l` for real coordinates `y`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {F : Type u} [Field F] {N : ℕ}

instance instMonoDiagTorus : Mono (diagTorus F N).hom.hom.left :=
  mono_of_isMaximalSplitTorus (GeneralLinear.isMaximalSplitTorus_diagonalTorus F)

/-- The rational point of `GL_N` with matrix `1 + t E_{kl}`. -/
def transvectionPoint {k l : Fin N} (hkl : k ≠ l) (t : F) :
    rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  toMatrixGL.symm (transvectionGL hkl t)

theorem transvectionPoint_zero {k l : Fin N} (hkl : k ≠ l) :
    transvectionPoint hkl (0 : F) = 1 := by
  rw [transvectionPoint, transvectionGL_zero, map_one]

theorem transvectionPoint_ne_one {k l : Fin N} (hkl : k ≠ l) {t : F} (ht : t ≠ 0) :
    transvectionPoint hkl t ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) k l) h
  simp only [transvectionPoint, MulEquiv.apply_symm_apply, coe_transvectionGL, map_one,
    Units.val_one, Matrix.add_apply, single_apply_same, one_apply_ne hkl, zero_add] at h1
  exact ht h1

theorem transvectionPoint_mul {k l : Fin N} (hkl : k ≠ l) (s t : F) :
    transvectionPoint hkl s * transvectionPoint hkl t = transvectionPoint hkl (s + t) := by
  apply toMatrixGL.injective
  rw [map_mul]
  simp only [transvectionPoint, MulEquiv.apply_symm_apply]
  ext : 1
  simp only [Units.val_mul, coe_transvectionGL, mul_add, add_mul, mul_one, one_mul,
    single_mul_single_of_ne _ _ _ _ hkl.symm, add_zero, single_add]
  abel

/-- The rational point of the diagonal split torus with coordinates `d`. -/
def torusPoint (d : Fin N → Fˣ) : rationalPoints (diagonalSplitTorus F N).toGrp :=
  (splitTorus.affinePointsEquiv (ULift.{u} (Fin N)) (𝟙 (Spec (CommRingCat.of F)))).symm
    fun a => d a.down

theorem toMatrixGL_map_torusPoint (d : Fin N → Fˣ) :
    toMatrixGL (rationalPoints.map (diagTorus F N) (torusPoint d)) = diagGL d := by
  rw [toMatrixGL_map_diagTorus]
  congr 1
  funext a
  simp [torusPoint]

/-- Conjugation of a transvection by a diagonal torus point. -/
theorem torusPoint_inv_conj_transvectionPoint (d : Fin N → Fˣ) {k l : Fin N} (hkl : k ≠ l)
    (t : F) :
    (rationalPoints.map (diagTorus F N) (torusPoint d))⁻¹ * transvectionPoint hkl t *
        rationalPoints.map (diagTorus F N) (torusPoint d) =
      transvectionPoint hkl (((d k)⁻¹ : Fˣ) * t * (d l : F)) := by
  apply toMatrixGL.injective
  rw [map_mul, map_mul, map_inv, toMatrixGL_map_torusPoint, transvectionPoint,
    transvectionPoint, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, coe_diagGL_inv]
  have h := diagGL_conj_transvectionGL (d⁻¹) hkl t
  rw [coe_diagGL_inv, inv_inv] at h
  rw [h]
  rfl

theorem prod_zpow_single_sub {M : Type*} [CommGroup M] {k l : Fin N} (hkl : k ≠ l)
    (x : ULift.{u} (Fin N) → M) :
    ∏ a, x a ^ ((Pi.single (⟨k⟩ : ULift.{u} (Fin N)) (1 : ℤ) -
      Pi.single (⟨l⟩ : ULift.{u} (Fin N)) 1 : ULift.{u} (Fin N) → ℤ) a) =
      x ⟨k⟩ * (x ⟨l⟩)⁻¹ := by
  have hkl' : (⟨k⟩ : ULift.{u} (Fin N)) ≠ ⟨l⟩ := fun h => hkl (congrArg ULift.down h)
  have h : ∀ a, x a ^ ((Pi.single (⟨k⟩ : ULift.{u} (Fin N)) (1 : ℤ) -
      Pi.single (⟨l⟩ : ULift.{u} (Fin N)) 1 : ULift.{u} (Fin N) → ℤ) a) =
      (if a = ⟨k⟩ then x ⟨k⟩ else 1) * (if a = ⟨l⟩ then (x ⟨l⟩)⁻¹ else 1) := by
    intro a
    by_cases hak : a = ⟨k⟩
    · subst hak
      simp [hkl]
    · by_cases hal : a = ⟨l⟩
      · subst hal
        simp [Ne.symm hkl]
      · simp [hak, hal]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The root character `e_k − e_l` takes the value `d_k / d_l` on the torus point `d`. -/
theorem rationalCharacterEval_rootCharacter_torusPoint {k l : Fin N} (hkl : k ≠ l)
    (d : Fin N → Fˣ) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm
      (rootCharacter (F := F) k l)) (torusPoint d) = d k * (d l)⁻¹ := by
  rw [rootCharacter, SplitTorusValuation.rationalCharacterEval_characterLatticeEquiv_symm,
    prod_zpow_single_sub hkl]
  simp [torusPoint]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem localFieldOrder_inv (t : Fˣ) : localFieldOrder F t⁻¹ = -localFieldOrder F t := by
  simp [localFieldOrder]

theorem localFieldOrder_mul (s t : Fˣ) :
    localFieldOrder F (s * t) = localFieldOrder F s + localFieldOrder F t := by
  simp [localFieldOrder]

variable (A : KPApartmentData (diagTorus F N) (localFieldOrder F))

include A in
/-- Every transvection `1 + t E_{kl}` lies in the root group of `e_k − e_l`. -/
theorem transvectionPoint_mem_rootGroupPoints {k l : Fin N} (hkl : k ≠ l) (t : F) :
    transvectionPoint hkl t ∈ rootGroupPoints (diagTorus F N) (rootCharacter k l) := by
  by_cases ht : t = 0
  · rw [ht, transvectionPoint_zero]
    exact Subgroup.one_mem _
  obtain ⟨x⟩ := (inferInstance : Nonempty A.Apartment)
  have ha := rootCharacter_mem_relativeRoots (F := F) hkl
  obtain ⟨u, hu, hne⟩ := x.isValuation.exists_ne_top ha
  obtain ⟨t₀, ht₀⟩ := exists_eq_transvectionGL_of_mem_rootGroupPoints hkl hu
  have hu' : u = transvectionPoint hkl t₀ := by
    rw [transvectionPoint, ← ht₀, MulEquiv.symm_apply_apply]
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    rw [transvectionPoint_zero] at hu'
    exact hne ((x.isValuation.eq_top_iff _ ha u hu).2 hu')
  let d : Fin N → Fˣ := Pi.mulSingle l (Units.mk0 (t * t₀⁻¹) (mul_ne_zero ht (inv_ne_zero ht₀0)))
  have hconj := torusPoint_inv_conj_transvectionPoint d hkl t₀
  have hdk : (((d k)⁻¹ : Fˣ) : F) = 1 := by simp [d, Pi.mulSingle_eq_of_ne hkl]
  have hdl : (d l : F) = t * t₀⁻¹ := by simp [d]
  rw [hdk, hdl, one_mul, mul_comm t₀, inv_mul_cancel_right₀ ht₀0] at hconj
  subst hu'
  by_contra hnot
  have htop := x.isValuation.eq_top_of_not_mem _ ha _ (hconj ▸ hnot)
  rw [x.isSplitTorusCompatible _ ha (torusPoint d) _ hu] at htop
  exact hne (WithTop.add_eq_top.1 htop |>.resolve_right WithTop.coe_ne_top)

/-- The value `c_{kl}(x) = φ_{kl}(1 + E_{kl})` of the valuation `x` (zero for `k = l`). -/
def rootValue (x : A.Apartment) (k l : Fin N) : ℝ :=
  if h : k = l then 0 else
    WithTop.untopD 0 (x.val (rootCharacter k l) (transvectionPoint h 1))

theorem val_transvectionPoint_one (x : A.Apartment) {k l : Fin N} (hkl : k ≠ l) :
    x.val (rootCharacter k l) (transvectionPoint hkl (1 : F)) =
      ((rootValue A x k l : ℝ) : WithTop ℝ) := by
  have ha := rootCharacter_mem_relativeRoots (F := F) hkl
  have hne : x.val (rootCharacter k l) (transvectionPoint hkl (1 : F)) ≠ ⊤ := fun h =>
    transvectionPoint_ne_one hkl one_ne_zero
      ((x.isValuation.eq_top_iff _ ha _ (transvectionPoint_mem_rootGroupPoints A hkl 1)).1 h)
  simp only [rootValue, hkl, ↓reduceDIte]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr]
  rfl

/-- **The valuation on root groups.** `φ_{kl}(1 + t E_{kl}) = ord(t) + c_{kl}(x)` for `t ≠ 0`. -/
theorem val_transvectionPoint (x : A.Apartment) {k l : Fin N} (hkl : k ≠ l) {t : F}
    (ht : t ≠ 0) :
    x.val (rootCharacter k l) (transvectionPoint hkl t) =
      ((localFieldOrder F (Units.mk0 t ht) + rootValue A x k l : ℝ) : WithTop ℝ) := by
  have ha := rootCharacter_mem_relativeRoots (F := F) hkl
  let d : Fin N → Fˣ := Pi.mulSingle l (Units.mk0 t ht)
  have hconj := torusPoint_inv_conj_transvectionPoint d hkl (1 : F)
  have hdk : (((d k)⁻¹ : Fˣ) : F) = 1 := by simp [d, Pi.mulSingle_eq_of_ne hkl]
  have hdl : (d l : F) = t := by simp [d]
  rw [hdk, hdl, one_mul, one_mul] at hconj
  have h := x.isSplitTorusCompatible _ ha (torusPoint d) _
    (transvectionPoint_mem_rootGroupPoints A hkl 1)
  rw [hconj, val_transvectionPoint_one, rationalCharacterEval_rootCharacter_torusPoint hkl] at h
  rw [h]
  have hdk' : d k = 1 := by simp [d, Pi.mulSingle_eq_of_ne hkl]
  have hdl' : d l = Units.mk0 t ht := by simp [d]
  rw [hdk', hdl', one_mul, localFieldOrder_inv, neg_neg, ← WithTop.coe_add, add_comm]

/-! ### Normalizing points -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Points of the diagonal torus centralize it. -/
theorem map_torusPoint_mem_centralizerPoints (s : rationalPoints (diagonalSplitTorus F N).toGrp) :
    rationalPoints.map (diagTorus F N) s ∈ centralizerPoints (diagTorus F N) := by
  have hcomm : (innerIso (diagonalSplitTorus F N).toGrp s).hom = 𝟙 _ := by
    apply hom_ext_points
    intro U x
    change x ≫ (innerIso (diagonalSplitTorus F N).toGrp s).hom.hom.hom = x ≫ 𝟙 _
    rw [comp_innerIso_hom, Category.comp_id, mul_inv_cancel_comm]
  rw [mem_centralizerPoints, rationalPoints.map_apply, ← innerIso_hom_comp, hcomm,
    Category.id_comp]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem toMatrixGL_permPoint (w : Equiv.Perm (Fin N)) :
    toMatrixGL (GeneralLinear.permPoint (CommRingCat.of F) w) = GeneralLinear.permGL F w := by
  change GeneralLinear.glRingEquiv _ (GeneralLinear.pointsEquiv _ _ _
    ((GeneralLinear.pointsEquiv _ _ _).symm _)) = _
  rw [MulEquiv.apply_symm_apply, GeneralLinear.glRingEquiv_eq_map, GeneralLinear.map_permGL]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `(1 − E_{lk})(1 + E_{kl})(1 − E_{lk})` is the permutation matrix of the transposition of
`k, l` times `diag(−1)` at `k`; in particular it normalizes the diagonal torus. -/
theorem transvectionPoint_rotation_eq {k l : Fin N} (hkl : k ≠ l) :
    transvectionPoint hkl.symm (-1 : F) * transvectionPoint hkl 1 *
        transvectionPoint hkl.symm (-1) =
      GeneralLinear.permPoint (CommRingCat.of F) (Equiv.swap k l) *
        rationalPoints.map (diagTorus F N) (torusPoint (Pi.mulSingle k (-1))) := by
  apply toMatrixGL.injective
  rw [map_mul, map_mul, map_mul, toMatrixGL_permPoint, toMatrixGL_map_torusPoint]
  simp only [transvectionPoint, MulEquiv.apply_symm_apply]
  ext p q : 2
  simp only [Units.val_mul, coe_transvectionGL, GeneralLinear.coe_permGL, coe_diagGL,
    mul_diagonal, GeneralLinear.permMatrix, Matrix.of_apply, mul_add, add_mul, mul_one,
    one_mul, Matrix.add_apply, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hkl,
    add_zero]
  by_cases hpk : p = k <;> by_cases hpl : p = l <;> by_cases hqk : q = k <;>
    by_cases hql : q = l <;>
    simp_all [one_apply, Equiv.swap_apply_def, Ne.symm hkl,
      @eq_comm _ k, @eq_comm _ l]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem transvectionPoint_rotation_mem_normalizerPoints {k l : Fin N} (hkl : k ≠ l) :
    transvectionPoint hkl.symm (-1 : F) * transvectionPoint hkl 1 *
        transvectionPoint hkl.symm (-1) ∈ normalizerPoints (diagTorus F N) := by
  rw [transvectionPoint_rotation_eq hkl]
  exact (normalizerPoints _).mul_mem (GeneralLinear.permNormalizer F (Equiv.swap k l)).2
    (centralizerPoints_le_normalizerPoints _ (map_torusPoint_mem_centralizerPoints _))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem neg_rootCharacter (k l : Fin N) :
    -rootCharacter (F := F) k l = rootCharacter l k := by
  apply (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).injective
  rw [map_neg, characterLatticeEquiv_rootCharacter, characterLatticeEquiv_rootCharacter,
    neg_sub]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rootCharacter_add (i j k : Fin N) :
    rootCharacter (F := F) i j + rootCharacter j k = rootCharacter i k := by
  apply (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).injective
  rw [map_add, characterLatticeEquiv_rootCharacter, characterLatticeEquiv_rootCharacter,
    characterLatticeEquiv_rootCharacter]
  abel

theorem localFieldOrder_neg_one : localFieldOrder F (-1) = 0 := by
  have h := localFieldOrder_mul (F := F) (-1) (-1)
  rw [neg_one_mul, neg_neg] at h
  have h1 : localFieldOrder F 1 = 0 := by simp [localFieldOrder]
  rw [h1] at h
  linarith

/-! ### Antisymmetry and additivity of the root values -/

/-- Axiom V 5: `c_{lk}(x) = −c_{kl}(x)`. -/
theorem rootValue_swap (x : A.Apartment) (k l : Fin N) :
    rootValue A x l k = -rootValue A x k l := by
  by_cases hkl : k = l
  · subst hkl
    simp [rootValue]
  have ha := rootCharacter_mem_relativeRoots (F := F) hkl
  have hu := transvectionPoint_mem_rootGroupPoints A hkl (1 : F)
  have hu' := transvectionPoint_mem_rootGroupPoints A (Ne.symm hkl) (-1 : F)
  rw [← neg_rootCharacter] at hu'
  have h := x.isValuation.opposite _ ha _ hu (transvectionPoint_ne_one hkl one_ne_zero) _ hu' _
    hu' (transvectionPoint_rotation_mem_normalizerPoints hkl)
  rw [neg_rootCharacter, val_transvectionPoint A x (Ne.symm hkl) (neg_ne_zero.2 one_ne_zero),
    val_transvectionPoint_one] at h
  have h1 : localFieldOrder F (Units.mk0 (-1 : F) (neg_ne_zero.2 one_ne_zero)) = 0 := by
    rw [show Units.mk0 (-1 : F) (neg_ne_zero.2 one_ne_zero) = -1 by ext; simp]
    exact localFieldOrder_neg_one
  rw [h1, zero_add, ← WithTop.coe_add, WithTop.coe_eq_zero] at h
  linarith

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem transvectionPoint_inv {k l : Fin N} (hkl : k ≠ l) (t : F) :
    (transvectionPoint hkl t)⁻¹ = transvectionPoint hkl (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [transvectionPoint_mul, add_neg_cancel, transvectionPoint_zero]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The commutator of `1 + E_{ij}` and `1 + E_{jk}` is `1 + E_{ik}`. -/
theorem commutatorElement_transvectionPoint {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ⁅transvectionPoint hij (1 : F), transvectionPoint hjk (1 : F)⁆ =
      transvectionPoint hik (1 : F) := by
  rw [commutatorElement_def, transvectionPoint_inv, transvectionPoint_inv]
  apply toMatrixGL.injective
  simp only [map_mul, transvectionPoint, MulEquiv.apply_symm_apply]
  ext : 1
  simp only [Units.val_mul, coe_transvectionGL, mul_add, add_mul, mul_one, one_mul,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hij.symm,
    single_mul_single_of_ne _ _ _ _ hik.symm, single_mul_single_of_ne _ _ _ _ hjk.symm,
    add_zero]
  simp only [mul_neg, mul_one, neg_neg, ← single_neg]
  abel

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `p (e_i − e_j) + q (e_j − e_k)` is a root with `p, q > 0`, then `p = q = 1`. -/
theorem eq_one_of_nsmul_add_nsmul_mem {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : p • rootCharacter (F := F) i j + q • rootCharacter j k ∈
      relativeRoots (diagTorus F N)) : p = 1 ∧ q = 1 := by
  obtain ⟨m, m', -, heq⟩ := exists_eq_rootCharacter h
  have hc := congrArg (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))) heq
  rw [map_add, map_nsmul, map_nsmul, characterLatticeEquiv_rootCharacter,
    characterLatticeEquiv_rootCharacter, characterLatticeEquiv_rootCharacter] at hc
  have hi := congrFun hc ⟨i⟩
  have hk := congrFun hc ⟨k⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, ULift.up_inj,
    hij, hik, Ne.symm hik, Ne.symm hjk, ↓reduceIte] at hi hk
  simp only [nsmul_eq_mul, sub_zero, zero_sub, sub_self, mul_one, mul_zero, add_zero, zero_add,
    mul_neg] at hi hk
  constructor <;> split_ifs at hi hk <;> omega

/-- Axiom V 3: `c_{ij}(x) + c_{jk}(x) ≤ c_{ik}(x)` for distinct `i, j, k`. -/
theorem rootValue_add_le (x : A.Apartment) {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : rootValue A x i j + rootValue A x j k ≤ rootValue A x i k := by
  have ha := rootCharacter_mem_relativeRoots (F := F) hij
  have hb := rootCharacter_mem_relativeRoots (F := F) hjk
  have hcomm := x.isValuation.commutator _ ha _ hb (fun t _ h => by
      have h' := congrArg (fun v => RealTorusSpace.pair (diagonalSplitTorus F N) v
        ((1 : ℝ) ⊗ₜ[ℤ] (splitTorus.cocharacterLatticeEquiv F (ULift.{u} (Fin N))).symm
          (Pi.single ⟨k⟩ 1))) h
      simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
        RealTorusSpace.pair_tmul_tmul, latticePairing_rootCharacter] at h'
      have hk' : (⟨i⟩ : ULift.{u} (Fin N)) ≠ ⟨k⟩ := fun e => hik (congrArg ULift.down e)
      have hj' : (⟨j⟩ : ULift.{u} (Fin N)) ≠ ⟨k⟩ := fun e => hjk (congrArg ULift.down e)
      simp [Pi.single_eq_of_ne hk', Pi.single_eq_of_ne hj'] at h')
    (rootValue A x i j) (rootValue A x j k)
  have hu1 : transvectionPoint hij (1 : F) ∈
      rootFiltration (diagTorus F N) x.val (rootCharacter i j) (rootValue A x i j) :=
    ⟨transvectionPoint_mem_rootGroupPoints A hij 1, (val_transvectionPoint_one A x hij).ge⟩
  have hu2 : transvectionPoint hjk (1 : F) ∈
      rootFiltration (diagTorus F N) x.val (rootCharacter j k) (rootValue A x j k) :=
    ⟨transvectionPoint_mem_rootGroupPoints A hjk 1, (val_transvectionPoint_one A x hjk).ge⟩
  have hmem := hcomm (Subgroup.commutator_mem_commutator (Subgroup.subset_closure hu1)
    (Subgroup.subset_closure hu2))
  rw [commutatorElement_transvectionPoint hij hjk hik] at hmem
  have hle : Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
      (_ : p • rootCharacter (F := F) i j + q • rootCharacter j k ∈
        relativeRoots (diagTorus F N)),
      rootFiltration (diagTorus F N) x.val (p • rootCharacter i j + q • rootCharacter j k)
        (p * rootValue A x i j + q * rootValue A x j k)) ≤
      x.isValuation.filtrationSubgroup (rootCharacter i k)
        (rootValue A x i j + rootValue A x j k) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨p, q, hp, hq, hroot, hg⟩ := hg
    obtain ⟨rfl, rfl⟩ := eq_one_of_nsmul_add_nsmul_mem hij hjk hik hp hq hroot
    simpa only [one_smul, rootCharacter_add, Nat.cast_one, one_mul,
      IsRootDatumValuation.coe_filtrationSubgroup] using hg
  have h2 := (hle hmem).2
  rw [val_transvectionPoint_one A x hik] at h2
  exact_mod_cast h2

/-- `c_{ik}(x) = c_{ij}(x) + c_{jk}(x)` for all `i, j, k`. -/
theorem rootValue_add (x : A.Apartment) (i j k : Fin N) :
    rootValue A x i k = rootValue A x i j + rootValue A x j k := by
  by_cases hij : i = j
  · subst hij
    simp [rootValue]
  by_cases hjk : j = k
  · subst hjk
    simp [rootValue]
  by_cases hik : i = k
  · subst hik
    rw [rootValue_swap A x i j]
    simp [rootValue]
  have h1 := rootValue_add_le A x hij hjk hik
  have h2 := rootValue_add_le A x (Ne.symm hjk) (Ne.symm hij) (Ne.symm hik)
  rw [rootValue_swap A x j k, rootValue_swap A x i j, rootValue_swap A x i k] at h2
  linarith

/-- **Coordinates of a point of the apartment.** There are real numbers `y_k` with
`c_{kl}(x) = y_k − y_l`. -/
theorem exists_rootValue_eq_sub (x : A.Apartment) :
    ∃ y : Fin N → ℝ, ∀ k l, rootValue A x k l = y k - y l := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨fun _ => 0, fun k => k.elim0⟩
  refine ⟨fun m => rootValue A x m ⟨0, hN⟩, fun k l => ?_⟩
  rw [rootValue_add A x k ⟨0, hN⟩ l, rootValue_swap A x l ⟨0, hN⟩]
  ring

end Langlands.Geometry.Building.GeneralLinearParahoric
