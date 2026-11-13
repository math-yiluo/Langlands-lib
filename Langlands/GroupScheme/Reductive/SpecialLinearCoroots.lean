import Langlands.GroupScheme.Reductive.SpecialLinearRoots
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Coroots of the diagonal torus of `SL_{n+1}` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ}

/-! ### Integer coordinates -/

section Coords

/-- The sum-zero function `y ↦ [y = p] - [y = q]` on `Fin (n + 1)`. -/
def delta (p q : Fin (n + 1)) : Fin (n + 1) → ℤ :=
  fun y => (if y = p then 1 else 0) - (if y = q then 1 else 0)

theorem sum_delta (p q : Fin (n + 1)) : ∑ y, delta p q y = 0 := by
  simp only [delta, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sub_self]

/-- The weights `w(p)` sum to zero. -/
theorem sum_weightCoord_eq_zero : ∑ p : Fin (n + 1), weightCoord n p = 0 := by
  funext c
  rw [Finset.sum_apply, sum_weightCoord, Pi.zero_apply]

/-- The dot product of the weight `w(x)` with the vector `c ↦ h(castSucc c)`. -/
theorem sum_weightCoord_mul (h : Fin (n + 1) → ℤ) (x : Fin (n + 1)) :
    ∑ c : Fin n, weightCoord n x c * h c.castSucc =
      h x - if x = Fin.last n then ∑ y, h y else 0 := by
  induction x using Fin.lastCases with
  | last =>
    simp only [weightCoord_last, ↓reduceIte, Fin.sum_univ_castSucc, neg_one_mul,
      Finset.sum_neg_distrib]
    ring
  | cast a =>
    rw [weightCoord_castSucc, ite_eq_right (Fin.castSucc_lt_last a).ne, sub_zero,
      Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul])
        (by simp), Pi.single_eq_same, one_mul]

/-- `∑_p (w(castSucc c) - w(p)) = (n + 1) e_c`. -/
theorem sum_weightCoord_sub (c : Fin n) :
    ∑ p : Fin (n + 1), (weightCoord n c.castSucc - weightCoord n p) =
      ((n : ℤ) + 1) • Pi.single c 1 := by
  funext d
  simp only [Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, sum_weightCoord, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.smul_apply,
    smul_eq_mul, weightCoord_castSucc]
  push_cast
  ring

theorem sum_weightCoord_mul_of_sum_eq_zero {h : Fin (n + 1) → ℤ} (hh : ∑ y, h y = 0)
    (x : Fin (n + 1)) :
    ∑ c : Fin n, weightCoord n x c * h c.castSucc = h x := by
  rw [sum_weightCoord_mul, hh, ite_self, sub_zero]

/-- **Reflection identity.** `w(x) - ([x = p] - [x = q]) (w(p) - w(q)) = w(σ x)` for the
transposition `σ` of `p` and `q`. -/
theorem weightCoord_sub_delta_smul (p q x : Fin (n + 1)) :
    weightCoord n x - delta p q x • (weightCoord n p - weightCoord n q) =
      weightCoord n (Equiv.swap p q x) := by
  by_cases hpq : p = q
  · subst hpq
    simp [delta]
  by_cases hxp : x = p
  · subst hxp
    simp [delta, hpq]
  by_cases hxq : x = q
  · subst hxq
    simp [delta, Ne.symm hpq]
  · simp [delta, hxp, hxq, Equiv.swap_apply_of_ne_of_ne hxp hxq]

end Coords

/-! ### Characters and cocharacters over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

theorem rootChar_self (p : Fin (n + 1)) : rootChar n k p p = 0 := by
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rw [characterCoordEquiv_rootChar, sub_self, map_zero]

theorem rootChar_add_rootChar (x y z : Fin (n + 1)) :
    rootChar n k x y + rootChar n k y z = rootChar n k x z := by
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rw [map_add, characterCoordEquiv_rootChar, characterCoordEquiv_rootChar,
    characterCoordEquiv_rootChar, sub_add_sub_cancel]

/-- The reflection of the root `w(x) - w(y)` along `w(p) - w(q)`. -/
theorem rootChar_sub_smul_rootChar (p q x y : Fin (n + 1)) :
    rootChar n k x y - (delta p q x - delta p q y) • rootChar n k p q =
      rootChar n k (Equiv.swap p q x) (Equiv.swap p q y) := by
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rw [map_sub, map_zsmul, characterCoordEquiv_rootChar, characterCoordEquiv_rootChar,
    characterCoordEquiv_rootChar, ← weightCoord_sub_delta_smul p q x,
    ← weightCoord_sub_delta_smul p q y, sub_smul]
  abel

variable (n k) in
/-- The cocharacter with coordinates `c ↦ h(castSucc c)`. -/
def cochar (h : Fin (n + 1) → ℤ) : cocharacterLattice 𝔻 :=
  (GeneralLinear.cocharacterCoordEquiv (Fin n) k).symm (fun c => h c.castSucc)

theorem cocharacterCoordEquiv_cochar (h : Fin (n + 1) → ℤ) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) k (cochar n k h) = fun c => h c.castSucc :=
  LinearEquiv.apply_symm_apply _ _

/-- For a sum-zero `h`, the root `w(x) - w(y)` pairs with `cochar h` to `h(x) - h(y)`. -/
theorem latticePairing_rootChar_cochar (x y : Fin (n + 1)) {h : Fin (n + 1) → ℤ}
    (hh : ∑ z, h z = 0) :
    latticePairing 𝔻 (rootChar n k x y) (cochar n k h) = h x - h y := by
  rw [GeneralLinear.latticePairing_coord, characterCoordEquiv_rootChar,
    cocharacterCoordEquiv_cochar]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [sum_weightCoord_mul_of_sum_eq_zero hh, sum_weightCoord_mul_of_sum_eq_zero hh]

variable (n k) in
/-- The cocharacter `u(p) - u(q)`, the coroot of `w(p) - w(q)`. -/
def corootChar (p q : Fin (n + 1)) : cocharacterLattice 𝔻 :=
  cochar n k (delta p q)

theorem latticePairing_rootChar_corootChar (x y p q : Fin (n + 1)) :
    latticePairing 𝔻 (rootChar n k x y) (corootChar n k p q) = delta p q x - delta p q y :=
  latticePairing_rootChar_cochar x y (sum_delta p q)

theorem cocharacterCoordEquiv_corootChar_last (a : Fin n) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) k (corootChar n k a.castSucc (Fin.last n)) =
      Pi.single a 1 := by
  rw [corootChar, cocharacterCoordEquiv_cochar]
  funext c
  simp only [delta, Fin.castSucc_inj, ite_eq_right (Fin.castSucc_lt_last c).ne, sub_zero,
    Pi.single_apply]

/-! ### Coroots of a root datum of the diagonal torus -/

/-- The roots of a root datum of the diagonal torus are the `w(p) - w(q)` with `p ≠ q`. -/
theorem mem_range_root_iff {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    (χ : characterLattice 𝔻) :
    χ ∈ Set.range P.root ↔ ∃ p q : Fin (n + 1), p ≠ q ∧ χ = rootChar n k p q := by
  rw [hP.2.1, mem_roots_iff]
  refine exists_congr fun p => exists_congr fun q => and_congr_right fun _ => ?_
  rw [← characterCoordEquiv_rootChar (k := k)]
  exact (GeneralLinear.characterCoordEquiv (Fin n) k).injective.eq_iff

/-- `(n + 1) χ` lies in the span of the roots: `(n + 1) e_c = ∑_p (w(c) - w(p))`. -/
theorem smul_mem_span_root {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    (χ : characterLattice 𝔻) :
    ((n : ℤ) + 1) • χ ∈ Submodule.span ℤ (Set.range P.root) := by
  have key : ((n : ℤ) + 1) • χ = ∑ c : Fin n, GeneralLinear.characterCoordEquiv (Fin n) k χ c •
      ∑ p : Fin (n + 1), rootChar n k c.castSucc p := by
    apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
    simp only [map_sum, map_zsmul, characterCoordEquiv_rootChar, sum_weightCoord_sub]
    funext d
    simp [Finset.sum_apply, Pi.single_apply]
    ring
  rw [key]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ => ?_)
  by_cases h : c.castSucc = p
  · rw [h, rootChar_self]
    exact zero_mem _
  · exact Submodule.subset_span ((mem_range_root_iff hP _).mpr ⟨_, _, h, rfl⟩)

/-- **Coroots.** In a root datum of the diagonal torus, the coroot of `w(p) - w(q)` is
`u(p) - u(q)`. -/
theorem coroot_eq_corootChar {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    {j : J} {p q : Fin (n + 1)} (hj : P.root j = rootChar n k p q) :
    P.coroot j = corootChar n k p q := by
  have hpq : p ≠ q := by
    rintro rfl
    exact P.ne_zero j (hj.trans (rootChar_self p))
  have : IsAddTorsionFree (characterLattice 𝔻) :=
    Function.Injective.isAddTorsionFree
      (GeneralLinear.characterCoordEquiv (Fin n) k).toLinearMap.toAddMonoidHom
      (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  let g : Module.Dual ℤ (characterLattice 𝔻) := P.toLinearMap.flip (corootChar n k p q)
  have hg1 : g (P.root j) = 2 := by
    change P.toLinearMap (P.root j) (corootChar n k p q) = 2
    rw [hP.1, hj, latticePairing_rootChar_corootChar]
    simp [delta, hpq, Ne.symm hpq]
  have hg2 : Set.MapsTo (Module.preReflection (P.root j) g) (Set.range P.root)
      (Set.range P.root) := by
    intro χ hχ
    obtain ⟨x, y, hxy, rfl⟩ := (mem_range_root_iff hP χ).mp hχ
    rw [Module.preReflection_apply]
    change rootChar n k x y - P.toLinearMap (rootChar n k x y) (corootChar n k p q) • P.root j
      ∈ _
    rw [hP.1, latticePairing_rootChar_corootChar, hj, rootChar_sub_smul_rootChar]
    exact (mem_range_root_iff hP _).mpr ⟨_, _, (Equiv.swap p q).injective.ne hxy, rfl⟩
  have heq := Module.Dual.eq_of_preReflection_mapsTo' (Set.finite_range P.root)
    (Submodule.subset_span (Set.mem_range_self j)) (P.coroot_root_two j)
    (P.mapsTo_reflection_root j) hg1 hg2
  have hfg : ∀ χ, P.toLinearMap χ (P.coroot j) = P.toLinearMap χ (corootChar n k p q) := by
    intro χ
    have h := LinearMap.congr_fun heq ⟨_, smul_mem_span_root hP χ⟩
    simp only [LinearMap.dualMap_apply, Submodule.subtype_apply, LinearMap.flip_apply,
      map_zsmul, smul_eq_mul] at h
    exact mul_left_cancel₀ (by omega) h
  apply P.flip.toPerfPair.injective
  ext χ
  exact hfg χ

/-- **Coroot span.** The coroots of a root datum of the diagonal torus span the cocharacter
lattice: the coroots `u(castSucc a) - u(last)` form its coordinate basis. -/
theorem corootSpan_eq_top {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) :
    P.corootSpan ℤ = ⊤ := by
  rw [eq_top_iff,
    ← ((Pi.basisFun ℤ (Fin n)).map (GeneralLinear.cocharacterCoordEquiv (Fin n) k).symm).span_eq,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨j, hj⟩ := (mem_range_root_iff hP (rootChar n k a.castSucc (Fin.last n))).mpr
    ⟨_, _, (Fin.castSucc_lt_last a).ne, rfl⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, ← cocharacterCoordEquiv_corootChar_last (k := k),
    LinearEquiv.symm_apply_apply, ← coroot_eq_corootChar hP hj]
  exact Submodule.subset_span ⟨j, rfl⟩

end Field

end Langlands.GroupScheme.SpecialLinear.FinSucc
