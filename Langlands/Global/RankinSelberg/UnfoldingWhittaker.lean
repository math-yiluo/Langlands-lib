import Langlands.Global.RankinSelberg.WhittakerIntegrals
import Langlands.Global.PrimitiveAdelicUnipotent
import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates

/-! # Unitriangular facts for the unfolding of unequal-rank integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

local instance whittakerUnfoldingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance whittakerUnfoldingSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

open PrimitiveAdelicHeight in
/-- The block unipotent subgroup for the weights `i ↦ -i` consists of the upper
unitriangular matrices. -/
theorem mem_blockUnipotentSubgroup_upperUnipotentWeight_iff {A : Type*} [CommRing A] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ GroupScheme.GeneralLinear.blockUnipotentSubgroup A (upperUnipotentWeight n) ↔
      IsUnitriangular (g : Matrix (Fin n) (Fin n) A) := by
  rw [GroupScheme.GeneralLinear.mem_blockUnipotentSubgroup]
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : j < i := hij
      have hw : upperUnipotentWeight n i ≤ upperUnipotentWeight n j := by
        simp only [upperUnipotentWeight, neg_le_neg_iff, Nat.cast_le]
        exact hij'.le
      rw [h i j hw, Matrix.one_apply_ne hij'.ne']
    · rw [h i i le_rfl, Matrix.one_apply_eq]
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upperUnipotentWeight, neg_le_neg_iff, Nat.cast_le] at hij
    rcases (Fin.le_iff_val_le_val.mpr hij).lt_or_eq with hlt | heq
    · rw [h1 hlt, Matrix.one_apply_ne hlt.ne']
    · subst heq
      rw [h2 j, Matrix.one_apply_eq]

variable (F : Type u) [Field F] [NumberField F]

open PrimitiveAdelicHeight in
/-- An adelic point lies in `N_n(𝔸)` exactly when its matrix is upper unitriangular. -/
theorem mem_unipotentAdelic_iff {n : ℕ} (x : Points F n) :
    x ∈ unipotentAdelic F n ↔
      IsUnitriangular ((GeneralLinearGroupPoints.adelicEquiv F n x :
        Matrix.GeneralLinearGroup (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F)) := by
  rw [← mem_blockUnipotentSubgroup_upperUnipotentWeight_iff]
  exact GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff
    (CommRingCat.of F) (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (upperUnipotentWeight n) x

omit [NumberField F] in
open PrimitiveAdelicHeight in
/-- A rational point lies in `N_n(F)` exactly when its matrix is upper unitriangular. -/
theorem mem_rationalPoints_upperUnipotent_iff {n : ℕ}
    (x : RationalGroupPoints F (Scheme F n)) :
    x ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F n) (upperUnipotent F n) ↔
      IsUnitriangular ((GeneralLinearGroupPoints.rationalEquiv F n x :
        Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [← mem_blockUnipotentSubgroup_upperUnipotentWeight_iff]
  exact GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff
    (CommRingCat.of F) (CommAlgCat.of F F) (upperUnipotentWeight n) x

/-- A unitriangular matrix as an invertible matrix, with the adjugate as inverse. -/
def unitriangularUnit {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hM : PrimitiveAdelicHeight.IsUnitriangular M) : Matrix.GeneralLinearGroup (Fin n) R where
  val := M
  inv := M.adjugate
  val_inv := by rw [Matrix.mul_adjugate, hM.det_eq_one, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, hM.det_eq_one, one_smul]

open PrimitiveAdelicHeight in
/-- `N_n(F) \ N_n(𝔸)` is compact, by the rational reduction of adelic unitriangular
matrices into a compact set. -/
theorem compactSpace_unipotentRationalQuotient (n : ℕ) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F (Scheme F n) (upperUnipotent F n)) := by
  obtain ⟨Ω, hΩc, hΩu, hred⟩ := exists_isCompact_unitriangular_reduction F n
  let f : Ω → Matrix.GeneralLinearGroup (Fin n) (Adeles F) := fun M =>
    unitriangularUnit (M : Matrix (Fin n) (Fin n) (Adeles F)) (hΩu M M.property)
  have hf : Continuous f :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  let K : Set (unipotentAdelic F n) :=
    Subtype.val ⁻¹' (GeneralLinearGroupPoints.adelicHomeomorph F n ⁻¹' Set.range f)
  have hK : IsCompact K :=
    (isClosed_upperUnipotent_adelicPoints F n).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).isCompact_preimage.mpr
        (isCompact_range hf))
  have hsurj : LeftCosetSpace.mk
      (AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)) '' K =
        Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    have hu := (mem_unipotentAdelic_iff F u.val).mp u.property
    obtain ⟨c, hc, hcΩ⟩ := hred _ hu
    let γ0 : RationalGroupPoints F (Scheme F n) :=
      (GeneralLinearGroupPoints.rationalEquiv F n).symm (unitriangularUnit c hc)
    have hγ0 : γ0 ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F n) (upperUnipotent F n) := by
      rw [mem_rationalPoints_upperUnipotent_iff]
      simpa [γ0, unitriangularUnit] using hc
    let γ : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) :=
      ⟨AdelicSubgroupPoints.rational F _ _ ⟨γ0, hγ0⟩, ⟨_, rfl⟩⟩
    refine ⟨(γ : unipotentAdelic F n) * u, ?_, LeftCosetSpace.mk_subgroup_mul _ γ u⟩
    refine ⟨⟨_, hcΩ⟩, ?_⟩
    apply Units.ext
    change c.map (algebraMap F (Adeles F)) * _ =
      ((GeneralLinearGroupPoints.adelicEquiv F n
        (AdelicGroupPoints.rational F (Scheme F n) γ0 * u.val) :
          Matrix.GeneralLinearGroup (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))
    rw [map_mul, Units.val_mul, GeneralLinearGroupPoints.adelicEquiv_rational]
    congr 1
    ext i j
    simp [γ0, unitriangularUnit]
  refine ⟨?_⟩
  rw [← hsurj]
  exact hK.image (LeftCosetSpace.continuous_mk _)

section Superdiagonal

open PrimitiveAdelicHeight

/-- Superdiagonal entries add under multiplication of upper unitriangular matrices. -/
theorem superdiag_mul_of_isUnitriangular {R : Type*} [CommRing R] {r : ℕ}
    {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) (i : Fin r) :
    (A * B) i.castSucc i.succ = A i.castSucc i.succ + B i.castSucc i.succ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne]
  · rw [hA.2, hB.2, one_mul, mul_one, add_comm]
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · exact mul_eq_zero_of_left (hA.1 hlt) _
    · have hk : i.succ < k :=
        lt_of_le_of_ne (Fin.castSucc_lt_iff_succ_le.mp hgt) (Ne.symm hk2)
      exact mul_eq_zero_of_right _ (hB.1 hk)

end Superdiagonal

section GenericCharacter

open PrimitiveAdelicHeight

/-- The matrix of an element of `N_n(𝔸)` is upper unitriangular. -/
theorem isUnitriangular_of_mem_unipotentAdelic {n : ℕ} (x : unipotentAdelic F n) :
    IsUnitriangular ((GeneralLinearGroupPoints.adelicEquiv F n (x : Points F n) :
      Matrix.GeneralLinearGroup (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F)) :=
  (mem_unipotentAdelic_iff F x.val).mp x.property

/-- The generic character is multiplicative on `N_(r+1)(𝔸)`. -/
theorem genericCharacter_mul (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (m : Fin r → F)
    (x y : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ m (x * y) = genericCharacter F r ψ m x * genericCharacter F r ψ m y := by
  simp only [genericCharacter]
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subgroup.coe_mul, map_mul, Units.val_mul,
    superdiag_mul_of_isUnitriangular (isUnitriangular_of_mem_unipotentAdelic F x)
      (isUnitriangular_of_mem_unipotentAdelic F y), mul_add]

/-- The generic character is trivial on `N_(r+1)(F)` when `ψ` is trivial on `F`. -/
theorem genericCharacter_rational (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (m : Fin r → F)
    (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1))) :
    genericCharacter F r ψ m k = 1 := by
  obtain ⟨q, hq⟩ := k.property
  simp only [genericCharacter]
  rw [← hq, AdelicSubgroupPoints.rational_coe, GeneralLinearGroupPoints.adelicEquiv_rational]
  simp only [AdelicGL.rational_apply]
  simp_rw [← map_mul, ← map_sum]
  exact hψ _

/-- The generic character of a unitary `ψ` takes values of norm one. -/
theorem norm_genericCharacter (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1) (m : Fin r → F) (x : unipotentAdelic F (r + 1)) :
    ‖genericCharacter F r ψ m x‖ = 1 :=
  hψ _

/-- The generic character of a continuous `ψ` is continuous. -/
theorem continuous_genericCharacter (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (m : Fin r → F) : Continuous (genericCharacter F r ψ m) := by
  have he : Continuous (GeneralLinearGroupPoints.adelicEquiv F (r + 1)) :=
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous
  have h1 : Continuous fun x : unipotentAdelic F (r + 1) =>
      ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (x : Points F (r + 1)) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) :=
    Units.continuous_val.comp (he.comp continuous_subtype_val)
  exact hψ.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (h1.matrix_elem _ _))

/-- The generic character of `ψ⁻¹` is the complex conjugate of that of a unitary `ψ`. -/
theorem genericCharacter_inv (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1) (m : Fin r → F) (x : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ⁻¹ m x = starRingEnd ℂ (genericCharacter F r ψ m x) := by
  simp only [genericCharacter]
  rw [AddChar.inv_apply', Complex.inv_eq_conj (hψ _)]

end GenericCharacter

section CuspFunctions

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Evaluation of a continuous rational-invariant function is continuous. -/
theorem continuous_evaluate (f : Automorphic.GroupSchemeFunctions.ContinuousRationalFunctions F G) :
    Continuous (Automorphic.GroupSchemeFunctions.evaluate F G f) :=
  f.property

/-- Evaluation of a continuous rational-invariant function is left invariant under the
rational points. -/
theorem evaluate_rational_mul (f : Automorphic.GroupSchemeFunctions.ContinuousRationalFunctions F G)
    (k : AdelicGroupPoints.rationalSubgroup F G) (x : AdelicGroupPoints F G) :
    Automorphic.GroupSchemeFunctions.evaluate F G f ((k : AdelicGroupPoints F G) * x) =
      Automorphic.GroupSchemeFunctions.evaluate F G f x := by
  obtain ⟨q, hq⟩ := k.property
  rw [← hq]
  exact f.val.property q x

end CuspFunctions

end Langlands.Global.RankinSelbergGlobal.Unfolding
