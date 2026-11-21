import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanPlaceLie
import Langlands.Representation.Archimedean.ComplexJacquetChart
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# Smooth Iwasawa factors near the mixed archimedean identity

The real and complex matrix Iwasawa charts assemble in the actual mixed
coordinates. Their local upper and compact factors have the expected
matrix properties and are smooth at the identity.
-/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.ArchimedeanGL

open NumberField
open Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "A" => ArchimedeanMatrix F n
local notation "C" => ((RP → RM) × (CP → CM))

/-- The actual mixed matrix algebra, with its real smooth structure, in place
matrix coordinates. -/
def matrixPlaceCoordinates : A ≃L[ℝ] C :=
  ((realLieAlgebraToMatrix F n).symm.trans
    (realLiePlaceCoordinates F n).toLinearEquiv).toContinuousLinearEquiv

@[simp]
theorem matrixPlaceCoordinates_symm_apply (r : RP → RM) (c : CP → CM) :
    (matrixPlaceCoordinates F n).symm (r, c) = assembleMatrix F n r c := rfl

private def realProjection (v : RP) : A →L[ℝ] RM :=
  ((realPlaceScalarProjection F v).mapMatrix).toLinearMap.toContinuousLinearMap

private def complexProjection (v : CP) : A →L[ℝ] CM :=
  ((complexPlaceScalarProjection F v).mapMatrix).toLinearMap.toContinuousLinearMap

private theorem realProjection_one (v : RP) : realProjection F n v 1 = 1 :=
  ((realPlaceScalarProjection F v).mapMatrix).map_one

private theorem complexProjection_one (v : CP) : complexProjection F n v 1 = 1 :=
  ((complexPlaceScalarProjection F v).mapMatrix).map_one

omit [NumberField F] in
private theorem assembleMatrix_star (r : RP → RM) (c : CP → CM) :
    star (assembleMatrix F n r c) =
      assembleMatrix F n (fun v => star (r v)) (fun v => star (c v)) := rfl

omit [NumberField F] in
private theorem assembleMatrix_mem_unitary (r : RP → RM) (c : CP → CM)
    (hr : ∀ v, r v ∈ unitary RM) (hc : ∀ v, c v ∈ unitary CM) :
    assembleMatrix F n r c ∈ unitary A := by
  rw [Unitary.mem_iff, assembleMatrix_star, assembleMatrix_mul, assembleMatrix_mul]
  constructor
  · simp only [Unitary.star_mul_self_of_mem (hr _), Unitary.star_mul_self_of_mem (hc _),
      assembleMatrix_one]
  · simp only [Unitary.mul_star_self_of_mem (hr _), Unitary.mul_star_self_of_mem (hc _),
      assembleMatrix_one]

set_option maxHeartbeats 650000 in
omit [NumberField F] in
/-- The standard infinite compact corresponds to the unitary subgroup of the
mixed archimedean matrix algebra. -/
theorem mem_standardInfiniteCompact_iff_mem_unitary (g : InfiniteAdelicGL F n) :
    g ∈ standardInfiniteCompact F n ↔ (archimedeanGLCoordinates F n g).val ∈ unitary A := by
  rw [mem_standardInfiniteCompact_iff]
  constructor
  · rintro ⟨hr, hc⟩
    exact assembleMatrix_mem_unitary F n _ _ hr hc
  · intro hg
    constructor
    · intro v
      let p : A →⋆* RM :=
        { ((realPlaceScalarProjection F v).mapMatrix).toMonoidHom with
          map_star' := fun _ => rfl }
      change p (archimedeanGLCoordinates F n g).val ∈ unitary RM
      exact Unitary.map_mem p hg
    · intro v
      let p : A →⋆* CM :=
        { ((complexPlaceScalarProjection F v).mapMatrix).toMonoidHom with
          map_star' := fun _ => rfl }
      change p (archimedeanGLCoordinates F n g).val ∈ unitary CM
      exact Unitary.map_mem p hg

/-- In a neighborhood of the mixed matrix identity, the upper triangular and
compact factors satisfy the Iwasawa identities. Both factors are based and
`ContDiffAt ℝ ∞` at the identity. -/
theorem exists_smoothLocalIwasawa_at_one :
    ∃ b k : A → A, ContDiffAt ℝ ∞ b 1 ∧ ContDiffAt ℝ ∞ k 1 ∧ b 1 = 1 ∧ k 1 = 1 ∧
      ∀ᶠ x in 𝓝 (1 : A), (b x).IsUpperTriangular ∧ IsUnit (b x) ∧
        k x ∈ unitary A ∧ b x * k x = x := by
  obtain ⟨r, hr, hr₀, hrInv⟩ := RealJacquetFrobenius.exists_localIwasawa
    (b₀ := (1 : RM)) Matrix.blockTriangular_one isUnit_one
  obtain ⟨c, hc, hc₀, _, hcInv⟩ := Langlands.Archimedean.exists_chartInverse (n := n)
  let uR (v : RP) (x : A) := 1 + RealJacquetFrobenius.upperPart (r (realProjection F n v x))
  let uC (v : CP) (x : A) := 1 + Langlands.Archimedean.upperPart (c (complexProjection F n v x))
  let kR (v : RP) (x : A) := NormedSpace.exp
    (RealJacquetFrobenius.skewPart (r (realProjection F n v x)))
  let kC (v : CP) (x : A) := NormedSpace.exp
    (Langlands.Archimedean.skewPart (c (complexProjection F n v x)))
  let e := matrixPlaceCoordinates F n
  let b (x : A) := e.symm (fun v => uR v x, fun v => uC v x)
  let k (x : A) := e.symm (fun v => kR v x, fun v => kC v x)
  have hrSmooth (v : RP) : ContDiffAt ℝ ∞ (fun x => r (realProjection F n v x)) 1 := by
    refine ContDiffAt.comp 1 ?_ (realProjection F n v).contDiff.contDiffAt
    rwa [realProjection_one]
  have hcSmooth (v : CP) : ContDiffAt ℝ ∞ (fun x => c (complexProjection F n v x)) 1 := by
    refine ContDiffAt.comp 1 ?_ (complexProjection F n v).contDiff.contDiffAt
    rwa [complexProjection_one]
  have hbSmooth : ContDiffAt ℝ ∞ b 1 :=
    (e.symm : C →L[ℝ] A).contDiff.contDiffAt.comp 1
      ((contDiffAt_pi.mpr fun v =>
        contDiffAt_const.add (RealJacquetFrobenius.upperPart.contDiff.contDiffAt.comp 1 (hrSmooth v))).prodMk
        (contDiffAt_pi.mpr fun v => contDiffAt_const.add
          ((LinearMap.toContinuousLinearMap Langlands.Archimedean.upperPart).contDiff.contDiffAt.comp
            1 (hcSmooth v))))
  have hkSmooth : ContDiffAt ℝ ∞ k 1 :=
    (e.symm : C →L[ℝ] A).contDiff.contDiffAt.comp 1
      ((contDiffAt_pi.mpr fun v => RealJacquetFrobenius.contDiff_matExp.contDiffAt.comp 1
        (RealJacquetFrobenius.skewPart.contDiff.contDiffAt.comp 1 (hrSmooth v))).prodMk
        (contDiffAt_pi.mpr fun v => (Langlands.Archimedean.contDiff_matrix_exp n).contDiffAt.comp
          1 ((LinearMap.toContinuousLinearMap Langlands.Archimedean.skewPart).contDiff.contDiffAt.comp
            1 (hcSmooth v))))
  have hb₀ : b 1 = 1 := by
    change assembleMatrix F n (fun v => uR v 1) (fun v => uC v 1) = 1
    simp only [uR, uC, realProjection_one, complexProjection_one, hr₀, hc₀, map_zero,
      add_zero, assembleMatrix_one]
  have hk₀ : k 1 = 1 := by
    change assembleMatrix F n (fun v => kR v 1) (fun v => kC v 1) = 1
    simp only [kR, kC, realProjection_one, complexProjection_one, hr₀, hc₀, map_zero,
      NormedSpace.exp_zero, assembleMatrix_one]
  have hrMul : ∀ᶠ x in 𝓝 (1 : A), ∀ v : RP, uR v x * kR v x = realProjection F n v x := by
    rw [Filter.eventually_all]
    intro v
    have h := (realProjection F n v).continuous.continuousAt (x := (1 : A))
    rw [ContinuousAt, realProjection_one] at h
    exact h.eventually hrInv
  have hcMul : ∀ᶠ x in 𝓝 (1 : A), ∀ v : CP, uC v x * kC v x = complexProjection F n v x := by
    rw [Filter.eventually_all]
    intro v
    have h := (complexProjection F n v).continuous.continuousAt (x := (1 : A))
    rw [ContinuousAt, complexProjection_one] at h
    exact h.eventually hcInv
  have hUnits : ∀ᶠ x in 𝓝 (1 : A), x ∈ Set.range (Units.val : Aˣ → A) :=
    Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨1, rfl⟩
  refine ⟨b, k, hbSmooth, hkSmooth, hb₀, hk₀, ?_⟩
  filter_upwards [hrMul, hcMul, hUnits] with x hrx hcx hx
  have hu : (b x).IsUpperTriangular := by
    intro i j hij
    apply Prod.ext
    · funext v
      exact (Matrix.blockTriangular_one.add
        (RealJacquetFrobenius.upperPart_isUpperTriangular _)) hij
    · funext v
      exact (Langlands.Archimedean.one_add_upperPart_isUpperTriangular _) hij
  have hk : k x ∈ unitary A :=
    assembleMatrix_mem_unitary F n _ _
      (fun _ => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (RealJacquetFrobenius.skewPart_mem _))
      (fun _ => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (skewAdjoint.mem_iff.mpr (Langlands.Archimedean.star_skewPart _)))
  have he : b x * k x = x := by
    change assembleMatrix F n (fun v => uR v x) (fun v => uC v x) *
      assembleMatrix F n (fun v => kR v x) (fun v => kC v x) = x
    rw [assembleMatrix_mul, funext hrx, funext hcx]
    rfl
  let ku : Aˣ := Unitary.toUnits ⟨k x, hk⟩
  have hbx : IsUnit (b x) := by
    obtain ⟨xu, hxu⟩ := hx
    have h : b x = (xu * ku⁻¹).val := by
      calc
        b x = b x * (ku.val * (ku⁻¹).val) := by rw [Units.mul_inv, mul_one]
        _ = (b x * ku.val) * (ku⁻¹).val := (mul_assoc _ _ _).symm
        _ = xu.val * (ku⁻¹).val := congrArg (fun y => y * (ku⁻¹).val) (he.trans hxu.symm)
        _ = (xu * ku⁻¹).val := rfl
    rw [h]
    exact (xu * ku⁻¹).isUnit
  exact ⟨hu, hbx, hk, he⟩

private theorem smoothLocalIwasawa_translate (b₀ k₀ : ArchimedeanGL F n)
    (hb₀ : b₀.val.IsUpperTriangular) (hk₀ : k₀.val ∈ unitary A) :
    ∃ b k : A → A, ContDiffAt ℝ ∞ b (b₀ * k₀).val ∧ ContDiffAt ℝ ∞ k (b₀ * k₀).val ∧
      ∀ᶠ x in 𝓝 (b₀ * k₀).val, (b x).IsUpperTriangular ∧ IsUnit (b x) ∧
        k x ∈ unitary A ∧ b x * k x = x := by
  obtain ⟨b, k, hb, hk, _, _, hfact⟩ := exists_smoothLocalIwasawa_at_one F n
  let translate (x : A) := (b₀⁻¹).val * x * (k₀⁻¹).val
  have hbase : translate (b₀ * k₀).val = 1 := by
    change (b₀⁻¹).val * (b₀.val * k₀.val) * (k₀⁻¹).val = 1
    rw [← mul_assoc, Units.inv_mul, one_mul, Units.mul_inv]
  have ht : ContDiff ℝ ∞ translate :=
    (contDiff_const.mul contDiff_id).mul contDiff_const
  have hb' : ContDiffAt ℝ ∞ (fun x => b (translate x)) (b₀ * k₀).val :=
    ContDiffAt.comp _ (hbase.symm ▸ hb) ht.contDiffAt
  have hk' : ContDiffAt ℝ ∞ (fun x => k (translate x)) (b₀ * k₀).val :=
    ContDiffAt.comp _ (hbase.symm ▸ hk) ht.contDiffAt
  refine ⟨fun x => b₀.val * b (translate x), fun x => k (translate x) * k₀.val,
    contDiffAt_const.mul hb', hk'.mul contDiffAt_const, ?_⟩
  have hT := ht.continuous.continuousAt (x := (b₀ * k₀).val)
  rw [ContinuousAt, hbase] at hT
  filter_upwards [hT.eventually hfact] with x hx
  refine ⟨hb₀.mul hx.1, b₀.isUnit.mul hx.2.1, (unitary A).mul_mem hx.2.2.1 hk₀, ?_⟩
  calc
    (b₀.val * b (translate x)) * (k (translate x) * k₀.val) =
        b₀.val * (b (translate x) * k (translate x)) * k₀.val := by
      rw [← mul_assoc, mul_assoc b₀.val]
    _ = b₀.val * translate x * k₀.val := by rw [hx.2.2.2]
    _ = x := by
      change (b₀.val * ((b₀⁻¹).val * x * (k₀⁻¹).val)) * k₀.val = x
      rw [← mul_assoc b₀.val, ← mul_assoc b₀.val, Units.mul_inv, one_mul,
        mul_assoc x, Units.inv_mul, mul_one]

/-- At an invertible archimedean matrix, the factors are `ContDiffAt ℝ ∞` in
mixed matrix coordinates and satisfy the Iwasawa identities on a neighborhood. -/
theorem exists_smoothLocalIwasawa (g : ArchimedeanGL F n) :
    ∃ b k : A → A, ContDiffAt ℝ ∞ b g.val ∧ ContDiffAt ℝ ∞ k g.val ∧
      ∀ᶠ x in 𝓝 g.val, (b x).IsUpperTriangular ∧ IsUnit (b x) ∧
        k x ∈ unitary A ∧ b x * k x = x := by
  let e := archimedeanGLCoordinates F n
  obtain ⟨b, k, hg, hb, hk⟩ := PrimitiveAdelicHeight.exists_infinite_iwasawa
    F n (e.symm g)
  let b₀ := e b
  let k₀ := e k
  have he : g = b₀ * k₀ :=
    (e.apply_symm_apply g).symm.trans ((congrArg e hg).trans (map_mul e b k))
  have hb₀ : b₀.val.IsUpperTriangular := by
    intro i j hij
    change archimedeanGLCoordinates F n b i j = 0
    rw [archimedeanGLCoordinates_apply, hb hij, map_zero]
  have hk₀ : k₀.val ∈ unitary A :=
    (mem_standardInfiniteCompact_iff_mem_unitary F n k).mp hk
  rw [he]
  exact smoothLocalIwasawa_translate F n b₀ k₀ hb₀ hk₀

end Langlands.Global.ArchimedeanGL
