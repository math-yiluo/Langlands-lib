import Langlands.Automorphic.GeneralLinearBlockConstantTermTransitivity
import Langlands.Automorphic.GroupSchemeConstantTermConjugation
import Langlands.GroupScheme.Dynamic.Conjugation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuous rational-invariant Levi slices of block constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints GeneralLinearBlockSemidirect

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "N(" e ")" => blockUnipotent (Fin n) RF e
local notation "P(" e ")" => blockParabolic (Fin n) RF e
local notation "L(" e ")" => blockLevi (Fin n) RF e

local instance : IsAffine (GLG).X.left := isAffine_groupScheme (Fin n) RF

local instance : Smooth (GLG).X.hom := smoothStatement (Fin n) RF

local instance (e : Fin n → ℤ) :
    IsClosed (adelicPoints F GLG N(e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance (e : Fin n → ℤ) : CompactSpace (RationalQuotient F GLG N(e)) :=
  blockUnipotentRationalQuotientCompactSpace F e

local instance (e : Fin n → ℤ) : BorelSpace (RationalQuotient F GLG N(e)) :=
  rationalQuotientBorelSpace F GLG N(e)

local instance (e : Fin n → ℤ) :
    IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F GLG N(e)) :=
  normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F GLG N(e)

/-- The normalized constant-term integrand is jointly continuous in the
adelic argument and the compact radical quotient coordinate. -/
theorem continuous_uncurry_blockConstantTermIntegrand (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG) :
    Continuous (Function.uncurry (constantTermIntegrand F GLG N(e) f)) := by
  let Γ := rationalSubgroup F GLG N(e)
  have hq : IsOpenQuotientMap
      (Prod.map (id : AdelicGroupPoints F GLG → AdelicGroupPoints F GLG) (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : AdelicGroupPoints F GLG × adelicPoints F GLG N(e) =>
    evaluate F GLG f (p.2.val * p.1))
  exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)

/-- The mass-one block constant term is continuous on the ambient adelic group. -/
theorem continuous_normalizedBlockConstantTerm (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG) : Continuous (normalizedBlockConstantTerm F e f) := by
  let ν := normalizedRationalQuotientHaarMeasure F GLG N(e)
  let φ := constantTermIntegrand F GLG N(e) f
  have hφ : Continuous (Function.uncurry φ) := continuous_uncurry_blockConstantTermIntegrand F e f
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨C, hC⟩ := (hK.prod
    (isCompact_univ : IsCompact (Set.univ : Set (RationalQuotient F GLG N(e))))).exists_bound_of_continuousOn
      hφ.continuousOn
  change ContinuousAt (fun x => ∫ q, φ x q ∂ν) g
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun x =>
      (continuous_constantTermIntegrand F GLG N(e) f x).aestronglyMeasurable)
    ?_ (integrable_const C) ?_
  · filter_upwards [hg] with x hx
    exact ae_of_all _ fun q => hC (x, q) ⟨hx, Set.mem_univ _⟩
  · exact ae_of_all _ fun q =>
      (hφ.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- Rational points in the block parabolic preserve the normalized constant term
by left multiplication. -/
theorem normalizedBlockConstantTerm_parabolic_rational_mul (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG)
    (q : Over.mk (𝟙 (Spec RF)) ⟶ (GLG).X)
    (hq : q ∈ P(e).carrier (Over.mk (𝟙 (Spec RF))))
    (g : AdelicGroupPoints F GLG) :
    normalizedBlockConstantTerm F e f (innerAdelicPoint F GLG q * g) =
      normalizedBlockConstantTerm F e f g := by
  have hnorm : N(e).IsNormalizedBy P(e) := by
    rw [← unipotent_diagonalCocharacter, ← parabolic_diagonalCocharacter]
    exact Dynamic.unipotent_isNormalizedBy_parabolic (diagonalCocharacter (Fin n) RF e)
  have hU : N(e) = N(e).comap ((GLG).innerIso q).hom := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    change x ∈ N(e).carrier T ↔ x ≫ ((GLG).innerIso q).hom.hom.hom ∈ N(e).carrier T
    rw [GroupScheme.comp_innerIso_hom]
    let a := (GLG).constantPoint q T
    have ha : a ∈ P(e).carrier T :=
      P(e).comp_mem (T := Over.mk (𝟙 (Spec RF))) (T' := T)
        (Over.homMk T.hom (by simp)) hq
    constructor
    · exact hnorm T a x ha
    · intro h
      have ha' := hnorm T a⁻¹ (a * x * a⁻¹) ((P(e).carrier T).inv_mem ha) h
      simpa only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using ha'
  have he := constantTerm_comap_innerIso F GLG q N(e) N(e) hU f (innerAdelicPoint F GLG q * g)
  rw [inv_mul_cancel_left] at he
  exact he

/-- The slice of the normalized block constant term on the actual adelic Levi
points, at an ambient argument `g`. -/
def normalizedBlockLeviSlice (e : Fin n → ℤ) (f : ContinuousRationalFunctions F GLG)
    (g : AdelicGroupPoints F GLG) (m : adelicPoints F GLG L(e)) : ℂ :=
  normalizedBlockConstantTerm F e f (m.val * g)

theorem continuous_normalizedBlockLeviSlice (e : Fin n → ℤ) (f : ContinuousRationalFunctions F GLG)
    (g : AdelicGroupPoints F GLG) : Continuous (normalizedBlockLeviSlice F e f g) :=
  (continuous_normalizedBlockConstantTerm F e f).comp (continuous_subtype_val.mul_const g)

theorem normalizedBlockLeviSlice_rational_mul (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG)
    (q : Over.mk (𝟙 (Spec RF)) ⟶ (GLG).X)
    (hq : q ∈ L(e).carrier (Over.mk (𝟙 (Spec RF))))
    (m m' : adelicPoints F GLG L(e))
    (hm : m'.val = innerAdelicPoint F GLG q * m.val) :
    normalizedBlockLeviSlice F e f g m' = normalizedBlockLeviSlice F e f g m := by
  have hle : L(e) ≤ P(e) := by
    rw [← centralizer_diagonalCocharacter, ← parabolic_diagonalCocharacter]
    exact Dynamic.centralizer_le_parabolic (diagonalCocharacter (Fin n) RF e)
  simp only [normalizedBlockLeviSlice, hm, mul_assoc]
  exact normalizedBlockConstantTerm_parabolic_rational_mul F e f q (hle _ hq) _

end Langlands.Automorphic.GroupSchemeFunctions
