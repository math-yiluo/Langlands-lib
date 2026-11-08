import Langlands.Geometry.Building.RootFunctionFieldEquivariance
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Normalizer shifts tested only on original field points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.RootFunctionFamily

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- For a normalized family, a normalizer translation is determined exactly
by its values on the original actual root groups. No valuation is assumed. -/
theorem smul_eq_vadd_iff_on_rootGroups
    (φ : RootFunctionFamily S G)
    (hroot : ∀ a, a ∉ relativeRoots i → ∀ g, φ a g = ⊤)
    (hgroup : ∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a → φ a g = ⊤)
    (n : normalizerPoints i) (v : V S) :
    n • φ = v +ᵥ φ ↔
      ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
        (n • φ) a g = φ a g + ((eval S a v : ℝ) : WithTop ℝ) := by
  constructor
  · intro h a _ g _
    exact congrArg (fun ψ : RootFunctionFamily S G => ψ a g) h
  · intro h
    apply RootFunctionFamily.ext
    intro a g
    rw [vadd_apply]
    by_cases ha : a ∈ relativeRoots i
    · by_cases hg : g ∈ rootGroupPoints i a
      · exact h a ha g hg
      · have ha' := weylAction_mapsTo_relativeRoots i n⁻¹ ha
        have hg' : (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∉
            rootGroupPoints i (weylAction i n⁻¹ a) := by
          intro hmem
          apply hg
          have he := RelativeRoot.normalizer_conj_mem_iff i a n⁻¹ g
          simp only [constantPoint_self, Subgroup.coe_inv, inv_inv] at he
          exact he.mp hmem
        rw [smul_apply, hgroup _ ha' _ hg', hgroup a ha g hg, WithTop.top_add]
    · have ha' : weylAction i n⁻¹ a ∉ relativeRoots i := by
        intro hmem
        exact ha ((weylAction_mem_roots_iff n⁻¹ a).mp hmem)
      rw [smul_apply, hroot _ ha', hroot a ha, WithTop.top_add]

section FieldExtension

variable {K : Type u} [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

omit [Mono i.hom.hom.left] in
/-- The two support-normalization laws descend without an upstairs valuation.
The only geometric input is reflection of the original nonzero root groups. -/
theorem fieldRestrict_normalization
    [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (ψ : RootFunctionFamily S_K G_K)
    (hroot : ∀ a, a ∉ relativeRoots (T := S_K) i_K → ∀ g, ψ a g = ⊤)
    (hgroup : ∀ a ∈ relativeRoots (T := S_K) i_K,
      ∀ g, g ∉ rootGroupPoints (S := S_K) i_K a → ψ a g = ⊤) :
    (∀ a, a ∉ relativeRoots i → ∀ g, fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤) ∧
      (∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a →
        fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤) := by
  constructor
  · intro a ha g
    apply hroot
    exact fun h => ha ((mem_roots_baseChange_iff (K := K) G S hS i a).mp h)
  · intro a ha g hg
    apply hgroup _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha)
    exact fun h => hg ((rationalExtend_mem_rootGroupPoints_iff i hS a ha.1 g).mp h)

variable (i)

/-- A shift of the restricted family is equivalent to the upstairs shift
formula on scalar extensions of original root-group points only. -/
theorem fieldRestrict_smul_eq_vadd_iff
    (ψ : RootFunctionFamily S_K G_K)
    (hroot : ∀ a, a ∉ relativeRoots i → ∀ g,
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (hgroup : ∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a →
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (n : normalizerPoints i) (v : V S) :
    n • fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ = v +ᵥ fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ ↔
      ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
        (normalizerPointsFieldExtend (K := K) i n • ψ)
            (a_K a) (rationalExtend k K G g) =
          ψ (a_K a) (rationalExtend k K G g) +
            ((eval S a v : ℝ) : WithTop ℝ) := by
  rw [smul_eq_vadd_iff_on_rootGroups (fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ) hroot hgroup n v]
  simp only [← fieldRestrict_normalizer i n ψ, fieldRestrict_apply]

/-- Choose an original cocharacter shift from a formula tested only on
the original field's root-group points. The entire-family equality is retained. -/
def fieldRestrictNormalizerShift
    (ψ : RootFunctionFamily S_K G_K)
    (hroot : ∀ a, a ∉ relativeRoots i → ∀ g,
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (hgroup : ∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a →
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (n : normalizerPoints i)
    (hshift : ∃ v : V S, ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
      (normalizerPointsFieldExtend (K := K) i n • ψ)
          (a_K a) (rationalExtend k K G g) =
        ψ (a_K a) (rationalExtend k K G g) +
          ((eval S a v : ℝ) : WithTop ℝ)) :
    {v : V S // n • fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ = v +ᵥ fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ} :=
  ⟨hshift.choose,
    (fieldRestrict_smul_eq_vadd_iff (K := K) i ψ hroot hgroup n hshift.choose).mpr
      hshift.choose_spec⟩

/-- Original-point shifts give exactly V2 for all original reflecting
normalizers. No valuation for the lower torus over the larger field is used. -/
theorem fieldRestrict_reflection_of_originalPointShifts
    (ψ : RootFunctionFamily S_K G_K)
    (hroot : ∀ a, a ∉ relativeRoots i → ∀ g,
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (hgroup : ∀ a ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i a →
      fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g = ⊤)
    (hshift : ∀ n : normalizerPoints i, ∃ v : V S,
      ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
        (normalizerPointsFieldExtend (K := K) i n • ψ)
            (a_K a) (rationalExtend k K G g) =
          ψ (a_K a) (rationalExtend k K G g) +
            ((eval S a v : ℝ) : WithTop ℝ)) :
    ∀ a ∈ relativeRoots i, ∀ n : normalizerPoints i,
      RealizesReflection i a n →
        ∃ c : ℝ, ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
          fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ a g =
            fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ (-a)
              ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) +
                (c : WithTop ℝ) := by
  intro a _ n hn
  let v := fieldRestrictNormalizerShift (K := K) i ψ hroot hgroup n (hshift n)
  have h := v.property
  refine ⟨-eval S a v.val, fun g _ _ => ?_⟩
  have ha : weylAction i n⁻¹ (-a) = a := by
    rw [← hn.1, map_inv]
    exact (weylAction i n).symm_apply_apply a
  have hg : (n : rationalPoints G)⁻¹ *
      ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) *
        (n : rationalPoints G) = g := by group
  have heq := congrArg
    (fun φ : RootFunctionFamily S G =>
      φ (-a) ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹)) h
  simpa only [smul_apply, vadd_apply, ha, hg, eval_neg_char] using heq

end FieldExtension

end Langlands.Geometry.Building.RootFunctionFamily
