import Langlands.Geometry.Building.RootValueTorusReflection
import Langlands.GroupScheme.Rational.NestedTorusNormalizerFactorization

/-! # Extending common-normalizer shifts through the actual centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section ScalarActions

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Centralizer covariance on root groups and the two normalization laws
give a translation on the entire scalar family, without assuming V2 or V5. -/
theorem RootFunctionFamily.centralizer_smul_eq_vadd
    [IsAffineHom G.X.hom]
    (ψ : RootFunctionFamily S G)
    (hroot : ∀ α, α ∉ relativeRoots i → ∀ g, ψ α g = ⊤)
    (hgroup : ∀ α ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i α → ψ α g = ⊤)
    (z : centralizerPoints i) (w : V S)
    (hcov : ∀ α ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i α,
      ψ α ((z : rationalPoints G)⁻¹ * g * (z : rationalPoints G)) =
        ψ α g + ((eval S α w : ℝ) : WithTop ℝ)) :
    Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z • ψ = w +ᵥ ψ := by
  let n := Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z
  have hw : weylAction i n⁻¹ = 1 :=
    weylAction_eq_one_of_mem_centralizerPoints i
      ((centralizerPoints i).inv_mem z.property)
  apply RootFunctionFamily.ext
  intro α g
  change (n • ψ) α g = (w +ᵥ ψ) α g
  rw [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hw,
    LinearEquiv.coe_one, id]
  by_cases hα : α ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i α
    · exact hcov α hα g hg
    · have hg' : (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∉
          rootGroupPoints i α := by
        intro hmem
        apply hg
        have he := RelativeRoot.normalizer_conj_mem_iff i α n⁻¹ g
        simp only [constantPoint_self, Subgroup.coe_inv, inv_inv, hw,
          LinearEquiv.coe_one, id] at he
        exact he.mp hmem
      rw [hgroup α hα _ hg', hgroup α hα g hg, WithTop.top_add]
  · rw [hroot α hα, hroot α hα, WithTop.top_add]

/-- Exact ambient factorization composes a centralizer shift and a
normalizer shift by addition in the original cocharacter space. -/
theorem RootFunctionFamily.normalizer_shift_of_centralizer_factor
    (ψ : RootFunctionFamily S G) (n : normalizerPoints i)
    (z : centralizerPoints i) (m : normalizerPoints i)
    (hn : (n : rationalPoints G) = (z : rationalPoints G) * (m : rationalPoints G))
    (v w : V S)
    (hz : Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z • ψ = w +ᵥ ψ)
    (hm : m • ψ = v +ᵥ ψ) :
    n • ψ = (v + w) +ᵥ ψ := by
  let nz := Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z
  have hn' : n = nz * m := Subtype.ext hn
  have hv : nz • v = v := by
    change normalizerAction i nz v = v
    rw [normalizerAction_eq_one_of_mem_centralizerPoints i (n := nz) z.property]
    rfl
  rw [hn', mul_smul, hm, RootFunctionFamily.smul_vadd, hv, hz, vadd_vadd]

end ScalarActions

section NestedTori

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (f : S ⟶ T) [Mono (CommGroupScheme.groupHom f ≫ i).hom.hom.left]
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (hE : RelativeRoot.HasOppositeFactorPairs i)
  {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
  (hi : IsMaximalSplitTorus i)
  {H : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G)
  (hj : (torusCentralizer (CommGroupScheme.groupHom f ≫ i)).IsRepresentedBy j)
  (hjc : IsClosedSubgroup j) (hH : MaximalSplitToriAreConjugate H)
  (ν : centralizerPoints (CommGroupScheme.groupHom f ≫ i) → V S)
  (hcov : ∀ (z : centralizerPoints (CommGroupScheme.groupHom f ≫ i)),
    ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i),
      ∀ g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α,
        torusRestrictedRootFunctionFamily hS hT hE hφ f α
            ((z : rationalPoints G)⁻¹ * g * (z : rationalPoints G)) =
          torusRestrictedRootFunctionFamily hS hT hE hφ f α g +
            ((eval S α (ν z) : ℝ) : WithTop ℝ))
  (hcommon : ∀ (nT : normalizerPoints i),
    (nT : rationalPoints G) ∈ normalizerPoints (CommGroupScheme.groupHom f ≫ i) →
      ∃ v : V S, nT • φ = cocharacterMapReal f v +ᵥ φ)

include hi hj hjc hH hcov hcommon

/-- Full-centralizer covariance and shifts on common normalizers yield a
shift for every actual lower normalizer through centralizer correction. -/
theorem exists_torusRestrictedNormalizerShift
    (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i)) :
    ∃ v : V S,
      nS • torusRestrictedRootFunctionFamily hS hT hE hφ f =
        v +ᵥ torusRestrictedRootFunctionFamily hS hT hE hφ f := by
  obtain ⟨z, nT, hnT, hn⟩ :=
    exists_centralizer_mul_commonNormalizer i f hi j hj hjc hH nS
  let m : normalizerPoints (CommGroupScheme.groupHom f ≫ i) := ⟨nT.val, hnT⟩
  obtain ⟨v, hv⟩ := hcommon nT hnT
  refine ⟨v + ν z, RootFunctionFamily.normalizer_shift_of_centralizer_factor
    (torusRestrictedRootFunctionFamily hS hT hE hφ f) nS z m hn v (ν z) ?_ ?_⟩
  · exact RootFunctionFamily.centralizer_smul_eq_vadd
      (torusRestrictedRootFunctionFamily hS hT hE hφ f)
      (torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f)
      (fun α _ g hg =>
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α g hg)
      z (ν z) (hcov z)
  · exact torusRestrictedRootFunctionFamily_normalizer_shift
      f m nT rfl hS hT hE hφ v hv

/-- Choose an actual lower cocharacter vector realizing the shift of the
entire restricted scalar family by the supplied arbitrary lower normalizer. -/
def torusRestrictedNormalizerShift
    (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i)) :
    {v : V S //
      nS • torusRestrictedRootFunctionFamily hS hT hE hφ f =
        v +ᵥ torusRestrictedRootFunctionFamily hS hT hE hφ f} :=
  let hex := exists_torusRestrictedNormalizerShift
    f hS hT hE hφ hi j hj hjc hH ν hcov hcommon nS
  ⟨hex.choose, hex.choose_spec⟩

/-- The corrected shift proves exactly V2 for every original lower
reflecting normalizer, with no common-upper-representative premise on it. -/
theorem torusRestrictedRootFunctionFamily_reflection_of_centralizer_correction :
    ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i),
      ∀ nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i),
        RealizesReflection (CommGroupScheme.groupHom f ≫ i) α nS →
          ∃ c : ℝ, ∀ g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α,
            g ≠ 1 →
              torusRestrictedRootFunctionFamily hS hT hE hφ f α g =
                torusRestrictedRootFunctionFamily hS hT hE hφ f (-α)
                  ((nS : rationalPoints G) * g * (nS : rationalPoints G)⁻¹) +
                    (c : WithTop ℝ) := by
  intro α _ nS hnS
  obtain ⟨v, hv⟩ := exists_torusRestrictedNormalizerShift
    f hS hT hE hφ hi j hj hjc hH ν hcov hcommon nS
  refine ⟨-eval S α v, fun g _ _ => ?_⟩
  exact RootFunctionFamily.reflection_eq_of_normalizer_shift
    (torusRestrictedRootFunctionFamily hS hT hE hφ f) α nS v hnS.1 hv g

end NestedTori

end Langlands.Geometry.Building
