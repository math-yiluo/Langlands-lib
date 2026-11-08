import Langlands.Geometry.Building.RootValueTorusTranslation
import Langlands.Geometry.Building.CrossTorusValuation
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Common actual normalizers and torus-restricted root functions -/

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
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

private theorem map_innerIso_inv (n g : rationalPoints G) :
    rationalPoints.map (G.innerIso n).inv g = n⁻¹ * g * n := by
  rw [rationalPoints.map_apply]
  have hi := congrArg (fun q : G ⟶ G => q.hom.hom) (innerIso_inv_hom G n)
  rw [← hi, comp_innerIso_hom, constantPoint_self, inv_inv]

private theorem normalizer_inverse_character
    (n : normalizerPoints i) (a : characterLattice T) :
    (characterLattice.congr (normalizingAut i n)).symm a = weylAction i n⁻¹ a := by
  have hn : IsNormalizingPoint i (n⁻¹ : normalizerPoints i)
      (normalizingAut i n).symm :=
    (isNormalizingPoint_normalizingAut i n).inv
  exact (weylAction_eq i (n := n⁻¹) (σ := (normalizingAut i n).symm) hn a).symm

/-- The original normalizer action is transport by its actual scheme
automorphisms on the torus and the ambient group. -/
theorem RootFunctionFamily.transportEquiv_normalizer
    (n : normalizerPoints i) (φ : RootFunctionFamily T G) :
    RootFunctionFamily.transportEquiv (normalizingAut i n)
      (G.innerIso (n : rationalPoints G)) φ = n • φ := by
  apply RootFunctionFamily.ext
  intro a g
  change φ ((characterLattice.congr (normalizingAut i n)).symm a)
      (rationalPoints.map (G.innerIso (n : rationalPoints G)).inv g) =
    φ (weylAction i n⁻¹ a) ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G))
  exact congrArg₂ (fun a g => φ a g) (normalizer_inverse_character n a)
    (map_innerIso_inv (n : rationalPoints G) g)

variable [IsAffineHom G.X.hom]

/-- The original action of every actual upper normalizer preserves all
normalization conditions and root-datum valuation axioms. -/
theorem IsRootDatumValuation.normalizer_smul {φ : RootFunctionFamily T G}
    (hφ : IsRootDatumValuation i φ) (n : normalizerPoints i) :
    IsRootDatumValuation i (n • φ) := by
  rw [← RootFunctionFamily.transportEquiv_normalizer]
  exact hφ.transport (normalizingAut i n) (G.innerIso (n : rationalPoints G))
    (isNormalizingPoint_normalizingAut i n)

omit [IsAffineHom G.X.hom] in
private theorem inverse_conj_mem_rootGroupPoints_iff
    (n : normalizerPoints i) (χ : characterLattice T) (g : rationalPoints G) :
    (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∈ rootGroupPoints i χ ↔
      g ∈ rootGroupPoints i (weylAction i n χ) := by
  have h := RelativeRoot.normalizer_conj_mem_iff i χ n
    ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G))
  simp only [constantPoint_self] at h
  have he : (n : rationalPoints G) *
      ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) *
        (n : rationalPoints G)⁻¹ = g := by group
  rw [he] at h
  exact h.symm

/-- Conjugation carries each actual upper filtration subgroup to its
Weyl-translated subgroup for the original normalizer action on families. -/
theorem IsRootDatumValuation.filtrationSubgroup_normalizer_smul
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (n : normalizerPoints i) (χ : characterLattice T) (r : ℝ) :
    (hφ.normalizer_smul n).filtrationSubgroup (weylAction i n χ) r =
      (hφ.filtrationSubgroup χ r).map
        (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  apply Subgroup.ext
  intro g
  change (g ∈ rootGroupPoints i (weylAction i n χ) ∧
      (r : WithTop ℝ) ≤ (n • φ) (weylAction i n χ) g) ↔
    ((MulAut.conj (n : rationalPoints G)).symm g ∈ rootGroupPoints i χ ∧
      (r : WithTop ℝ) ≤ φ χ ((MulAut.conj (n : rationalPoints G)).symm g))
  have ha : weylAction i n⁻¹ (weylAction i n χ) = χ := by
    rw [map_inv]
    exact (weylAction i n).symm_apply_apply χ
  simp only [RootFunctionFamily.smul_apply, ha, MulAut.conj_symm_apply]
  rw [inverse_conj_mem_rootGroupPoints_iff]

section CommonNormalizer

variable (f : S ⟶ T)
  (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i))
  (nT : normalizerPoints i)
  (hn : (nS : rationalPoints G) = (nT : rationalPoints G))

include hn

omit [IsAffineHom G.X.hom] in
/-- Two actual normalizers with the same ambient point intertwine the
original torus morphism, by monomorphy of the upper embedding. -/
theorem commonNormalizer_normalizingAut_comp :
    (normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).hom ≫ f =
      f ≫ (normalizingAut i nT).hom := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hS := isNormalizingPoint_normalizingAut
    (CommGroupScheme.groupHom f ≫ i) nS
  have hT := isNormalizingPoint_normalizingAut i nT
  have he :
      CommGroupScheme.groupHom
          ((normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).hom ≫ f) ≫ i =
        CommGroupScheme.groupHom (f ≫ (normalizingAut i nT).hom) ≫ i := by
    change CommGroupScheme.groupHom
        (normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).hom ≫
          CommGroupScheme.groupHom f ≫ i =
      CommGroupScheme.groupHom f ≫
        CommGroupScheme.groupHom (normalizingAut i nT).hom ≫ i
    rw [← hS, hn, Category.assoc, hT]
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact (cancel_mono i.hom.hom).mp
    (congrArg (fun q : S.toGrp ⟶ G => q.hom.hom) he)

variable [Mono (CommGroupScheme.groupHom f ≫ i).hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- Restriction of characters intertwines the two actual Weyl actions. -/
theorem commonNormalizer_weylAction_comp (χ : characterLattice T) :
    f ≫ weylAction i nT χ =
      weylAction (CommGroupScheme.groupHom f ≫ i) nS (f ≫ χ) := by
  have h := commonNormalizer_normalizingAut_comp f nS nT hn
  have hinv :
      f ≫ (normalizingAut i nT).inv =
        (normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).inv ≫ f := by
    calc
      _ = (normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).inv ≫
          ((normalizingAut (CommGroupScheme.groupHom f ≫ i) nS).hom ≫ f) ≫
            (normalizingAut i nT).inv := by simp
      _ = _ := by rw [h]; simp
  simp only [weylAction_apply, ← Category.assoc, hinv]

omit [IsAffineHom G.X.hom] in
/-- The common normalizer character square preserves every positive
integral multiplier in a restriction fibre. -/
theorem commonNormalizer_restrict_eq_nsmul_iff
    (χ : characterLattice T) (α : characterLattice S) (m : ℕ) :
    f ≫ weylAction i nT χ =
        m • weylAction (CommGroupScheme.groupHom f ≫ i) nS α ↔
      f ≫ χ = m • α := by
  rw [commonNormalizer_weylAction_comp f nS nT hn, ← map_nsmul]
  exact (weylAction (CommGroupScheme.groupHom f ≫ i) nS).injective.eq_iff

/-- Common actual normalizers carry the entire canonical restricted
filtration to the corresponding Weyl-translated filtration. -/
theorem torusRestrictedRootDepthSubgroup_normalizer_smul
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (α : characterLattice S) (r : ℝ) :
    torusRestrictedRootDepthSubgroup (hφ.normalizer_smul nT) f
        (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) r =
      (torusRestrictedRootDepthSubgroup hφ f α r).map
        (MulAut.conj (nT : rationalPoints G)).toMonoidHom := by
  unfold torusRestrictedRootDepthSubgroup
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    obtain ⟨χ, rfl⟩ := (weylAction i nT).surjective χ
    have hχ0 : χ ∈ relativeRoots i := (weylAction_mem_roots_iff nT χ).mp hχ
    have heq0 := (commonNormalizer_restrict_eq_nsmul_iff
      f nS nT hn χ α m).mp heq
    rw [hφ.filtrationSubgroup_normalizer_smul]
    exact le_iSup_of_le χ (le_iSup_of_le hχ0 (le_iSup_of_le m
      (le_iSup_of_le hm (le_iSup_of_le heq0 le_rfl))))
  · refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    have hχ1 : weylAction i nT χ ∈ relativeRoots i :=
      (weylAction_mem_roots_iff nT χ).mpr hχ
    have heq1 := (commonNormalizer_restrict_eq_nsmul_iff
      f nS nT hn χ α m).mpr heq
    rw [← hφ.filtrationSubgroup_normalizer_smul]
    exact le_iSup_of_le (weylAction i nT χ) (le_iSup_of_le hχ1
      (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le heq1 le_rfl))))

/-- Membership in the canonical restricted filtration is preserved and
reflected by conjugation by the common ambient point. -/
theorem mem_torusRestrictedRootDepthSubgroup_normalizer_smul_iff
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (α : characterLattice S) (g : rationalPoints G) (r : ℝ) :
    (nT : rationalPoints G) * g * (nT : rationalPoints G)⁻¹ ∈
        torusRestrictedRootDepthSubgroup (hφ.normalizer_smul nT) f
          (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) r ↔
      g ∈ torusRestrictedRootDepthSubgroup hφ f α r := by
  change MulAut.conj (nT : rationalPoints G) g ∈ _ ↔ _
  rw [torusRestrictedRootDepthSubgroup_normalizer_smul f nS nT hn hφ,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The induced multiplicative equivalence acts by the original ambient
conjugation, rather than by an unspecified abstract subgroup isomorphism. -/
def torusRestrictedRootDepthNormalizerPointsEquiv
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (α : characterLattice S) (r : ℝ) :
    ↥(torusRestrictedRootDepthSubgroup hφ f α r) ≃*
      ↥(torusRestrictedRootDepthSubgroup (hφ.normalizer_smul nT) f
        (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) r) :=
  ((MulAut.conj (nT : rationalPoints G)).subgroupMap
    (torusRestrictedRootDepthSubgroup hφ f α r)).trans
    (MulEquiv.subgroupCongr
      (torusRestrictedRootDepthSubgroup_normalizer_smul f nS nT hn hφ α r).symm)

@[simp] theorem torusRestrictedRootDepthNormalizerPointsEquiv_val
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (α : characterLattice S) (r : ℝ)
    (g : ↥(torusRestrictedRootDepthSubgroup hφ f α r)) :
    (torusRestrictedRootDepthNormalizerPointsEquiv
      (i := i) (φ := φ) f nS nT hn hφ α r g).val =
      (nT : rationalPoints G) * g.val * (nT : rationalPoints G)⁻¹ := by
  rfl

variable [Smooth G.X.hom]

/-- The entire constructed scalar family intertwines the two original
normalizer actions whenever the lower and upper normalizers are the same
ambient point. -/
theorem torusRestrictedRootFunctionFamily_normalizer_smul
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ) :
    torusRestrictedRootFunctionFamily hS hT hE (hφ.normalizer_smul nT) f =
      nS • torusRestrictedRootFunctionFamily hS hT hE hφ f := by
  apply RootFunctionFamily.ext
  intro α g
  obtain ⟨α, rfl⟩ :=
    (weylAction (CommGroupScheme.groupHom f ≫ i) nS).surjective α
  obtain ⟨g, rfl⟩ := (MulAut.conj (nT : rationalPoints G)).surjective g
  have ha : weylAction (CommGroupScheme.groupHom f ≫ i) nS⁻¹
      (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) = α := by
    rw [map_inv]
    exact (weylAction (CommGroupScheme.groupHom f ≫ i) nS).symm_apply_apply α
  have hg : (nS : rationalPoints G)⁻¹ *
      (MulAut.conj (nT : rationalPoints G) g) * (nS : rationalPoints G) = g := by
    rw [hn, MulAut.conj_apply]
    group
  rw [RootFunctionFamily.smul_apply, ha, hg]
  have hroot : weylAction (CommGroupScheme.groupHom f ≫ i) nS α ∈
      relativeRoots (CommGroupScheme.groupHom f ≫ i) ↔
        α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i) :=
    weylAction_mem_roots_iff nS α
  have hgroup : MulAut.conj (nT : rationalPoints G) g ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ i)
        (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) ↔
      g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α := by
    have h := RelativeRoot.normalizer_conj_mem_iff
      (CommGroupScheme.groupHom f ≫ i) α nS g
    simpa only [constantPoint_self, hn, MulAut.conj_apply, rootGroupPoints] using h
  by_cases hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
  · by_cases hg0 : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α
    · apply WithTop.eq_of_forall_coe_le_iff
      intro r
      rw [le_torusRestrictedRootFunctionFamily_iff hS hT hE
          (hφ.normalizer_smul nT) f _ (hroot.mpr hα) _ (hgroup.mpr hg0) r,
        le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg0 r]
      exact mem_torusRestrictedRootDepthSubgroup_normalizer_smul_iff
        f nS nT hn hφ α g r
    · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE
          (hφ.normalizer_smul nT) f _ _ (fun h => hg0 (hgroup.mp h)),
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α g hg0]
  · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE
        (hφ.normalizer_smul nT) f _ (fun h => hα (hroot.mp h)),
      torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f α hα]

/-- An upper shift coming from an actual lower cocharacter vector descends
to that same shift of the lower scalar family for common normalizers. -/
theorem torusRestrictedRootFunctionFamily_normalizer_shift
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (v : V S) (hshift : nT • φ = cocharacterMapReal f v +ᵥ φ) :
    nS • torusRestrictedRootFunctionFamily hS hT hE hφ f =
      v +ᵥ torusRestrictedRootFunctionFamily hS hT hE hφ f := by
  rw [← torusRestrictedRootFunctionFamily_normalizer_smul f nS nT hn]
  have hcongr :
      ∀ (ψ : RootFunctionFamily T G) (hψ : IsRootDatumValuation i ψ),
        nT • φ = ψ →
          torusRestrictedRootFunctionFamily hS hT hE (hφ.normalizer_smul nT) f =
            torusRestrictedRootFunctionFamily hS hT hE hψ f := by
    intro ψ hψ heq
    subst ψ
    rfl
  exact (hcongr _ _ hshift).trans
    (torusRestrictedRootFunctionFamily_vadd hS hT hE hφ f v)

end CommonNormalizer

end Langlands.Geometry.Building
