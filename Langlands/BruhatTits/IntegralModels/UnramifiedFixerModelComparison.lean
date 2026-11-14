import Langlands.BruhatTits.IntegralModels.UnramifiedNonnegativeIntegrality
import Langlands.BruhatTits.IntegralModels.UnramifiedComponentModelComparison
import Langlands.Geometry.Building.TorusRestrictedRootFixer
import Langlands.Geometry.Building.UnramifiedRootRadicalPositivity

/-! # Recovered models of apartment subsets and nearby root bounds -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped ValuativeRel CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom]

private instance fixerComparisonExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

private instance fixerComparisonExtendedSmooth :
    Smooth (baseChanged F (inertiaFixedField F) G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))

omit [Smooth G.X.hom] in
/-- Literal subset inclusion gives reverse inclusion of full norm-one fixers.
No assertion about constancy of full fixers on facets is used. -/
theorem normOneFixer_le_of_subset {Ω₀ Ω₁ : Set D.Apartment} (hΩ : Ω₁ ⊆ Ω₀) :
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω₀) ≤
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω₁) := by
  intro g hg
  refine ⟨hg.1, D.mem_pointwiseFixer.mpr ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact D.mem_pointwiseFixer.mp hg.2 _ ⟨x, hΩ hx, rfl⟩

omit [Smooth G.X.hom] in
/-- Choose the compatible full and neutral comparison between recovered
fixer models for nested apartment subsets. Hom extension remains explicit. -/
def comparisonOfRecoveredFixerModels
    (hext : IntegralModel.UnramifiedSmoothHomExtensionStatement.{u})
    {L₀ L₁ : RelativeComponentModelData ↥𝒪[F] F G}
    {E₀ E₁ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (e₀ : UnramifiedComponentModelRecovery L₀ E₀)
    (e₁ : UnramifiedComponentModelRecovery L₁ E₁)
    {Ω₀ Ω₁ : Set D.Apartment} (hΩ : Ω₁ ⊆ Ω₀)
    (hfull₀ : E₀.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω₀))
    (hfull₁ : E₁.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω₁)) :
    RelativeComponentModelHom L₀ L₁ :=
  Classical.choice ((e₀.nonempty_comparison_iff e₁ hext).mpr (by
    rw [hfull₀, hfull₁]
    exact normOneFixer_le_of_subset D hΩ))

section RootBounds

variable
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hS : IsSplitTorus S.toGrp)
  (hopp : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

include hGK hf

/-- A lower root point whose scalar extension fixes an upper apartment
point has nonnegative restricted depth at that point. -/
theorem nonnegative_restrictedDepth_of_extend_mem_reducedFixer
    (x : D.Apartment) {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hfix : rationalExtend F (inertiaFixedField F) G g ∈
      D.reducedFixer (D.apartmentMap x)) :
    0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g := by
  have hfK :
      CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have haK :
      characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a ∈
        relativeRoots (CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
          (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) := by
    rw [hfK]
    exact (mem_roots_baseChange_iff (K := inertiaFixedField F) G S hS iS a).mpr ha
  have hgrootK := rationalExtend_mem_rootGroupPoints
    (K := inertiaFixedField F) iS a hg
  rw [← hfK] at hgrootK
  have hdepth : rationalExtend F (inertiaFixedField F) G g ∈
      torusRestrictedRootDepthSubgroup x.isValuation
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a) 0 := by
    rw [← D.restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero hGK hiT
      (hS.baseChange (algebraBaseMap F (inertiaFixedField F))) hopp _ _ haK.1 x]
    exact ⟨hgrootK, hfix⟩
  have hfil : g ∈ rootFiltration iS
      (torusFieldRestrictedRootFunctionFamily
        (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
        (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)) a 0 := by
    rw [rootFiltration_torusFieldRestrictedRootFunctionFamily iS hS
      hiT.isSplitSubtorus.1 hopp _ _ hfK a ha 0]
    exact hdepth
  simpa using hfil.2

/-- Exact full recovery and a one-sided upper fixer bound suffice for
integral root points. An equality with a singleton fixer is unnecessary. -/
theorem nonnegative_restrictedDepth_of_full_integralPoints_le_fixer
    {L : RelativeComponentModelData ↥𝒪[F] F G}
    {E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (e : UnramifiedComponentModelRecovery L E)
    (x : D.Apartment)
    (hfix : E.full.integralPoints ≤ D.reducedFixer (D.apartmentMap x))
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgi : g ∈ L.full.integralPoints) :
    0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g := by
  apply nonnegative_restrictedDepth_of_extend_mem_reducedFixer
    D hGK hiT f hf hS hopp x ha hg
  apply hfix
  rwa [e.full_integralPoints_eq_comap] at hgi

/-- A recovered model fixing an apartment subset bounds the depth at every
point of that subset, including the translated point in a two-point set. -/
theorem nonnegative_restrictedDepth_of_integralPoints_fix_set
    {L : RelativeComponentModelData ↥𝒪[F] F G}
    {E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (e : UnramifiedComponentModelRecovery L E)
    {Ω : Set D.Apartment}
    (hfix : E.full.integralPoints ≤ D.pointwiseFixer (D.apartmentMap '' Ω))
    {x : D.Apartment} (hx : x ∈ Ω)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgi : g ∈ L.neutral.integralPoints) :
    0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g := by
  apply nonnegative_restrictedDepth_of_full_integralPoints_le_fixer
    D hGK hiT f hf hS hopp e x
    (fun g hg => D.mem_reducedFixer.mpr
      (D.mem_pointwiseFixer.mp (hfix hg) _ ⟨x, hx, rfl⟩)) ha hg
  exact L.neutralPoints_le_full (L.neutralPoints_eq.symm ▸ hgi)

/-- Nearby recovered parabolic source models require only an upper full
fixer bound to supply all the lower integral-root comparisons. -/
theorem parabolicRootComparisonsNear_of_recoveredFixerModels
    (target : RelativeComponentModelData ↥𝒪[F] F G) (x : D.Apartment)
    (hmodels : ∀ v : V S, ∀ᶠ t : ℝ in 𝓝 0,
      ∃ (source : RelativeComponentModelData ↥𝒪[F] F G)
        (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
          (baseChanged F (inertiaFixedField F) G))
        (_e : UnramifiedComponentModelRecovery source E)
        (ρ : RelativeComponentModelHom source target),
        ρ.HasParabolicSpecialFibreImage ∧ ρ.HasParabolicReductionPreimage ∧
          E.full.integralPoints ≤ D.reducedFixer
            (D.apartmentMap (D.descentTranslate f hS x (t • v)))) :
    D.ParabolicRootComparisonsNearDescentTranslations f hS hiT.isSplitSubtorus.1
      hopp iS target x := by
  intro v
  filter_upwards [hmodels v] with t ht
  obtain ⟨source, E, e, ρ, hpar, hpre, hfix⟩ := ht
  refine ⟨source, ρ, hpar, hpre, ?_⟩
  intro a ha g hg hgi
  exact nonnegative_restrictedDepth_of_full_integralPoints_le_fixer
    D hGK hiT f hf hS hopp e _ hfix ha hg
    (source.neutralPoints_le_full (source.neutralPoints_eq.symm ▸ hgi))

end RootBounds

end Langlands.BruhatTits.IntegralModels
