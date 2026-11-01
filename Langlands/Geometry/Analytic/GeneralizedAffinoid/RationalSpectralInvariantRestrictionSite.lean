import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Functoriality of finite spectral-invariant weighted rational sites -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits DomainAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

private theorem invariant_hom_unique {U : OpenSubgroup G}
    {d e : SpectralInvariantChart ρ U} (f g : d ⟶ e) : f = g := by
  apply ObjectProperty.hom_ext
  exact @Subsingleton.elim (Restriction d.obj e.obj) inferInstance _ _

omit [CompleteSpace K] in
private theorem chart_hom_unique {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance _ _

/-- Subgroup restriction retains the actual whole rational presentation. -/
@[simp]
theorem spectralInvariantRestriction_whole {U V : OpenSubgroup G} (h : V ≤ U) :
    (spectralInvariantChartRestriction ρ h).obj (SpectralInvariantChart.whole ρ U) =
      SpectralInvariantChart.whole ρ V :=
  rfl

/-- Subgroup restriction retains the actual intersection presentation. -/
@[simp]
theorem spectralInvariantRestriction_inter {U V : OpenSubgroup G} (h : V ≤ U)
    (d e : SpectralInvariantChart ρ U) :
    (spectralInvariantChartRestriction ρ h).obj (SpectralInvariantChart.inter ρ U d e) =
      SpectralInvariantChart.inter ρ V
        ((spectralInvariantChartRestriction ρ h).obj d)
        ((spectralInvariantChartRestriction ρ h).obj e) :=
  rfl

/-- Every pair of inclusions into restricted domains lifts to the same actual
intersection quotient, even when its source is only V-invariant. -/
def spectralInvariantRestrictionInterLift {U V : OpenSubgroup G} (h : V ≤ U)
    {c : SpectralInvariantChart ρ V} {d e : SpectralInvariantChart ρ U}
    (f : c ⟶ (spectralInvariantChartRestriction ρ h).obj d)
    (g : c ⟶ (spectralInvariantChartRestriction ρ h).obj e) :
    c ⟶ (spectralInvariantChartRestriction ρ h).obj
      (SpectralInvariantChart.inter ρ U d e) :=
  ObjectProperty.homMk (RationalChart.interLift f.hom g.hom)

/-- The image of the constructed invariant intersection cone is a pullback. -/
def spectralInvariantRestrictionMapConeIsLimit {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : SpectralInvariantChart ρ U} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((SpectralInvariantChart.pullbackCone ρ U f g).map
      (spectralInvariantChartRestriction ρ h)) :=
  PullbackCone.IsLimit.mk _ (fun s => spectralInvariantRestrictionInterLift ρ h s.fst s.snd)
    (fun _ => invariant_hom_unique ρ _ _) (fun _ => invariant_hom_unique ρ _ _)
    (fun _ _ _ _ => invariant_hom_unique ρ _ _)

/-- The actual subgroup-change functor preserves terminal objects. -/
instance spectralInvariantRestriction_preservesTerminal {U V : OpenSubgroup G} (h : V ≤ U) :
    PreservesLimit (Functor.empty.{0} (SpectralInvariantChart ρ U))
      (spectralInvariantChartRestriction ρ h) :=
  preservesLimit_of_preserves_limit_cone (SpectralInvariantChart.wholeIsTerminal ρ U)
    ((isLimitMapConeEmptyConeEquiv _ _).symm
      (SpectralInvariantChart.wholeIsTerminal ρ V))

/-- The actual subgroup-change functor preserves pullbacks of inclusions. -/
instance spectralInvariantRestriction_preservesPullback {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : SpectralInvariantChart ρ U} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (spectralInvariantChartRestriction ρ h) :=
  preservesLimit_of_preserves_limit_cone (SpectralInvariantChart.pullbackConeIsLimit ρ U f g)
    (((SpectralInvariantChart.pullbackCone ρ U f g).isLimitMapConeEquiv _).symm
      (spectralInvariantRestrictionMapConeIsLimit ρ h f g))

/-- The image of an invariant covering sieve contains the same finite
point-covering family after restriction. -/
theorem spectralInvariantRestriction_isFiniteCovering_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : SpectralInvariantChart ρ U} {S : Sieve d}
    (hS : SpectralInvariantChart.IsFiniteCovering ρ U S) :
    SpectralInvariantChart.IsFiniteCovering ρ V
      (S.functorPushforward (spectralInvariantChartRestriction ρ h)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (spectralInvariantChartRestriction ρ h).obj (D i),
    fun i => (spectralInvariantChartRestriction ρ h).map (f i), ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (spectralInvariantChartRestriction ρ h) S (hf i)

/-- A finite cover in the image sieve factors through finitely many original
sieve arrows, whose unchanged loci therefore cover the original target. -/
theorem spectralInvariantRestriction_isFiniteCovering_of_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : SpectralInvariantChart ρ U} {S : Sieve d}
    (hS : SpectralInvariantChart.IsFiniteCovering ρ V
      (S.functorPushforward (spectralInvariantChartRestriction ρ h))) :
    SpectralInvariantChart.IsFiniteCovering ρ U S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D g a hg _ using hf
  refine ⟨I, hI, D, g, hg, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, (a i).hom.subset hi⟩

/-- Subgroup restriction preserves and reflects covering of a sieve by a finite
family of actual invariant quotient domains. -/
theorem spectralInvariantRestriction_pushforward_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {d : SpectralInvariantChart ρ U} (S : Sieve d) :
    S.functorPushforward (spectralInvariantChartRestriction ρ h) ∈
        SpectralInvariantChart.finiteRationalTopology ρ V
          ((spectralInvariantChartRestriction ρ h).obj d) ↔
      S ∈ SpectralInvariantChart.finiteRationalTopology ρ U d :=
  ⟨spectralInvariantRestriction_isFiniteCovering_of_pushforward ρ h,
    spectralInvariantRestriction_isFiniteCovering_pushforward ρ h⟩

/-- The subgroup-change functor preserves the finite invariant rational covers. -/
theorem spectralInvariantRestriction_coverPreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CoverPreserving (SpectralInvariantChart.finiteRationalTopology ρ U)
      (SpectralInvariantChart.finiteRationalTopology ρ V)
      (spectralInvariantChartRestriction ρ h) :=
  ⟨fun hS => spectralInvariantRestriction_isFiniteCovering_pushforward ρ h hS⟩

/-- A finite family generates a covering sieve before subgroup restriction
exactly when its image family does afterwards. -/
theorem spectralInvariantRestriction_ofArrows_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {I : Type u} [Finite I] {d : SpectralInvariantChart ρ U}
    (D : I → SpectralInvariantChart ρ U) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows (fun i => (spectralInvariantChartRestriction ρ h).obj (D i))
        (fun i => (spectralInvariantChartRestriction ρ h).map (f i)) ∈
        SpectralInvariantChart.finiteRationalTopology ρ V
          ((spectralInvariantChartRestriction ρ h).obj d) ↔
      Sieve.ofArrows D f ∈ SpectralInvariantChart.finiteRationalTopology ρ U d := by
  rw [SpectralInvariantChart.ofArrows_mem_finiteRationalTopology_iff,
    SpectralInvariantChart.ofArrows_mem_finiteRationalTopology_iff]
  rfl

/-- The intersection lift preserves compatible families even for comparison
domains which are only invariant under the smaller subgroup. -/
theorem spectralInvariantRestriction_compatiblePreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CompatiblePreserving.{w} (SpectralInvariantChart.finiteRationalTopology ρ V)
      (spectralInvariantChartRestriction ρ h) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l := spectralInvariantRestrictionInterLift ρ h f₁ f₂
  have heq := hx (SpectralInvariantChart.interLeft ρ U Y₁ Y₂)
    (SpectralInvariantChart.interRight ρ U Y₁ Y₂) hg₁ hg₂ (invariant_hom_unique ρ _ _)
  have heq' := congrArg (ℱ.obj.map l.op) heq
  have e₁ : l ≫ (spectralInvariantChartRestriction ρ h).map
      (SpectralInvariantChart.interLeft ρ U Y₁ Y₂) = f₁ := invariant_hom_unique ρ _ _
  have e₂ : l ≫ (spectralInvariantChartRestriction ρ h).map
      (SpectralInvariantChart.interRight ρ U Y₁ Y₂) = f₂ := invariant_hom_unique ρ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact heq'

/-- Subgroup restriction is continuous for the actual finite invariant sites. -/
instance spectralInvariantRestriction_isContinuous {U V : OpenSubgroup G} (h : V ≤ U) :
    (spectralInvariantChartRestriction ρ h).IsContinuous
      (SpectralInvariantChart.finiteRationalTopology ρ U)
      (SpectralInvariantChart.finiteRationalTopology ρ V) :=
  Functor.isContinuous_of_coverPreserving
    (spectralInvariantRestriction_compatiblePreserving ρ h)
    (spectralInvariantRestriction_coverPreserving ρ h)

/-- Precomposition with subgroup change sends sheaves on V-invariant rational
domains to sheaves on U-invariant rational domains, for categorical coefficients. -/
def spectralInvariantSheafRestriction {U V : OpenSubgroup G} (h : V ≤ U)
    (E : Type w) [Category.{w'} E] :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ V) E ⥤
      Sheaf (SpectralInvariantChart.finiteRationalTopology ρ U) E :=
  (spectralInvariantChartRestriction ρ h).sheafPushforwardContinuous E
    (SpectralInvariantChart.finiteRationalTopology ρ U)
    (SpectralInvariantChart.finiteRationalTopology ρ V)

/-- The sheaf functor retains exactly the presheaf obtained by precomposition. -/
theorem spectralInvariantSheafRestriction_obj {U V : OpenSubgroup G} (h : V ≤ U)
    (E : Type w) [Category.{w'} E]
    (F : Sheaf (SpectralInvariantChart.finiteRationalTopology ρ V) E) :
    ((spectralInvariantSheafRestriction ρ h E).obj F).obj =
      (spectralInvariantChartRestriction ρ h).op ⋙ F.obj :=
  rfl


/-- The original full inclusion of invariant charts into all weighted charts. -/
abbrev spectralInvariantChartInclusion (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ RationalChart K A :=
  (spectralInvariantChartProperty ρ H).ι

/-- An arbitrary actual rational source with restrictions to both invariant
charts restricts to their unchanged weighted intersection. -/
def spectralInvariantInclusionInterLift (H : OpenSubgroup G)
    {c : RationalChart K A} {d e : SpectralInvariantChart ρ H}
    (f : c ⟶ (spectralInvariantChartInclusion ρ H).obj d)
    (g : c ⟶ (spectralInvariantChartInclusion ρ H).obj e) :
    c ⟶ (spectralInvariantChartInclusion ρ H).obj
      (SpectralInvariantChart.inter ρ H d e) :=
  RationalChart.interLift f g

/-- Forgetting invariance retains the actual intersection pullback cone. -/
def spectralInvariantInclusionMapConeIsLimit (H : OpenSubgroup G)
    {d e t : SpectralInvariantChart ρ H} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((SpectralInvariantChart.pullbackCone ρ H f g).map
      (spectralInvariantChartInclusion ρ H)) :=
  PullbackCone.IsLimit.mk _ (fun s => spectralInvariantInclusionInterLift ρ H s.fst s.snd)
    (fun _ => chart_hom_unique _ _) (fun _ => chart_hom_unique _ _)
    (fun _ _ _ _ => chart_hom_unique _ _)

/-- The original whole rational quotient stays terminal after forgetting invariance. -/
instance spectralInvariantInclusion_preservesTerminal (H : OpenSubgroup G) :
    PreservesLimit (Functor.empty.{0} (SpectralInvariantChart ρ H))
      (spectralInvariantChartInclusion ρ H) :=
  preservesLimit_of_preserves_limit_cone (SpectralInvariantChart.wholeIsTerminal ρ H)
    ((isLimitMapConeEmptyConeEquiv _ _).symm (RationalChart.wholeIsTerminal K A))

/-- Forgetting invariance preserves the constructed pullbacks of restrictions. -/
instance spectralInvariantInclusion_preservesPullback (H : OpenSubgroup G)
    {d e t : SpectralInvariantChart ρ H} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (spectralInvariantChartInclusion ρ H) :=
  preservesLimit_of_preserves_limit_cone (SpectralInvariantChart.pullbackConeIsLimit ρ H f g)
    (((SpectralInvariantChart.pullbackCone ρ H f g).isLimitMapConeEquiv _).symm
      (spectralInvariantInclusionMapConeIsLimit ρ H f g))

/-- An invariant covering sieve gives the same finite ordinary point cover. -/
theorem spectralInvariantInclusion_isFiniteCovering_pushforward (H : OpenSubgroup G)
    {d : SpectralInvariantChart ρ H} {S : Sieve d}
    (hS : SpectralInvariantChart.IsFiniteCovering ρ H S) :
    RationalChart.IsFiniteCovering
      (S.functorPushforward (spectralInvariantChartInclusion ρ H)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (D i).obj, fun i => (f i).hom, ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (spectralInvariantChartInclusion ρ H) S (hf i)

/-- Every finite cover in the ordinary image sieve factors through finitely
many original invariant sieve arrows, whose loci still cover. -/
theorem spectralInvariantInclusion_isFiniteCovering_of_pushforward (H : OpenSubgroup G)
    {d : SpectralInvariantChart ρ H} {S : Sieve d}
    (hS : RationalChart.IsFiniteCovering
      (S.functorPushforward (spectralInvariantChartInclusion ρ H))) :
    SpectralInvariantChart.IsFiniteCovering ρ H S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D g a hg _ using hf
  refine ⟨I, hI, D, g, hg, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, (a i).subset hi⟩

/-- Forgetting invariance preserves and reflects covering of every invariant sieve. -/
theorem spectralInvariantInclusion_pushforward_mem_iff (H : OpenSubgroup G)
    {d : SpectralInvariantChart ρ H} (S : Sieve d) :
    S.functorPushforward (spectralInvariantChartInclusion ρ H) ∈
        RationalChart.finiteRationalTopology K A d.obj ↔
      S ∈ SpectralInvariantChart.finiteRationalTopology ρ H d :=
  ⟨spectralInvariantInclusion_isFiniteCovering_of_pushforward ρ H,
    spectralInvariantInclusion_isFiniteCovering_pushforward ρ H⟩

/-- Forgetting invariance preserves the actual finite rational covers. -/
theorem spectralInvariantInclusion_coverPreserving (H : OpenSubgroup G) :
    CoverPreserving (SpectralInvariantChart.finiteRationalTopology ρ H)
      (RationalChart.finiteRationalTopology K A) (spectralInvariantChartInclusion ρ H) :=
  ⟨fun hS => spectralInvariantInclusion_isFiniteCovering_pushforward ρ H hS⟩

/-- Finite generated covering sieves have the same point criterion on both sites. -/
theorem spectralInvariantInclusion_ofArrows_mem_iff (H : OpenSubgroup G)
    {I : Type u} [Finite I] {d : SpectralInvariantChart ρ H}
    (D : I → SpectralInvariantChart ρ H) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows (fun i => (D i).obj) (fun i => (f i).hom) ∈
        RationalChart.finiteRationalTopology K A d.obj ↔
      Sieve.ofArrows D f ∈ SpectralInvariantChart.finiteRationalTopology ρ H d := by
  rw [RationalChart.ofArrows_mem_finiteRationalTopology_iff,
    SpectralInvariantChart.ofArrows_mem_finiteRationalTopology_iff]

/-- The actual intersection lift compares compatible sections on every ordinary
comparison chart, including charts not invariant under H. -/
theorem spectralInvariantInclusion_compatiblePreserving (H : OpenSubgroup G) :
    CompatiblePreserving.{w} (RationalChart.finiteRationalTopology K A)
      (spectralInvariantChartInclusion ρ H) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l := spectralInvariantInclusionInterLift ρ H f₁ f₂
  have heq := hx (SpectralInvariantChart.interLeft ρ H Y₁ Y₂)
    (SpectralInvariantChart.interRight ρ H Y₁ Y₂) hg₁ hg₂ (invariant_hom_unique ρ _ _)
  have heq' := congrArg (ℱ.obj.map l.op) heq
  have e₁ : l ≫ (spectralInvariantChartInclusion ρ H).map
      (SpectralInvariantChart.interLeft ρ H Y₁ Y₂) = f₁ := chart_hom_unique _ _
  have e₂ : l ≫ (spectralInvariantChartInclusion ρ H).map
      (SpectralInvariantChart.interRight ρ H Y₁ Y₂) = f₂ := chart_hom_unique _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact heq'

/-- The full invariant-chart inclusion is continuous for the actual finite sites. -/
instance spectralInvariantInclusion_isContinuous (H : OpenSubgroup G) :
    (spectralInvariantChartInclusion ρ H).IsContinuous
      (SpectralInvariantChart.finiteRationalTopology ρ H)
      (RationalChart.finiteRationalTopology K A) :=
  Functor.isContinuous_of_coverPreserving
    (spectralInvariantInclusion_compatiblePreserving ρ H)
    (spectralInvariantInclusion_coverPreserving ρ H)

/-- Ordinary sheaves restrict by exact precomposition to the invariant site. -/
def spectralInvariantSheafInclusion (H : OpenSubgroup G) (E : Type w) [Category.{w'} E] :
    Sheaf (RationalChart.finiteRationalTopology K A) E ⥤
      Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H) E :=
  (spectralInvariantChartInclusion ρ H).sheafPushforwardContinuous E
    (SpectralInvariantChart.finiteRationalTopology ρ H)
    (RationalChart.finiteRationalTopology K A)

/-- The restricted sheaf keeps exactly the original presheaf on invariant charts. -/
theorem spectralInvariantSheafInclusion_obj (H : OpenSubgroup G)
    (E : Type w) [Category.{w'} E]
    (F : Sheaf (RationalChart.finiteRationalTopology K A) E) :
    ((spectralInvariantSheafInclusion ρ H E).obj F).obj =
      (spectralInvariantChartInclusion ρ H).op ⋙ F.obj := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
