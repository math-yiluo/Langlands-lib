import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Functoriality of finite norm-invariant weighted rational sites -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

omit [CompleteSpace K] in
private theorem invariant_hom_unique {U : OpenSubgroup G}
    {d e : NormInvariantChart ρ hρ U} (f g : d ⟶ e) : f = g := by
  apply ObjectProperty.hom_ext
  exact @Subsingleton.elim (Restriction d.obj e.obj) inferInstance _ _

omit [CompleteSpace K] in
private theorem chart_hom_unique {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance _ _

omit [CompleteSpace K] in
/-- Subgroup restriction retains the actual whole rational presentation. -/
@[simp]
theorem normInvariantRestriction_whole {U V : OpenSubgroup G} (h : V ≤ U) :
    (normInvariantChartRestriction ρ hρ h).obj (NormInvariantChart.whole ρ hρ U) =
      NormInvariantChart.whole ρ hρ V :=
  rfl

omit [CompleteSpace K] in
/-- Subgroup restriction retains the actual intersection presentation. -/
@[simp]
theorem normInvariantRestriction_inter {U V : OpenSubgroup G} (h : V ≤ U)
    (d e : NormInvariantChart ρ hρ U) :
    (normInvariantChartRestriction ρ hρ h).obj (NormInvariantChart.inter ρ hρ U d e) =
      NormInvariantChart.inter ρ hρ V
        ((normInvariantChartRestriction ρ hρ h).obj d)
        ((normInvariantChartRestriction ρ hρ h).obj e) :=
  rfl

/-- Every pair of inclusions into restricted domains lifts to the same actual
intersection quotient, even when its source is only V-invariant. -/
def normInvariantRestrictionInterLift {U V : OpenSubgroup G} (h : V ≤ U)
    {c : NormInvariantChart ρ hρ V} {d e : NormInvariantChart ρ hρ U}
    (f : c ⟶ (normInvariantChartRestriction ρ hρ h).obj d)
    (g : c ⟶ (normInvariantChartRestriction ρ hρ h).obj e) :
    c ⟶ (normInvariantChartRestriction ρ hρ h).obj
      (NormInvariantChart.inter ρ hρ U d e) :=
  ObjectProperty.homMk (RationalChart.interLift f.hom g.hom)

/-- The image of the constructed invariant intersection cone is a pullback. -/
def normInvariantRestrictionMapConeIsLimit {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : NormInvariantChart ρ hρ U} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((NormInvariantChart.pullbackCone ρ hρ U f g).map
      (normInvariantChartRestriction ρ hρ h)) :=
  PullbackCone.IsLimit.mk _ (fun s => normInvariantRestrictionInterLift ρ hρ h s.fst s.snd)
    (fun _ => invariant_hom_unique ρ hρ _ _) (fun _ => invariant_hom_unique ρ hρ _ _)
    (fun _ _ _ _ => invariant_hom_unique ρ hρ _ _)

/-- The actual subgroup-change functor preserves terminal objects. -/
instance normInvariantRestriction_preservesTerminal {U V : OpenSubgroup G} (h : V ≤ U) :
    PreservesLimit (Functor.empty.{0} (NormInvariantChart ρ hρ U))
      (normInvariantChartRestriction ρ hρ h) :=
  preservesLimit_of_preserves_limit_cone (NormInvariantChart.wholeIsTerminal ρ hρ U)
    ((isLimitMapConeEmptyConeEquiv _ _).symm
      (NormInvariantChart.wholeIsTerminal ρ hρ V))

/-- The actual subgroup-change functor preserves pullbacks of inclusions. -/
instance normInvariantRestriction_preservesPullback {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : NormInvariantChart ρ hρ U} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (normInvariantChartRestriction ρ hρ h) :=
  preservesLimit_of_preserves_limit_cone (NormInvariantChart.pullbackConeIsLimit ρ hρ U f g)
    (((NormInvariantChart.pullbackCone ρ hρ U f g).isLimitMapConeEquiv _).symm
      (normInvariantRestrictionMapConeIsLimit ρ hρ h f g))

omit [CompleteSpace K] in
/-- The image of an invariant covering sieve contains the same finite
point-covering family after restriction. -/
theorem normInvariantRestriction_isFiniteCovering_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : NormInvariantChart ρ hρ U} {S : Sieve d}
    (hS : NormInvariantChart.IsFiniteCovering ρ hρ U S) :
    NormInvariantChart.IsFiniteCovering ρ hρ V
      (S.functorPushforward (normInvariantChartRestriction ρ hρ h)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (normInvariantChartRestriction ρ hρ h).obj (D i),
    fun i => (normInvariantChartRestriction ρ hρ h).map (f i), ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (normInvariantChartRestriction ρ hρ h) S (hf i)

omit [CompleteSpace K] in
/-- A finite cover in the image sieve factors through finitely many original
sieve arrows, whose unchanged loci therefore cover the original target. -/
theorem normInvariantRestriction_isFiniteCovering_of_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : NormInvariantChart ρ hρ U} {S : Sieve d}
    (hS : NormInvariantChart.IsFiniteCovering ρ hρ V
      (S.functorPushforward (normInvariantChartRestriction ρ hρ h))) :
    NormInvariantChart.IsFiniteCovering ρ hρ U S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D g a hg _ using hf
  refine ⟨I, hI, D, g, hg, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, (a i).hom.subset hi⟩

/-- Subgroup restriction preserves and reflects covering of a sieve by a finite
family of actual invariant quotient domains. -/
theorem normInvariantRestriction_pushforward_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {d : NormInvariantChart ρ hρ U} (S : Sieve d) :
    S.functorPushforward (normInvariantChartRestriction ρ hρ h) ∈
        NormInvariantChart.finiteRationalTopology ρ hρ V
          ((normInvariantChartRestriction ρ hρ h).obj d) ↔
      S ∈ NormInvariantChart.finiteRationalTopology ρ hρ U d :=
  ⟨normInvariantRestriction_isFiniteCovering_of_pushforward ρ hρ h,
    normInvariantRestriction_isFiniteCovering_pushforward ρ hρ h⟩

/-- The subgroup-change functor preserves the finite invariant rational covers. -/
theorem normInvariantRestriction_coverPreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CoverPreserving (NormInvariantChart.finiteRationalTopology ρ hρ U)
      (NormInvariantChart.finiteRationalTopology ρ hρ V)
      (normInvariantChartRestriction ρ hρ h) :=
  ⟨fun hS => normInvariantRestriction_isFiniteCovering_pushforward ρ hρ h hS⟩

/-- A finite family generates a covering sieve before subgroup restriction
exactly when its image family does afterwards. -/
theorem normInvariantRestriction_ofArrows_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {I : Type u} [Finite I] {d : NormInvariantChart ρ hρ U}
    (D : I → NormInvariantChart ρ hρ U) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows (fun i => (normInvariantChartRestriction ρ hρ h).obj (D i))
        (fun i => (normInvariantChartRestriction ρ hρ h).map (f i)) ∈
        NormInvariantChart.finiteRationalTopology ρ hρ V
          ((normInvariantChartRestriction ρ hρ h).obj d) ↔
      Sieve.ofArrows D f ∈ NormInvariantChart.finiteRationalTopology ρ hρ U d := by
  rw [NormInvariantChart.ofArrows_mem_finiteRationalTopology_iff,
    NormInvariantChart.ofArrows_mem_finiteRationalTopology_iff]
  rfl

/-- The intersection lift preserves compatible families even for comparison
domains which are only invariant under the smaller subgroup. -/
theorem normInvariantRestriction_compatiblePreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CompatiblePreserving.{w} (NormInvariantChart.finiteRationalTopology ρ hρ V)
      (normInvariantChartRestriction ρ hρ h) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l := normInvariantRestrictionInterLift ρ hρ h f₁ f₂
  have heq := hx (NormInvariantChart.interLeft ρ hρ U Y₁ Y₂)
    (NormInvariantChart.interRight ρ hρ U Y₁ Y₂) hg₁ hg₂ (invariant_hom_unique ρ hρ _ _)
  have heq' := congrArg (ℱ.obj.map l.op) heq
  have e₁ : l ≫ (normInvariantChartRestriction ρ hρ h).map
      (NormInvariantChart.interLeft ρ hρ U Y₁ Y₂) = f₁ := invariant_hom_unique ρ hρ _ _
  have e₂ : l ≫ (normInvariantChartRestriction ρ hρ h).map
      (NormInvariantChart.interRight ρ hρ U Y₁ Y₂) = f₂ := invariant_hom_unique ρ hρ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact heq'

/-- Subgroup restriction is continuous for the actual finite invariant sites. -/
instance normInvariantRestriction_isContinuous {U V : OpenSubgroup G} (h : V ≤ U) :
    (normInvariantChartRestriction ρ hρ h).IsContinuous
      (NormInvariantChart.finiteRationalTopology ρ hρ U)
      (NormInvariantChart.finiteRationalTopology ρ hρ V) :=
  Functor.isContinuous_of_coverPreserving
    (normInvariantRestriction_compatiblePreserving ρ hρ h)
    (normInvariantRestriction_coverPreserving ρ hρ h)

/-- Precomposition with subgroup change sends sheaves on V-invariant rational
domains to sheaves on U-invariant rational domains, for categorical coefficients. -/
def normInvariantSheafRestriction {U V : OpenSubgroup G} (h : V ≤ U)
    (E : Type w) [Category.{w'} E] :
    Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ V) E ⥤
      Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ U) E :=
  (normInvariantChartRestriction ρ hρ h).sheafPushforwardContinuous E
    (NormInvariantChart.finiteRationalTopology ρ hρ U)
    (NormInvariantChart.finiteRationalTopology ρ hρ V)

/-- The sheaf functor retains exactly the presheaf obtained by precomposition. -/
theorem normInvariantSheafRestriction_obj {U V : OpenSubgroup G} (h : V ≤ U)
    (E : Type w) [Category.{w'} E]
    (F : Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ V) E) :
    ((normInvariantSheafRestriction ρ hρ h E).obj F).obj =
      (normInvariantChartRestriction ρ hρ h).op ⋙ F.obj :=
  rfl


/-- The original full inclusion of invariant charts into all weighted charts. -/
abbrev normInvariantChartInclusion (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ RationalChart K A :=
  (normInvariantChartProperty ρ hρ H).ι

/-- An arbitrary actual rational source with restrictions to both invariant
charts restricts to their unchanged weighted intersection. -/
def normInvariantInclusionInterLift (H : OpenSubgroup G)
    {c : RationalChart K A} {d e : NormInvariantChart ρ hρ H}
    (f : c ⟶ (normInvariantChartInclusion ρ hρ H).obj d)
    (g : c ⟶ (normInvariantChartInclusion ρ hρ H).obj e) :
    c ⟶ (normInvariantChartInclusion ρ hρ H).obj
      (NormInvariantChart.inter ρ hρ H d e) :=
  RationalChart.interLift f g

/-- Forgetting invariance retains the actual intersection pullback cone. -/
def normInvariantInclusionMapConeIsLimit (H : OpenSubgroup G)
    {d e t : NormInvariantChart ρ hρ H} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((NormInvariantChart.pullbackCone ρ hρ H f g).map
      (normInvariantChartInclusion ρ hρ H)) :=
  PullbackCone.IsLimit.mk _ (fun s => normInvariantInclusionInterLift ρ hρ H s.fst s.snd)
    (fun _ => chart_hom_unique _ _) (fun _ => chart_hom_unique _ _)
    (fun _ _ _ _ => chart_hom_unique _ _)

/-- The original whole rational quotient stays terminal after forgetting invariance. -/
instance normInvariantInclusion_preservesTerminal (H : OpenSubgroup G) :
    PreservesLimit (Functor.empty.{0} (NormInvariantChart ρ hρ H))
      (normInvariantChartInclusion ρ hρ H) :=
  preservesLimit_of_preserves_limit_cone (NormInvariantChart.wholeIsTerminal ρ hρ H)
    ((isLimitMapConeEmptyConeEquiv _ _).symm (RationalChart.wholeIsTerminal K A))

/-- Forgetting invariance preserves the constructed pullbacks of restrictions. -/
instance normInvariantInclusion_preservesPullback (H : OpenSubgroup G)
    {d e t : NormInvariantChart ρ hρ H} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (normInvariantChartInclusion ρ hρ H) :=
  preservesLimit_of_preserves_limit_cone (NormInvariantChart.pullbackConeIsLimit ρ hρ H f g)
    (((NormInvariantChart.pullbackCone ρ hρ H f g).isLimitMapConeEquiv _).symm
      (normInvariantInclusionMapConeIsLimit ρ hρ H f g))

omit [CompleteSpace K] in
/-- An invariant covering sieve gives the same finite ordinary point cover. -/
theorem normInvariantInclusion_isFiniteCovering_pushforward (H : OpenSubgroup G)
    {d : NormInvariantChart ρ hρ H} {S : Sieve d}
    (hS : NormInvariantChart.IsFiniteCovering ρ hρ H S) :
    RationalChart.IsFiniteCovering
      (S.functorPushforward (normInvariantChartInclusion ρ hρ H)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (D i).obj, fun i => (f i).hom, ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (normInvariantChartInclusion ρ hρ H) S (hf i)

omit [CompleteSpace K] in
/-- Every finite cover in the ordinary image sieve factors through finitely
many original invariant sieve arrows, whose loci still cover. -/
theorem normInvariantInclusion_isFiniteCovering_of_pushforward (H : OpenSubgroup G)
    {d : NormInvariantChart ρ hρ H} {S : Sieve d}
    (hS : RationalChart.IsFiniteCovering
      (S.functorPushforward (normInvariantChartInclusion ρ hρ H))) :
    NormInvariantChart.IsFiniteCovering ρ hρ H S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D g a hg _ using hf
  refine ⟨I, hI, D, g, hg, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, (a i).subset hi⟩

/-- Forgetting invariance preserves and reflects covering of every invariant sieve. -/
theorem normInvariantInclusion_pushforward_mem_iff (H : OpenSubgroup G)
    {d : NormInvariantChart ρ hρ H} (S : Sieve d) :
    S.functorPushforward (normInvariantChartInclusion ρ hρ H) ∈
        RationalChart.finiteRationalTopology K A d.obj ↔
      S ∈ NormInvariantChart.finiteRationalTopology ρ hρ H d :=
  ⟨normInvariantInclusion_isFiniteCovering_of_pushforward ρ hρ H,
    normInvariantInclusion_isFiniteCovering_pushforward ρ hρ H⟩

/-- Forgetting invariance preserves the actual finite rational covers. -/
theorem normInvariantInclusion_coverPreserving (H : OpenSubgroup G) :
    CoverPreserving (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (RationalChart.finiteRationalTopology K A) (normInvariantChartInclusion ρ hρ H) :=
  ⟨fun hS => normInvariantInclusion_isFiniteCovering_pushforward ρ hρ H hS⟩

/-- Finite generated covering sieves have the same point criterion on both sites. -/
theorem normInvariantInclusion_ofArrows_mem_iff (H : OpenSubgroup G)
    {I : Type u} [Finite I] {d : NormInvariantChart ρ hρ H}
    (D : I → NormInvariantChart ρ hρ H) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows (fun i => (D i).obj) (fun i => (f i).hom) ∈
        RationalChart.finiteRationalTopology K A d.obj ↔
      Sieve.ofArrows D f ∈ NormInvariantChart.finiteRationalTopology ρ hρ H d := by
  rw [RationalChart.ofArrows_mem_finiteRationalTopology_iff,
    NormInvariantChart.ofArrows_mem_finiteRationalTopology_iff]

/-- The actual intersection lift compares compatible sections on every ordinary
comparison chart, including charts not invariant under H. -/
theorem normInvariantInclusion_compatiblePreserving (H : OpenSubgroup G) :
    CompatiblePreserving.{w} (RationalChart.finiteRationalTopology K A)
      (normInvariantChartInclusion ρ hρ H) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l := normInvariantInclusionInterLift ρ hρ H f₁ f₂
  have heq := hx (NormInvariantChart.interLeft ρ hρ H Y₁ Y₂)
    (NormInvariantChart.interRight ρ hρ H Y₁ Y₂) hg₁ hg₂ (invariant_hom_unique ρ hρ _ _)
  have heq' := congrArg (ℱ.obj.map l.op) heq
  have e₁ : l ≫ (normInvariantChartInclusion ρ hρ H).map
      (NormInvariantChart.interLeft ρ hρ H Y₁ Y₂) = f₁ := chart_hom_unique _ _
  have e₂ : l ≫ (normInvariantChartInclusion ρ hρ H).map
      (NormInvariantChart.interRight ρ hρ H Y₁ Y₂) = f₂ := chart_hom_unique _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact heq'

/-- The full invariant-chart inclusion is continuous for the actual finite sites. -/
instance normInvariantInclusion_isContinuous (H : OpenSubgroup G) :
    (normInvariantChartInclusion ρ hρ H).IsContinuous
      (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (RationalChart.finiteRationalTopology K A) :=
  Functor.isContinuous_of_coverPreserving
    (normInvariantInclusion_compatiblePreserving ρ hρ H)
    (normInvariantInclusion_coverPreserving ρ hρ H)

/-- Ordinary sheaves restrict by exact precomposition to the invariant site. -/
def normInvariantSheafInclusion (H : OpenSubgroup G) (E : Type w) [Category.{w'} E] :
    Sheaf (RationalChart.finiteRationalTopology K A) E ⥤
      Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ H) E :=
  (normInvariantChartInclusion ρ hρ H).sheafPushforwardContinuous E
    (NormInvariantChart.finiteRationalTopology ρ hρ H)
    (RationalChart.finiteRationalTopology K A)

/-- The restricted sheaf keeps exactly the original presheaf on invariant charts. -/
theorem normInvariantSheafInclusion_obj (H : OpenSubgroup G)
    (E : Type w) [Category.{w'} E]
    (F : Sheaf (RationalChart.finiteRationalTopology K A) E) :
    ((normInvariantSheafInclusion ρ hρ H E).obj F).obj =
      (normInvariantChartInclusion ρ hρ H).op ⋙ F.obj := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
