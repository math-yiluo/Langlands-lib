import Langlands.Geometry.Analytic.StrictTestDomain.InvariantRationalSite
import Langlands.Geometry.Analytic.StrictTestDomain.InvariantSubgroupRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Subgroup change on finite invariant rational sites -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

private theorem invariant_hom_unique {U : OpenSubgroup G}
    {d e : ρ.InvariantRationalDomain U} (f g : d ⟶ e) : f = g := by
  apply ObjectProperty.hom_ext
  exact (inferInstance : Subsingleton (RationalData.Inclusion d.obj e.obj)).elim _ _

/-- Subgroup restriction retains the actual whole rational presentation. -/
@[simp]
theorem invariantRestriction_whole {U V : OpenSubgroup G} (h : V ≤ U) :
    (ρ.invariantRestrictionFunctor h).obj (InvariantRationalDomain.whole ρ U) =
      InvariantRationalDomain.whole ρ V :=
  rfl

/-- Subgroup restriction retains the actual intersection presentation. -/
@[simp]
theorem invariantRestriction_inter {U V : OpenSubgroup G} (h : V ≤ U)
    (d e : ρ.InvariantRationalDomain U) :
    (ρ.invariantRestrictionFunctor h).obj (InvariantRationalDomain.inter ρ U d e) =
      InvariantRationalDomain.inter ρ V
        ((ρ.invariantRestrictionFunctor h).obj d)
        ((ρ.invariantRestrictionFunctor h).obj e) :=
  rfl

/-- Every pair of inclusions into restricted domains lifts to the same actual
intersection quotient, even when its source is only V-invariant. -/
def invariantRestrictionInterLift {U V : OpenSubgroup G} (h : V ≤ U)
    {c : ρ.InvariantRationalDomain V} {d e : ρ.InvariantRationalDomain U}
    (f : c ⟶ (ρ.invariantRestrictionFunctor h).obj d)
    (g : c ⟶ (ρ.invariantRestrictionFunctor h).obj e) :
    c ⟶ (ρ.invariantRestrictionFunctor h).obj
      (InvariantRationalDomain.inter ρ U d e) :=
  ObjectProperty.homMk (RationalData.interLift f.hom g.hom)

/-- The image of the constructed invariant intersection cone is a pullback. -/
def invariantRestrictionMapConeIsLimit {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : ρ.InvariantRationalDomain U} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((InvariantRationalDomain.pullbackCone ρ U f g).map
      (ρ.invariantRestrictionFunctor h)) :=
  PullbackCone.IsLimit.mk _ (fun s => ρ.invariantRestrictionInterLift h s.fst s.snd)
    (fun _ => invariant_hom_unique ρ _ _) (fun _ => invariant_hom_unique ρ _ _)
    (fun _ _ _ _ => invariant_hom_unique ρ _ _)

/-- The actual subgroup-change functor preserves terminal objects. -/
instance invariantRestriction_preservesTerminal {U V : OpenSubgroup G} (h : V ≤ U) :
    PreservesLimit (Functor.empty.{0} (ρ.InvariantRationalDomain U))
      (ρ.invariantRestrictionFunctor h) :=
  preservesLimit_of_preserves_limit_cone (InvariantRationalDomain.wholeIsTerminal ρ U)
    ((isLimitMapConeEmptyConeEquiv _ _).symm
      (InvariantRationalDomain.wholeIsTerminal ρ V))

/-- The actual subgroup-change functor preserves pullbacks of inclusions. -/
instance invariantRestriction_preservesPullback {U V : OpenSubgroup G} (h : V ≤ U)
    {d e t : ρ.InvariantRationalDomain U} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (ρ.invariantRestrictionFunctor h) :=
  preservesLimit_of_preserves_limit_cone (InvariantRationalDomain.pullbackConeIsLimit ρ U f g)
    (((InvariantRationalDomain.pullbackCone ρ U f g).isLimitMapConeEquiv _).symm
      (ρ.invariantRestrictionMapConeIsLimit h f g))

/-- The image of an invariant covering sieve contains the same finite
point-covering family after restriction. -/
theorem invariantRestriction_isFiniteCovering_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : InvariantRationalDomain.IsFiniteCovering ρ U S) :
    InvariantRationalDomain.IsFiniteCovering ρ V
      (S.functorPushforward (ρ.invariantRestrictionFunctor h)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (ρ.invariantRestrictionFunctor h).obj (D i),
    fun i => (ρ.invariantRestrictionFunctor h).map (f i), ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (ρ.invariantRestrictionFunctor h) S (hf i)

/-- A finite cover in the image sieve factors through finitely many original
sieve arrows, whose unchanged loci therefore cover the original target. -/
theorem invariantRestriction_isFiniteCovering_of_pushforward {U V : OpenSubgroup G}
    (h : V ≤ U) {d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : InvariantRationalDomain.IsFiniteCovering ρ V
      (S.functorPushforward (ρ.invariantRestrictionFunctor h))) :
    InvariantRationalDomain.IsFiniteCovering ρ U S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D g a hg _ using hf
  refine ⟨I, hI, D, g, hg, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, (a i).hom.subset hi⟩

/-- Subgroup restriction preserves and reflects covering of a sieve by a finite
family of actual invariant quotient domains. -/
theorem invariantRestriction_pushforward_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {d : ρ.InvariantRationalDomain U} (S : Sieve d) :
    S.functorPushforward (ρ.invariantRestrictionFunctor h) ∈
        InvariantRationalDomain.finiteRationalTopology ρ V
          ((ρ.invariantRestrictionFunctor h).obj d) ↔
      S ∈ InvariantRationalDomain.finiteRationalTopology ρ U d :=
  ⟨ρ.invariantRestriction_isFiniteCovering_of_pushforward h,
    ρ.invariantRestriction_isFiniteCovering_pushforward h⟩

/-- The subgroup-change functor preserves the finite invariant rational covers. -/
theorem invariantRestriction_coverPreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CoverPreserving (InvariantRationalDomain.finiteRationalTopology ρ U)
      (InvariantRationalDomain.finiteRationalTopology ρ V)
      (ρ.invariantRestrictionFunctor h) :=
  ⟨fun hS => ρ.invariantRestriction_isFiniteCovering_pushforward h hS⟩

/-- A finite family generates a covering sieve before subgroup restriction
exactly when its image family does afterwards. -/
theorem invariantRestriction_ofArrows_mem_iff {U V : OpenSubgroup G} (h : V ≤ U)
    {I : Type u} [Finite I] {d : ρ.InvariantRationalDomain U}
    (D : I → ρ.InvariantRationalDomain U) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows (fun i => (ρ.invariantRestrictionFunctor h).obj (D i))
        (fun i => (ρ.invariantRestrictionFunctor h).map (f i)) ∈
        InvariantRationalDomain.finiteRationalTopology ρ V
          ((ρ.invariantRestrictionFunctor h).obj d) ↔
      Sieve.ofArrows D f ∈ InvariantRationalDomain.finiteRationalTopology ρ U d := by
  rw [InvariantRationalDomain.ofArrows_mem_finiteRationalTopology_iff,
    InvariantRationalDomain.ofArrows_mem_finiteRationalTopology_iff]
  rfl

/-- The intersection lift preserves compatible families even for comparison
domains which are only invariant under the smaller subgroup. -/
theorem invariantRestriction_compatiblePreserving {U V : OpenSubgroup G} (h : V ≤ U) :
    CompatiblePreserving.{w} (InvariantRationalDomain.finiteRationalTopology ρ V)
      (ρ.invariantRestrictionFunctor h) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l := ρ.invariantRestrictionInterLift h f₁ f₂
  have heq := hx (InvariantRationalDomain.interLeft ρ U Y₁ Y₂)
    (InvariantRationalDomain.interRight ρ U Y₁ Y₂) hg₁ hg₂ (invariant_hom_unique ρ _ _)
  have heq' := congrArg (ℱ.obj.map l.op) heq
  have e₁ : l ≫ (ρ.invariantRestrictionFunctor h).map
      (InvariantRationalDomain.interLeft ρ U Y₁ Y₂) = f₁ := invariant_hom_unique ρ _ _
  have e₂ : l ≫ (ρ.invariantRestrictionFunctor h).map
      (InvariantRationalDomain.interRight ρ U Y₁ Y₂) = f₂ := invariant_hom_unique ρ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact heq'

/-- Subgroup restriction is continuous for the actual finite invariant sites. -/
instance invariantRestriction_isContinuous {U V : OpenSubgroup G} (h : V ≤ U) :
    (ρ.invariantRestrictionFunctor h).IsContinuous
      (InvariantRationalDomain.finiteRationalTopology ρ U)
      (InvariantRationalDomain.finiteRationalTopology ρ V) :=
  Functor.isContinuous_of_coverPreserving
    (ρ.invariantRestriction_compatiblePreserving h)
    (ρ.invariantRestriction_coverPreserving h)

/-- Precomposition with subgroup change sends sheaves on V-invariant rational
domains to sheaves on U-invariant rational domains, for categorical coefficients. -/
def invariantSheafRestriction {U V : OpenSubgroup G} (h : V ≤ U)
    (A : Type w) [Category.{w'} A] :
    Sheaf (InvariantRationalDomain.finiteRationalTopology ρ V) A ⥤
      Sheaf (InvariantRationalDomain.finiteRationalTopology ρ U) A :=
  (ρ.invariantRestrictionFunctor h).sheafPushforwardContinuous A
    (InvariantRationalDomain.finiteRationalTopology ρ U)
    (InvariantRationalDomain.finiteRationalTopology ρ V)

/-- The sheaf functor retains exactly the presheaf obtained by precomposition. -/
theorem invariantSheafRestriction_obj {U V : OpenSubgroup G} (h : V ≤ U)
    (A : Type w) [Category.{w'} A]
    (F : Sheaf (InvariantRationalDomain.finiteRationalTopology ρ V) A) :
    ((ρ.invariantSheafRestriction h A).obj F).obj =
      (ρ.invariantRestrictionFunctor h).op ⋙ F.obj :=
  rfl

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
