import Langlands.Geometry.Analytic.OriginalDomainTopology
import Langlands.Geometry.Analytic.AtlasTopology.LocallyConstant
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Locally constant sections on actual original-chart domains -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {A : Type z} {S T : OriginalChartDomain a}

/-- Restrict an actual locally constant function along a domain inclusion. -/
def locallyConstantRestrict (hST : S ≤ T) (f : LocallyConstant T A) :
    LocallyConstant S A :=
  f.comap ⟨Set.inclusion hST, continuous_inclusion hST⟩

@[simp]
theorem locallyConstantRestrict_apply (hST : S ≤ T) (f : LocallyConstant T A) (x : S) :
    locallyConstantRestrict hST f x = f (Set.inclusion hST x) := rfl

/-- The full locally constant function sets, with actual inclusion pullbacks. -/
abbrev locallyConstantPresheaf (a : IndexedAffinoidAtlas.{u, v, w} K X) (A : Type z) :
    (OriginalChartDomain a)ᵒᵖ ⥤ Type (max v z) where
  obj S := LocallyConstant S.unop A
  map f := TypeCat.ofHom (locallyConstantRestrict (leOfHom f.unop))
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    ext x
    rfl

variable {R : Sieve S}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf a A) R.arrows)
  (hp : p.Compatible)

include hp in
/-- Matching along the actual intersection gives pointwise agreement at
every common point of two sieve domains. -/
theorem locallyConstantCompatible_apply {U V : OriginalChartDomain a}
    (f : U ⟶ S) (g : V ⟶ S) (hf : R f) (hg : R g)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    (p f hf : LocallyConstant U A) ⟨x, hxU⟩ =
      (p g hg : LocallyConstant V A) ⟨x, hxV⟩ := by
  have h := hp (homOfLE (inf_le_left : U ⊓ V ≤ U))
    (homOfLE (inf_le_right : U ⊓ V ≤ V)) hf hg (Subsingleton.elim _ _)
  exact congrArg
    (fun q : LocallyConstant (U ⊓ V : OriginalChartDomain a) A => q ⟨x, hxU, hxV⟩) h

include hp in
/-- Point coverage constructs a coefficient value; matching proves that it
recovers every local value at that point. No coefficient choice is supplied. -/
theorem exists_locallyConstantSieveValue (hR : IsCovering R) (x : S) :
    ∃ c : A, ∀ (V : OriginalChartDomain a) (f : V ⟶ S) (hf : R f)
      (hxV : x.val ∈ V), c = (p f hf : LocallyConstant V A) ⟨x.val, hxV⟩ := by
  obtain ⟨U, hUS, hRU, hxU⟩ := hR.exists_mem x.property
  refine ⟨(p (homOfLE hUS) hRU : LocallyConstant U A) ⟨x.val, hxU⟩, ?_⟩
  intro V f hf hxV
  exact locallyConstantCompatible_apply p hp (homOfLE hUS) f hRU hf x.val hxU hxV

/-- The glued function chooses the uniquely determined coefficient value at
each point from the actual compatible family. -/
def locallyConstantSieveGlueFun (hR : IsCovering R) : S → A :=
  fun x => (exists_locallyConstantSieveValue p hp hR x).choose

theorem locallyConstantSieveGlueFun_apply (hR : IsCovering R)
    {V : OriginalChartDomain a} (f : V ⟶ S) (hf : R f)
    (x : S) (hxV : x.val ∈ V) :
    locallyConstantSieveGlueFun p hp hR x =
      (p f hf : LocallyConstant V A) ⟨x.val, hxV⟩ :=
  (exists_locallyConstantSieveValue p hp hR x).choose_spec V f hf hxV

/-- The quasinet local-constancy criterion upgrades the constructed function
to an actual locally constant section on the target domain. -/
def locallyConstantSieveGlue (hR : IsCovering R) : LocallyConstant S A where
  toFun := locallyConstantSieveGlueFun p hp hR
  isLocallyConstant := by
    apply (AtlasTopology.LocallyRefines.isLocallyConstant_iff hR _).mpr
    rintro V ⟨D, hDS, hRD, rfl⟩ hVS
    have he : (fun x : D => locallyConstantSieveGlueFun p hp hR
        (Set.inclusion hVS x)) =
          ⇑(p (homOfLE hDS) hRD : LocallyConstant D A) := by
      funext x
      exact locallyConstantSieveGlueFun_apply p hp hR (homOfLE hDS) hRD
        (Set.inclusion hVS x) x.property
    exact (congrArg (fun f : D → A => IsLocallyConstant f) he).mpr
      (p (homOfLE hDS) hRD : LocallyConstant D A).isLocallyConstant

@[simp]
theorem locallyConstantSieveGlue_apply (hR : IsCovering R)
    {V : OriginalChartDomain a} (f : V ⟶ S) (hf : R f) (x : V) :
    locallyConstantSieveGlue p hp hR (Set.inclusion (leOfHom f) x) =
      (p f hf : LocallyConstant V A) x :=
  locallyConstantSieveGlueFun_apply p hp hR f hf _ x.property

/-- Every compatible family on every covering sieve has exactly one actual
locally constant amalgamation, including empty domains and coefficient sets. -/
theorem locallyConstantPresheaf_isSheaf
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (A : Type z) :
    Presheaf.IsSheaf (quasinetTopology a) (locallyConstantPresheaf a A) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro S R hR p hp
  refine ⟨locallyConstantSieveGlue p hp hR, ?_, ?_⟩
  · intro V f hf
    ext x
    exact locallyConstantSieveGlue_apply p hp hR f hf x
  · intro f hf
    ext x
    obtain ⟨V, hVS, hRV, hxV⟩ := hR.exists_mem x.property
    have he := congrArg (fun q : LocallyConstant V A => q ⟨x.val, hxV⟩)
      (hf (homOfLE hVS) hRV)
    exact he.trans
      (locallyConstantSieveGlueFun_apply p hp hR (homOfLE hVS) hRV x hxV).symm

/-- The constructed locally constant function sheaf on the existing actual
fixed-original-chart quasinet site. -/
def locallyConstantSheaf (a : IndexedAffinoidAtlas.{u, v, w} K X) (A : Type z) :
    Sheaf (quasinetTopology a) (Type (max v z)) :=
  ⟨locallyConstantPresheaf a A, locallyConstantPresheaf_isSheaf a A⟩

end Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain
