import Langlands.AbelianScheme.IsogenyStability
import Langlands.GroupScheme.Rational.Characters
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Central isogenies with their full scheme-theoretic kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H K : GroupScheme S}

/-- Centrality is inclusion of the full range functor in the scheme-theoretic centre. -/
theorem isCentral_iff_range_le_center (i : H ⟶ G) :
    IsCentral i ↔ SubgroupFunctor.range i ≤ center G := by
  constructor
  · rintro hi T x ⟨y, rfl⟩
    exact hi T y
  · intro hi T x
    exact hi T ⟨x, rfl⟩

/-- The range of the actual kernel inclusion consists of exactly the points killed by `f`. -/
theorem mem_range_kernelι_iff (f : G ⟶ H) {T : Over S} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range (kernelι f)).carrier T ↔ x ≫ f.hom.hom = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (kernelPointsEquiv f T y).property
  · intro hx
    exact ⟨(kernelPointsEquiv f T).symm ⟨x, hx⟩,
      congrArg Subtype.val ((kernelPointsEquiv f T).apply_symm_apply ⟨x, hx⟩)⟩

/-- Centrality of the actual kernel, expressed on every test scheme and every restriction. -/
theorem isCentral_kernelι_iff (f : G ⟶ H) :
    IsCentral (kernelι f) ↔
      ∀ (T : Over S) (x : T ⟶ G.X), x ≫ f.hom.hom = 1 →
        x ∈ (center G).carrier T := by
  rw [isCentral_iff_range_le_center]
  constructor
  · intro hf T x hx
    exact hf T ((mem_range_kernelι_iff f x).mpr hx)
  · intro hf T x hx
    exact hf T x ((mem_range_kernelι_iff f x).mp hx)

/-- A finite fppf homomorphism with central scheme-theoretic kernel. Local finite presentation
is explicit so the predicate is meaningful without extra finiteness assumptions on the base. -/
structure IsCentralIsogeny (f : G ⟶ H) : Prop where
  isIsogeny : IsIsogeny f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f.hom.hom.left
  isCentral_kernelι : IsCentral (kernelι f)

namespace IsCentralIsogeny

variable {f : G ⟶ H} (hf : IsCentralIsogeny f)

include hf

theorem isFinite : IsFinite f.hom.hom.left := hf.isIsogeny.1

theorem flat : Flat f.hom.hom.left := hf.isIsogeny.2.1

theorem surjective : Surjective f.hom.hom.left := hf.isIsogeny.2.2

/-- The three scheme-morphism conditions giving an fppf covering map. -/
theorem fppf : Flat f.hom.hom.left ∧ LocallyOfFinitePresentation f.hom.hom.left ∧
    Surjective f.hom.hom.left :=
  ⟨hf.flat, hf.locallyOfFinitePresentation, hf.surjective⟩

/-- The kernel is finite over the base, without a smoothness hypothesis on the kernel. -/
theorem kernel_isFinite : IsFinite (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf.isFinite

/-- The kernel is flat over the base. -/
theorem kernel_flat : Flat (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf.flat

/-- Local finite presentation of the kernel follows from the actual kernel square. -/
theorem kernel_locallyOfFinitePresentation : LocallyOfFinitePresentation (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf.locallyOfFinitePresentation

/-- Every point of the actual kernel lies in the all-test centre. -/
theorem kernel_range_le_center : SubgroupFunctor.range (kernelι f) ≤ center G :=
  (isCentral_iff_range_le_center _).mp hf.isCentral_kernelι

/-- A point killed by the map is central, including after every test-scheme restriction. -/
theorem mem_center_of_comp_eq_one {T : Over S} {x : T ⟶ G.X}
    (hx : x ≫ f.hom.hom = 1) : x ∈ (center G).carrier T :=
  (isCentral_kernelι_iff f).mp hf.isCentral_kernelι T x hx

end IsCentralIsogeny

/-- With local finite presentation available, the definition is the finite-flat-surjective
isogeny convention together with centrality of the full kernel. -/
theorem isCentralIsogeny_iff (f : G ⟶ H) [LocallyOfFinitePresentation f.hom.hom.left] :
    IsCentralIsogeny f ↔ IsIsogeny f ∧ IsCentral (kernelι f) :=
  ⟨fun hf => ⟨hf.isIsogeny, hf.isCentral_kernelι⟩,
    fun hf => ⟨hf.1, inferInstance, hf.2⟩⟩

/-- An isomorphism is a central isogeny. -/
theorem isCentralIsogeny_of_isIso (f : G ⟶ H) [IsIso f] : IsCentralIsogeny f := by
  have : IsIso f.hom.hom := (Grp.forget (Over S)).map_isIso f
  have : IsIso f.hom.hom.left := (Over.forget S).map_isIso f.hom.hom
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, ?_⟩
  apply (isCentral_kernelι_iff f).mpr
  intro T x hx
  have hx1 : x = 1 := by
    apply (cancel_mono f.hom.hom).mp
    rw [hx, MonObj.one_comp]
  rw [hx1]
  exact (center G).carrier T |>.one_mem

/-- The identity is a central isogeny. -/
theorem isCentralIsogeny_id (G : GroupScheme S) : IsCentralIsogeny (𝟙 G) :=
  isCentralIsogeny_of_isIso _

end Langlands.GroupScheme
