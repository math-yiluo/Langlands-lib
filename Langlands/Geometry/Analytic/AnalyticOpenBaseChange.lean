import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof
import Mathlib.Topology.Sets.Opens

/-! # Change of base along an analytic open domain -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation.AnalyticOpenBaseChange

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X A B P : LocalizedCategory.{u, v, v} (K := K)} (U : Opens (localizedSpaceFunctor.obj X))

abbrev base := domainObj X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)

abbrev domain (f : A ⟶ X) := preimageOpenDomain f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

abbrev obj (f : A ⟶ X) := domainObj A (domain U f)

abbrev inclusion (f : A ⟶ X) := domainι A (domain U f)

abbrev projection (f : A ⟶ X) : obj U f ⟶ base U :=
  preimageOpenDomainMap f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

abbrev baseInclusion : base U ⟶ X :=
  domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)

theorem projection_comp (f : A ⟶ X) : projection U f ≫ baseInclusion U = inclusion U f ≫ f :=
  preimageOpenDomainMap_comp f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

theorem isPullback_projection (f : A ⟶ X) :
    IsPullback (projection U f) (inclusion U f) (baseInclusion U) f :=
  isPullback_preimageOpenDomain f (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

variable {f : A ⟶ X} {g : B ⟶ X} {k : P ⟶ X}

/-- Restrict an analytic arrow over `X` to the inverse images of `U`. -/
def map (m : A ⟶ B) (hm : m ≫ g = f) : obj U f ⟶ obj U g :=
  (isPullback_projection U g).lift (projection U f) (inclusion U f ≫ m) (by
    rw [projection_comp, Category.assoc, hm])

@[reassoc (attr := simp)]
theorem map_projection (m : A ⟶ B) (hm : m ≫ g = f) :
    map U m hm ≫ projection U g = projection U f :=
  (isPullback_projection U g).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_inclusion (m : A ⟶ B) (hm : m ≫ g = f) :
    map U m hm ≫ inclusion U g = inclusion U f ≫ m :=
  (isPullback_projection U g).lift_snd _ _ _

/-- Open restriction commutes with every existing pullback over the base. -/
theorem isPullback_map {a : P ⟶ A} {b : P ⟶ B}
    (h : IsPullback a b f g) (ha : a ≫ f = k) (hb : b ≫ g = k) :
    IsPullback (map U a ha) (map U b hb) (projection U f) (projection U g) := by
  apply IsPullback.mk' ((map_projection U a ha).trans (map_projection U b hb).symm)
  · intro T u v hua hub
    apply (cancel_mono (inclusion U k)).mp
    apply h.hom_ext
    · simpa only [Category.assoc, map_inclusion] using congrArg (· ≫ inclusion U f) hua
    · simpa only [Category.assoc, map_inclusion] using congrArg (· ≫ inclusion U g) hub
  · intro T u v huv
    have h' : (u ≫ inclusion U f) ≫ f = (v ≫ inclusion U g) ≫ g := by
      simpa only [Category.assoc, projection_comp] using congrArg (· ≫ baseInclusion U) huv
    obtain ⟨r, hra, hrb⟩ := h.exists_lift _ _ h'
    have hrk : r ≫ k = (u ≫ projection U f) ≫ baseInclusion U := by
      rw [← ha, ← Category.assoc, hra, Category.assoc, Category.assoc, projection_comp]
    let l := (isPullback_projection U k).lift (u ≫ projection U f) r hrk.symm
    have hl : l ≫ inclusion U k = r := (isPullback_projection U k).lift_snd _ _ _
    refine ⟨l, ?_, ?_⟩
    · apply (cancel_mono (inclusion U f)).mp
      rw [Category.assoc, map_inclusion, ← Category.assoc, hl, hra]
    · apply (cancel_mono (inclusion U g)).mp
      rw [Category.assoc, map_inclusion, ← Category.assoc, hl, hrb]

/-- A point of the restricted target is in the image of the restricted map
exactly when its underlying point was in the original image. -/
theorem mem_range_map_iff (m : A ⟶ B) (hm : m ≫ g = f) (z : localizedSpaceFunctor.obj (obj U g)) :
    z ∈ range (localizedSpaceFunctor.map (map U m hm)) ↔
      z.val ∈ range (localizedSpaceFunctor.map m) := by
  have hpoint (y : localizedSpaceFunctor.obj (obj U f)) :
      (localizedSpaceFunctor.map (map U m hm) y).val = localizedSpaceFunctor.map m y.val := by
    change @Eq (localizedSpaceFunctor.obj B) _ _
    simpa only [Functor.map_comp, TopCat.comp_app, domainι_apply] using
      congrArg (fun q => localizedSpaceFunctor.map q y) (map_inclusion U m hm)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, (hpoint y).symm.trans (congrArg Subtype.val hy)⟩
  · rintro ⟨y, hy⟩
    have hym : localizedSpaceFunctor.map f y = localizedSpaceFunctor.map g z.val := by
      have h := congrArg (fun q : A ⟶ X => localizedSpaceFunctor.map q y) hm
      simpa only [Functor.map_comp, TopCat.comp_app, hy] using h.symm
    have hyU : localizedSpaceFunctor.map f y ∈ U := by rw [hym]; exact z.property
    let y' : localizedSpaceFunctor.obj (obj U f) := ⟨y, hyU⟩
    exact ⟨y', Subtype.ext ((hpoint y').trans hy)⟩

/-- The composite to the restricted base of a pullback of two étale arrows is étale. -/
theorem etale_projection_of_isPullback {a : P ⟶ A} {b : P ⟶ B}
    (h : IsPullback a b f g) (ha : a ≫ f = k) (hb : b ≫ g = k)
    (hf : etale (projection U f)) (hg : etale (projection U g)) : etale (projection U k) := by
  have hpullback : LocalizedEtalePullbackStatement.{u, v} K :=
    localizedEtalePullback_of_targetLocality_and_finitePieces
      (AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent
        PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent)
      AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces
  obtain ⟨_, _, _, hP, hq⟩ := hpullback (projection U f) (projection U g) hf
  have hb' := etale_snd_of_isPullback hP (isPullback_map U h ha hb) hq
  rw [← map_projection U b hb]
  exact etale_comp hb' hg

end Langlands.Analytic.SaturatedAtlasPresentation.AnalyticOpenBaseChange
