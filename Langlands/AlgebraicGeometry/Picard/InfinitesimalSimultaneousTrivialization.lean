import Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Langlands.AlgebraicGeometry.Picard.AffineNilpotentLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Simultaneous affine trivializations in infinitesimal squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace
open Langlands.Scheme.Modules Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalSimultaneousTrivialization

variable {Y Y₀ Y₁ Y₂ : Scheme.{u}}

/-- A surjective closed immersion identifies the underlying topological spaces. -/
def closedImmersionHomeomorph (j : Y₁ ⟶ Y) [IsClosedImmersion j] [Surjective j] :
    Y₁ ≃ₜ Y :=
  IsHomeomorph.homeomorph j
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨j.isClosedEmbedding.isEmbedding, j.surjective⟩)

/-- An affine neighborhood on which both actual inverse-image bundles are trivial. -/
structure SimultaneousAffineNeighborhood (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
    (L₁ : LineBundle Y₁) (L₂ : LineBundle Y₂) (V : Y.Opens) (x : Y) where
  opens : Y.Opens
  affine : IsAffineOpen opens
  mem : x ∈ opens
  le : opens ≤ V
  fstTrivialization : (Scheme.Modules.pullback (j₁ ⁻¹ᵁ opens).ι).obj L₁.obj ≅
    structureModule (j₁ ⁻¹ᵁ opens).toScheme
  sndTrivialization : (Scheme.Modules.pullback (j₂ ⁻¹ᵁ opens).ι).obj L₂.obj ≅
    structureModule (j₂ ⁻¹ᵁ opens).toScheme

set_option backward.isDefEq.respectTransparency false in
/-- Compatible line bundles in an affine square with surjective closed-immersion
first and overlap legs have simultaneous affine trivializing neighborhoods. -/
def simultaneousAffineNeighborhood
    (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂)
    [IsClosedImmersion j₁] [Surjective j₁] [IsAffineHom j₂]
    [IsClosedImmersion i₂] [Surjective i₂]
    (L₁ : LineBundle Y₁) (L₂ : LineBundle Y₂)
    (e : (Scheme.Modules.pullback i₁).obj L₁.obj ≅
      (Scheme.Modules.pullback i₂).obj L₂.obj)
    (V : Y.Opens) (x : Y) (hxV : x ∈ V) :
    SimultaneousAffineNeighborhood j₁ j₂ L₁ L₂ V x := by
  classical
  apply Classical.choice
  let E := closedImmersionHomeomorph j₁
  let W := E.opensCongr (L₁.trivializingOpen (E.symm x))
  have hxW : x ∈ W := L₁.mem_trivializingOpen (E.symm x)
  obtain ⟨U, hU, hxU, hUWV⟩ :=
    (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show x ∈ W ⊓ V from ⟨hxW, hxV⟩)
  have hU₁ : j₁ ⁻¹ᵁ U ≤ L₁.trivializingOpen (E.symm x) := by
    intro y hy
    have hh := (hUWV hy).1
    change E.symm (E y) ∈ L₁.trivializingOpen (E.symm x) at hh
    simpa using hh
  let e₁ := pullbackTrivializationOfLE hU₁ L₁.obj (L₁.localTrivialization (E.symm x))
  let U₁ := j₁ ⁻¹ᵁ U
  let U₂ := j₂ ⁻¹ᵁ U
  let U₀ := i₂ ⁻¹ᵁ U₂
  have hU₀ : U₀ ≤ i₁ ⁻¹ᵁ U₁ := by
    intro z hz
    have hw := congrArg (fun g : Y₀ ⟶ Y ↦ g z) w
    change j₁ (i₁ z) = j₂ (i₂ z) at hw
    change j₁ (i₁ z) ∈ U
    rw [hw]
    exact hz
  let g₁ := i₁.resLE U₁ U₀ hU₀
  let g₂ := i₂ ∣_ U₂
  let : IsAffine U₂.toScheme := hU.preimage j₂
  let : IsClosedImmersion g₂ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_morphismRestrict i₂ U₂).flip inferInstance
  let : Surjective g₂ :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict i₂ U₂).flip inferInstance
  let : IsAffine U₀.toScheme := isAffine_of_isAffineHom g₂
  let e₀ : (Scheme.Modules.pullback g₂).obj
      ((Scheme.Modules.pullback U₂.ι).obj L₂.obj) ≅ structureModule U₀.toScheme :=
    (Scheme.Modules.pullbackComp g₂ U₂.ι).app L₂.obj ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι i₂ U₂)).app L₂.obj ≪≫
      ((Scheme.Modules.pullbackComp U₀.ι i₂).app L₂.obj).symm ≪≫
      (Scheme.Modules.pullback U₀.ι).mapIso e.symm ≪≫
      (Scheme.Modules.pullbackComp U₀.ι i₁).app L₁.obj ≪≫
      (Scheme.Modules.pullbackCongr (i₁.resLE_comp_ι hU₀).symm).app L₁.obj ≪≫
      ((Scheme.Modules.pullbackComp g₁ U₁.ι).app L₁.obj).symm ≪≫
      (Scheme.Modules.pullback g₁).mapIso e₁ ≪≫ pullbackUnitIso g₁
  let e₂ := affinePullbackTrivialization g₂
    (IsClosedImmersion.isAffine_surjective_of_isAffine g₂).2
    ((LineBundle.pullback U₂.ι).obj L₂) e₀
  exact ⟨⟨U, hU, hxU, le_trans hUWV inf_le_right, e₁, e₂⟩⟩

section Relative

variable {k R A B C : Type u}
  [CommRing k] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual relative-space arrow induced by a surjective algebra map is a
closed immersion. -/
lemma relativeMap_isClosedImmersion (p : R →ₐ[k] A) (hp : Function.Surjective p) :
    IsClosedImmersion ((relativeSpace f).map (affineBaseMap p)) :=
  relativeSpace_map_property f @IsClosedImmersion (affineBaseMap p)
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom p.toRingHom) hp)

/-- A nilpotent surjection induces a surjective actual relative-space arrow. -/
lemma relativeMap_surjective (p : R →ₐ[k] A) (hp : Function.Surjective p)
    (hn : IsNilpotent (RingHom.ker p.toRingHom)) :
    Surjective ((relativeSpace f).map (affineBaseMap p)) := by
  let : Surjective (affineBaseMap p).left :=
    InfinitesimalTensorNilpotence.spec_surjective p.toRingHom hp hn
  exact relativeSpace_map_surjective f (affineBaseMap p)

/-- A nilpotent surjection induces a homeomorphism on the actual relative spaces. -/
def relativeMapHomeomorph (p : R →ₐ[k] A) (hp : Function.Surjective p)
    (hn : IsNilpotent (RingHom.ker p.toRingHom)) :
    (relativeSpace f).obj (affineBase k A) ≃ₜ
      (relativeSpace f).obj (affineBase k R) := by
  letI : IsClosedImmersion ((relativeSpace f).map (affineBaseMap p)) :=
    relativeMap_isClosedImmersion f p hp
  letI : Surjective ((relativeSpace f).map (affineBaseMap p)) :=
    relativeMap_surjective f p hp hn
  exact closedImmersionHomeomorph ((relativeSpace f).map (affineBaseMap p))

/-- Actual relative line bundles have simultaneous affine trivializations on
every refinement of a neighborhood in an infinitesimal affine ring square. -/
def affineSquareNeighborhood
    (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
    (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom))
    (L₁ : LineBundle ((relativeSpace f).obj (affineBase k A)))
    (L₂ : LineBundle ((relativeSpace f).obj (affineBase k B)))
    (e : (Scheme.Modules.pullback ((relativeSpace f).map (affineBaseMap a))).obj L₁.obj ≅
      (Scheme.Modules.pullback ((relativeSpace f).map (affineBaseMap b))).obj L₂.obj)
    (V : ((relativeSpace f).obj (affineBase k R)).Opens)
    (x : (relativeSpace f).obj (affineBase k R)) (hxV : x ∈ V) :
    SimultaneousAffineNeighborhood
      ((relativeSpace f).map (affineBaseMap p))
      ((relativeSpace f).map (affineBaseMap q)) L₁ L₂ V x := by
  have hp := InfinitesimalRankOnePatching.fst_surjective
    p.toRingHom q.toRingHom a.toRingHom b.toRingHom h hb
  have hnp := InfinitesimalRingPullback.ker_fst_isNilpotent
    p.toRingHom q.toRingHom a.toRingHom b.toRingHom h hn
  letI : IsClosedImmersion ((relativeSpace f).map (affineBaseMap p)) :=
    relativeMap_isClosedImmersion f p hp
  letI : Surjective ((relativeSpace f).map (affineBaseMap p)) :=
    relativeMap_surjective f p hp hnp
  letI : IsAffineHom (affineBaseMap q).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom q.toRingHom))
    infer_instance
  letI : IsAffineHom ((relativeSpace f).map (affineBaseMap q)) :=
    relativeSpace_map_isAffineHom f (affineBaseMap q)
  letI : IsClosedImmersion ((relativeSpace f).map (affineBaseMap b)) :=
    relativeMap_isClosedImmersion f b hb
  letI : Surjective ((relativeSpace f).map (affineBaseMap b)) :=
    relativeMap_surjective f b hb hn
  exact simultaneousAffineNeighborhood _ _ _ _
    (PicardGroupoid.relativeSquare_comm f _ _ _ _
      (PicardGroupoid.affineSquare_comm p q a b h)) L₁ L₂ e V x hxV

end Relative

end Langlands.AlgebraicGeometry.Picard.InfinitesimalSimultaneousTrivialization
