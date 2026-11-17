import Langlands.GroupScheme.FieldOpenSubgroup
import Langlands.AlgebraicGeometry.DvrSpecialFiberSectionEmbedding
import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # An open canonical affinization over a DVR is an isomorphism -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.DvrOpenAffinization


/-- A point in the image of a base change can be lifted along a morphism
whose corresponding base change is surjective. -/
private theorem exists_preimage_of_baseChange
    {S T : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (b : T ⟶ S)
    (hf : Surjective ((Over.pullback b).map f).left) (y : Y.left)
    (hy : Y.hom y ∈ Set.range b) : ∃ x, f.left x = y := by
  have hyr : y ∈ Set.range (pullback.fst Y.hom b) := by
    rw [Scheme.Pullback.range_fst]
    exact hy
  obtain ⟨z, hz⟩ := hyr
  obtain ⟨w, hw⟩ := hf.surj z
  refine ⟨pullback.fst X.hom b w, ?_⟩
  have hfac : ((Over.pullback b).map f).left ≫ pullback.fst Y.hom b =
      pullback.fst X.hom b ≫ f.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  calc
    _ = pullback.fst Y.hom b (((Over.pullback b).map f).left w) :=
      (congrArg (fun a => a w) hfac).symm
    _ = y := by rw [hw, hz]

private theorem range_fractionMap
    (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Set.range (Spec.algebraMap R K) = {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} := by
  have hpoint : ∀ t, Spec.algebraMap R K t = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
    intro t
    have ht : t = (⟨⊥, inferInstance⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    rw [ht]
    apply PrimeSpectrum.ext
    change RingHom.ker (algebraMap R K) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact hpoint t
  · intro hx
    subst x
    exact ⟨IsLocalRing.closedPoint K, hpoint _⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [IsAffine H.X.left]
    (f : G ⟶ H) [IsOpenImmersion f.hom.hom.left]

/-- The actual special-fibre map of an open group homomorphism which is
bijective on global functions is an isomorphism. -/
def specialFiberIso (hf : Function.Bijective f.hom.hom.left.appTop) :
    ((baseChange (DvrSpecialFiberSectionEmbedding.residueMap R)).obj G).X.left ≅
      ((baseChange (DvrSpecialFiberSectionEmbedding.residueMap R)).obj H).X.left := by
  let b := DvrSpecialFiberSectionEmbedding.residueMap R
  let fs := (baseChange b).map f
  have : IsAffineHom H.X.hom := isAffineHom_of_isAffine _
  have : IsAffine ((baseChange b).obj H).X.left := by
    have : IsAffineHom ((baseChange b).obj H).X.hom :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact isAffine_of_isAffineHom ((baseChange b).obj H).X.hom
  have : CompactSpace ((baseChange b).obj G).X.left := by
    have : QuasiCompact ((baseChange b).obj G).X.hom :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace ((baseChange b).obj G).X.hom
  have : IsOpenImmersion fs.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b f.hom.hom inferInstance
  have hinj : Function.Injective fs.hom.hom.left.appTop :=
    DvrSpecialFiberSectionEmbedding.appTop_injective f.hom.hom hf
  have : IsDominant fs.hom.hom.left := isDominant_of_of_appTop_injective hinj
  have hclosed : IsClosed (Set.range fs.hom.hom.left) :=
    FieldOpenSubgroup.isClosed_range fs.hom.hom
  have hrange : Set.range fs.hom.hom.left = Set.univ := by
    rw [← hclosed.closure_eq]
    exact ((isDominant_iff _).mp inferInstance).closure_range
  have : Surjective fs.hom.hom.left := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso fs.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  exact asIso fs.hom.hom.left

@[simp]
theorem specialFiberIso_hom (hf : Function.Bijective f.hom.hom.left.appTop) :
    (specialFiberIso f hf).hom =
      ((baseChange (DvrSpecialFiberSectionEmbedding.residueMap R)).map f).hom.hom.left := rfl

/-- An open group homomorphism over a DVR, bijective on global functions and
an isomorphism on its actual generic fibre, is an actual scheme isomorphism. -/
def isoOfGeneric (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hf : Function.Bijective f.hom.hom.left.appTop)
    (hgen : IsIso ((baseChange (Spec.algebraMap R K)).map f).hom.hom.left) :
    G.X.left ≅ H.X.left := by
  let := hgen
  have hspec : IsIso
      ((baseChange (DvrSpecialFiberSectionEmbedding.residueMap R)).map f).hom.hom.left := by
    rw [← specialFiberIso_hom f hf]
    infer_instance
  have : IsIso ((Over.pullback (Spec.algebraMap R K)).map f.hom.hom).left := hgen
  have : IsIso ((Over.pullback
      (DvrSpecialFiberSectionEmbedding.residueMap R)).map f.hom.hom).left := hspec
  have : Surjective f.hom.hom.left := by
    constructor
    intro y
    rcases FlatReducedDvrConnectedness.point_eq_generic_or_closed R (H.X.hom y) with hy | hy
    · apply exists_preimage_of_baseChange f.hom.hom (Spec.algebraMap R K) inferInstance y
      rw [range_fractionMap R K]
      exact hy
    · apply exists_preimage_of_baseChange f.hom.hom
        (DvrSpecialFiberSectionEmbedding.residueMap R) inferInstance y
      rw [DvrSpecialFiberSectionEmbedding.range_residueMap]
      exact hy
  have : IsIso f.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  exact asIso f.hom.hom.left

@[simp]
theorem isoOfGeneric_hom (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hf : Function.Bijective f.hom.hom.left.appTop)
    (hgen : IsIso ((baseChange (Spec.algebraMap R K)).map f).hom.hom.left) :
    (isoOfGeneric f K hf hgen).hom = f.hom.hom.left := rfl

end Langlands.GroupScheme.DvrOpenAffinization
