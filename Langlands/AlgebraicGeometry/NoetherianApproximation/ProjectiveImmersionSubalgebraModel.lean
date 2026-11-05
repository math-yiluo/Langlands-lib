import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- An actual model of a specified projective immersion over a finite-type
integer subalgebra of its original field. -/
structure ProjectiveImmersionSubalgebraModelData (F : Type u) [Field F]
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n) where
  coefficients : Subalgebra ℤ F
  finiteGeneration : coefficients.FG
  model : Scheme.{u}
  immersion : model ⟶ ProjectiveSpace coefficients n
  isImmersion : IsImmersion immersion
  locallyOfFinitePresentation : LocallyOfFinitePresentation
    (immersion ≫ projectiveSpaceToSpec coefficients n)
  quasiCompact : QuasiCompact (immersion ≫ projectiveSpaceToSpec coefficients n)
  comparison : X ⟶ model
  cartesian : IsPullback comparison (j ≫ projectiveSpaceToSpec F n)
    (immersion ≫ projectiveSpaceToSpec coefficients n) (Spec.algebraMap coefficients F)
  originalImmersion : comparison ≫ immersion = j ≫ ProjSpace.map coefficients F n

private theorem closure_model (F : Type u) [Field F]
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n)
    [IsImmersion j] [CompactSpace X] :
    ∃ (A : Subalgebra ℤ F), A.FG ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ ProjectiveSpace A n) (g : j.image ⟶ Z),
        IsClosedImmersion i ∧ Flat (i ≫ projectiveSpaceToSpec A n) ∧
        LocallyOfFinitePresentation (i ≫ projectiveSpaceToSpec A n) ∧
        IsPullback g (j.imageι ≫ projectiveSpaceToSpec F n)
          (i ≫ projectiveSpaceToSpec A n) (Spec.algebraMap A F) ∧
        g ≫ i = j.imageι ≫ ProjSpace.map A F n := by
  let : QuasiSeparatedSpace (ProjectiveSpace F n) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceToSpec F n)
  let : QuasiCompact j := inferInstance
  let hclosed : IsClosedImmersion j.imageι := inferInstance
  let : LocallyOfFiniteType (j.imageι ≫ projectiveSpaceToSpec F n) := inferInstance
  have hflat : Flat (j.imageι ≫ projectiveSpaceToSpec F n) := inferInstance
  have hfp : LocallyOfFinitePresentation (j.imageι ≫ projectiveSpaceToSpec F n) :=
    inferInstance
  exact ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
    n j.image j.imageι hclosed hflat hfp

set_option backward.isDefEq.respectTransparency.types false in
open P2MW.S_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.ProjFlatDescent25 in
private theorem model_nonempty (F : Type u) [Field F]
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n)
    [IsImmersion j] [CompactSpace X] :
    Nonempty (ProjectiveImmersionSubalgebraModelData F X n j) := by
  classical
  let : QuasiSeparatedSpace (ProjectiveSpace F n) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceToSpec F n)
  let : QuasiCompact j := inferInstance
  obtain ⟨A, hA, Z, ι, g, hclosed, hflat, hfp, hpb, hg⟩ := closure_model F X n j
  let := hclosed
  let := hflat
  let := hfp
  let f := ι ≫ projectiveSpaceToSpec A n
  let e := hpb.isoPullback
  let i := j.toImage ≫ e.hom
  have : IsOpenImmersion i := inferInstance
  have hW : IsCompact
      (i.opensRange : Set ↥(pullback (C := Scheme) f (Spec.algebraMap A F))) :=
    isCompact_range i.continuous
  obtain ⟨T, hT, -, W, hcompact, hpre⟩ :=
    exists_fg_subalgebra_opens_preimage_eq_of_isCompact f i.opensRange hW ∅
  have : IsScalarTower A T F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨q, hqfst, hqsnd⟩ := exists_transition T f
  have hqpre : q ⁻¹ᵁ W = i.opensRange := hpre q hqfst hqsnd
  have hq : IsPullback q (pullback.snd f (Spec.algebraMap A F))
      (pullback.snd f (Spec.algebraMap A T)) (Spec.algebraMap T F) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f (Spec.algebraMap A T))
      (h₂₂ := Spec.algebraMap A T) (v₁₃ := f) _ hqsnd
      (IsPullback.of_hasPullback f (Spec.algebraMap A T))
    rw [hqfst, specMap_algebraMap_comp]
    exact IsPullback.of_hasPullback f (Spec.algebraMap A F)
  have hrange : Set.range (i ≫ q) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change i x ∈ q ⁻¹ᵁ W
    rw [hqpre]
    exact ⟨x, rfl⟩
  let p := IsOpenImmersion.lift W.ι (i ≫ q) hrange
  have hp : p ≫ W.ι = i ≫ q := IsOpenImmersion.lift_fac _ _ _
  have hopen : IsPullback p i W.ι q := by
    apply IsOpenImmersion.isPullback p i W.ι q hp.symm
    simpa using hqpre
  have hi : i ≫ pullback.snd f (Spec.algebraMap A F) =
      j ≫ projectiveSpaceToSpec F n := by
    dsimp only [i, e, f]
    rw [Category.assoc, hpb.isoPullback_hom_snd,
      ← Category.assoc, Scheme.Hom.toImage_imageι]
  have hX := hopen.paste_vert hq
  rw [hi] at hX
  let aT : ProjectiveSpace T n ⟶ ProjectiveSpace A n := ProjSpace.map A T n
  let tF : ProjectiveSpace F n ⟶ ProjectiveSpace T n := ProjSpace.map T F n
  let aF : ProjectiveSpace F n ⟶ ProjectiveSpace A n := ProjSpace.map A F n
  have hcomp : tF ≫ aT = aF := map_comp_map A T F n
  have hg' : g ≫ ι = j.imageι ≫ aF := hg
  have hproj : IsPullback aT (projectiveSpaceToSpec T n)
      (projectiveSpaceToSpec A n) (Spec.algebraMap A T) :=
    ProjSpace.isPullback_map A T n
  let ιT : pullback f (Spec.algebraMap A T) ⟶ ProjectiveSpace T n :=
    hproj.lift (pullback.fst f (Spec.algebraMap A T) ≫ ι)
    (pullback.snd f (Spec.algebraMap A T)) (by
      exact (Category.assoc _ _ _).trans
        (pullback.condition (f := f) (g := Spec.algebraMap A T)))
  have hιfst : ιT ≫ aT =
      pullback.fst f (Spec.algebraMap A T) ≫ ι := hproj.lift_fst _ _ _
  have hιsnd : ιT ≫ projectiveSpaceToSpec T n =
      pullback.snd f (Spec.algebraMap A T) := hproj.lift_snd _ _ _
  have hιpb : IsPullback (pullback.fst f (Spec.algebraMap A T)) ιT ι
      aT := by
    apply IsPullback.of_bot (v₂₁ := projectiveSpaceToSpec T n)
      (v₂₂ := projectiveSpaceToSpec A n) _ hιfst.symm hproj
    rw [hιsnd]
    exact IsPullback.of_hasPullback f (Spec.algebraMap A T)
  have : IsClosedImmersion ιT :=
    MorphismProperty.of_isPullback hιpb inferInstance
  let m : (W : Scheme) ⟶ ProjectiveSpace T n := W.ι ≫ ιT
  have hm : m ≫ projectiveSpaceToSpec T n =
      W.ι ≫ pullback.snd f (Spec.algebraMap A T) := by
    simp only [m, Category.assoc, hιsnd]
  have : CompactSpace W := isCompact_iff_compactSpace.mp hcompact
  have hloc : LocallyOfFinitePresentation (m ≫ projectiveSpaceToSpec T n) := by
    rw [hm]
    infer_instance
  have hqc : QuasiCompact (m ≫ projectiveSpaceToSpec T n) :=
    quasiCompact_of_compactSpace _
  have himm : IsImmersion m := by dsimp only [m]; infer_instance
  have htF : tF ≫ projectiveSpaceToSpec T n =
      projectiveSpaceToSpec F n ≫ Spec.algebraMap T F :=
    (ProjSpace.isPullback_map T F n).w
  have horiginal : p ≫ m = j ≫ tF := by
    apply hproj.hom_ext
    · calc
        (p ≫ m) ≫ aT = (p ≫ W.ι) ≫ ιT ≫ aT := by
          simp only [m, Category.assoc]
        _ = (i ≫ q) ≫ (pullback.fst f (Spec.algebraMap A T) ≫ ι) := by
          rw [hp, hιfst]
        _ = i ≫ pullback.fst f (Spec.algebraMap A F) ≫ ι := by
          rw [Category.assoc, ← Category.assoc q, hqfst]
        _ = j.toImage ≫ g ≫ ι := by
          dsimp only [i, e, f]
          rw [Category.assoc, ← Category.assoc hpb.isoPullback.hom,
            hpb.isoPullback_hom_fst]
        _ = j ≫ aF := by
          rw [hg', ← Category.assoc, Scheme.Hom.toImage_imageι]
        _ = (j ≫ tF) ≫ aT := by rw [Category.assoc, hcomp]
    · calc
        (p ≫ m) ≫ projectiveSpaceToSpec T n =
            p ≫ W.ι ≫ pullback.snd f (Spec.algebraMap A T) := by
          rw [Category.assoc, hm]
        _ = (j ≫ projectiveSpaceToSpec F n) ≫ Spec.algebraMap T F := hX.w
        _ = (j ≫ tF) ≫ projectiveSpaceToSpec T n := by
          simp only [Category.assoc, htF]
  refine ⟨{
    coefficients := T.restrictScalars ℤ
    finiteGeneration := fg_restrictScalars A T hA hT
    model := W
    immersion := m
    isImmersion := himm
    locallyOfFinitePresentation := hloc
    quasiCompact := hqc
    comparison := p
    cartesian := ?_
    originalImmersion := horiginal }⟩
  change IsPullback p (j ≫ projectiveSpaceToSpec F n)
    (m ≫ projectiveSpaceToSpec T n) (Spec.algebraMap T F)
  rw [hm]
  exact hX

/-- A constructed finite-type coefficient model retaining the original projective
immersion and its original-field Cartesian square. -/
def projectiveImmersionSubalgebraModel (F : Type u) [Field F]
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n)
    [IsImmersion j] [CompactSpace X] :
    ProjectiveImmersionSubalgebraModelData F X n j :=
  Classical.choice (model_nonempty F X n j)

end Langlands.AlgebraicGeometry.NoetherianApproximation
