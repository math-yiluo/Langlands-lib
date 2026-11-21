import Langlands.GroupScheme.ClosedRepresentationEvaluation
import Langlands.Global.InfinitePlaceGroupManifold
import Langlands.Global.InfinitePlaceIwasawaBaseChange

/-! # Smoothness into an infinite-place point group through a closed representation

For a closed matrix representation `ρ` of the completion base change `G_v` of an affine group
scheme `G` over a number field, a family of points of `G(F_v)` is smooth for the published atlas
exactly when the matrix entries of its image under `ρ` are smooth.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

omit [IsAffine G.X.left] in
/-- A closed representation reflects coordinate smoothness. -/
theorem coordinateSmooth_of_postcomp (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) {B : Type v} [NormedCommRing B] [NormedAlgebra ℝ B]
    (c : A →+* B) {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {p : M → G.affinePoints A}
    (hp : (GeneralLinear.groupScheme n (CommRingCat.of k)).CoordinateSmooth A c I
      (fun x => p x ≫ ρ.hom.hom)) :
    G.CoordinateSmooth A c I p := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (Grp.toMon (GeneralLinear.groupScheme n (CommRingCat.of k))).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of k)
  intro a
  obtain ⟨a', ha'⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2 a
  have h := hp a'
  simp only [affinePointEvaluation_postcomp] at h
  rw [← ha']
  exact h

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear

variable (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (v : InfinitePlace F) {N : ℕ}

/-- The matrix of a point of `G(F_v)` under a representation of the completion base change. -/
def realizationMatrix (ρ : MatrixRepresentation (completionBaseChange F G v) (Fin N)) :
    InfinitePlaceGroupPoints F G v →* GL (Fin N) v.Completion :=
  (ρ.affineMatrix (CommAlgCat.of v.Completion v.Completion)).comp
    (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G).toMonoidHom

variable {d : ℕ} {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Smoothness into `G(F_v)` is smoothness of the matrix entries of a closed realization. -/
theorem contMDiff_iff_realizationMatrix (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (ρ : MatrixRepresentation (completionBaseChange F G v) (Fin N)) (hρ : IsClosedSubgroup ρ)
    (p : M → InfinitePlaceGroupPoints F G v) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → v.Completion) ∞ p ↔
      ∀ i j, ContMDiff I 𝓘(ℝ, v.Completion) ∞
        (fun x => (realizationMatrix F G v ρ (p x)).val i j) := by
  let := completionRCLike F v
  let := smoothChartedSpace F G v hsmooth
  have hmat : ∀ x, (realizationMatrix F G v ρ (p x)).val =
      (coefficientCoordinates (Fin N) (CommRingCat.of v.Completion) (CommAlgCat.of v.Completion v.Completion) (RingHom.id v.Completion)
        (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G (p x) ≫ ρ.hom.hom)).val := by
    intro x
    rfl
  refine (contMDiff_iff_coordinateSmooth F G v I hsmooth p).trans ?_
  rw [← coordinateSmooth_baseChange_iff F v.Completion v.Completion G (RingHom.id v.Completion) I p]
  constructor
  · intro hp i j
    have h := (coordinateSmooth_iff_contMDiff (Fin N) (CommRingCat.of v.Completion) (CommAlgCat.of v.Completion v.Completion) (RingHom.id v.Completion) I
      (fun x => affinePointsBaseChangeMulEquiv F v.Completion v.Completion G (p x) ≫ ρ.hom.hom)).mp (hp.postcomp ρ.hom.hom)
    simp_rw [hmat]
    have hval := (Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).comp h
    let L : Matrix (Fin N) (Fin N) v.Completion →L[ℝ] v.Completion :=
      { toLinearMap :=
          { toFun := fun m => m i j
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        cont := (continuous_apply j).comp (continuous_apply i) }
    exact L.contDiff.contMDiff.comp hval
  · intro hp
    apply MatrixRepresentation.coordinateSmooth_of_postcomp ρ hρ (CommAlgCat.of v.Completion v.Completion) (RingHom.id v.Completion) I
    apply (coordinateSmooth_iff_contMDiff (Fin N) (CommRingCat.of v.Completion) (CommAlgCat.of v.Completion v.Completion) (RingHom.id v.Completion) I
      (fun x => affinePointsBaseChangeMulEquiv F v.Completion v.Completion G (p x) ≫ ρ.hom.hom)).mpr
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have hpi : ContMDiff I 𝓘(ℝ, Fin N → Fin N → v.Completion) ∞
        (fun x i j => (realizationMatrix F G v ρ (p x)).val i j) :=
      contMDiff_pi_space.mpr fun i => contMDiff_pi_space.mpr fun j => hp i j
    let L : (Fin N → Fin N → v.Completion) →L[ℝ] Matrix (Fin N) (Fin N) v.Completion :=
      { toLinearMap := LinearMap.id
        cont := continuous_id }
    have h := L.contDiff.contMDiff.comp hpi
    convert h using 1
    funext x
    exact (hmat x).symm

end Langlands.Global.InfinitePlaceGroupPoints
