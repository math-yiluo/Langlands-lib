import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof
import Langlands.GroupScheme.Lie.TorusCentralizerSlice
import Langlands.GroupScheme.Lie.TorusElementCentralizer

/-! # Lie coordinates of the centralizer of a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k] [CharZero k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {d : ℕ} (c : FiniteCoordinates G d)
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- The common kernel of the adjoint differentials of `Lie T`, for a maximal torus
of a connected reductive group in characteristic zero, is the image of `Lie T`. -/
theorem mem_maximalTorusCentralizerCoordinates_iff
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (v : Fin d → k) :
    v ∈ torusCentralizerCoordinates c j ↔
      ∃ Y : lieKernel T.toGrp k,
        c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul (targetMap j k Y)) = v := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom T.toGrp.X.hom := hj.2.1.isAffineHom
  have : Mono j.hom.hom.left := hj.2.1.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  rw [mem_torusCentralizerCoordinates_iff]
  constructor
  · intro hv
    let x := (c.equiv (.of (CommRingCat.of k) k)).symm v
    have hx : c.equiv (.of (CommRingCat.of k) k) x = v := LinearEquiv.apply_symm_apply _ _
    have hcent := charZeroTorusLieCentralizer k G T j hj.1 x.toMul fun y => by
      rw [mem_elementCentralizerLie_iff_adjointDifferential c, ofMul_toMul, hx]
      exact hv y
    have hm := (mem_torusCentralizerLie j x).1
      ((range_le_elementCentralizer_iff_mem_torusCentralizerLie j x.toMul).1 hcent)
    rw [maximalTorusCentralizer k G hG T j hj] at hm
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hm
    have hy₀ : reduction G (y ≫ j.hom.hom) = 1 := hy ▸ x.toMul.property
    refine ⟨⟨y, mem_lieKernel_of_comp j y hy₀⟩, ?_⟩
    have he : targetMap j k (⟨y, mem_lieKernel_of_comp j y hy₀⟩ : lieKernel T.toGrp k) =
        x.toMul := Subtype.ext hy
    rw [he, ofMul_toMul, hx]
  · rintro ⟨y, rfl⟩ y'
    exact adjointDifferentialFamily_targetMap_targetMap c j y y'

/-- A maximal torus's Lie centralizer in finite coordinates, over fields of
characteristic zero. -/
def MaximalTorusLieCentralizerCoordinatesStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (d : ℕ) (c : FiniteCoordinates G d)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsConnectedReductive G → IsMaximalTorus j →
      ∀ v : Fin d → k, v ∈ torusCentralizerCoordinates c j ↔
        ∃ Y : lieKernel T.toGrp k,
          c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul (targetMap j k Y)) = v

theorem maximalTorusLieCentralizerCoordinates :
    MaximalTorusLieCentralizerCoordinatesStatement.{u} := by
  intro k _ _ G _ d c T j hG hj v
  exact mem_maximalTorusCentralizerCoordinates_iff c j hG hj v

end Langlands.GroupScheme.Lie
