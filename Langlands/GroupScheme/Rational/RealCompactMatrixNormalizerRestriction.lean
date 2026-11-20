import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.RealCompactMatrixPoints

/-! # Restricting a normalizing matrix to a closed group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RealCompactForm

open GaloisPointComparison
variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

local notation "GLScheme" => Langlands.GroupScheme.GeneralLinear.groupScheme n (CommRingCat.of k)

private def glRationalPointEquiv : rationalPoints GLScheme ≃* GL n k :=
  (rationalCoeffEquiv k GLScheme).trans
    (Langlands.GroupScheme.GeneralLinear.affinePointsEquiv n (CommRingCat.of k) (CommAlgCat.of k k))

private theorem rationalMatrix_eq_glRationalPoint (ρ : MatrixRepresentation G n)
    (x : rationalPoints G) :
    ρ.rationalMatrix x = glRationalPointEquiv (x ≫ ρ.hom.hom) := by
  let std := MatrixRepresentation.standard n (CommRingCat.of k)
  have h : std.restrict ρ = ρ := Category.comp_id ρ
  calc
    ρ.rationalMatrix x = (std.restrict ρ).rationalMatrix x := by rw [h]
    _ = std.rationalMatrix (x ≫ ρ.hom.hom) := std.rationalMatrix_restrict ρ x
    _ = _ := by
      rw [rationalMatrix_eq_coeffMatrix]
      exact MatrixRepresentation.standard_affineMatrix _ _

private def matrixPoint (c : GL n k) : rationalPoints GLScheme :=
  glRationalPointEquiv.symm c

private theorem rationalMatrix_conjugate (ρ : MatrixRepresentation G n)
    (c : GL n k) (x : rationalPoints G) :
    (ρ.conjugate (matrixPoint c)).rationalMatrix x =
      c * ρ.rationalMatrix x * c⁻¹ := by
  rw [rationalMatrix_eq_glRationalPoint (ρ.conjugate (matrixPoint c)) x,
    ρ.comp_conjugate (matrixPoint c) _ x, constantPoint_self,
    map_mul, map_mul, map_inv, matrixPoint, MulEquiv.apply_symm_apply,
    ← rationalMatrix_eq_glRationalPoint ρ x]

private theorem exists_normalizer_hom [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom] (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    {c : GL n k} (hc : c ∈ Subgroup.normalizer (ρ.rationalMatrix.range : Set (GL n k))) :
    ∃ f : G ⟶ G, f ≫ ρ = ρ.conjugate (matrixPoint c) := by
  refine SubgroupFunctor.exists_factor_of_algClosed_points
    (i := ρ.conjugate (matrixPoint c)) (j := ρ) hρ ?_
  intro z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  have hx : c * ρ.rationalMatrix x * c⁻¹ ∈ ρ.rationalMatrix.range :=
    (Subgroup.mem_normalizer_iff.mp hc (ρ.rationalMatrix x)).mp ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
  apply glRationalPointEquiv.injective
  rw [← rationalMatrix_eq_glRationalPoint, ← rationalMatrix_eq_glRationalPoint,
    rationalMatrix_conjugate]
  exact hy

/-- A normalizing matrix acts by a group-scheme automorphism of the represented group. -/
theorem exists_normalizer_iso [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom] (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    {c : GL n k} (hc : c ∈ Subgroup.normalizer (ρ.rationalMatrix.range : Set (GL n k))) :
    ∃ e : G ≅ G, ∀ x : rationalPoints G,
      ρ.rationalMatrix (rationalPoints.map e.hom x) = c * ρ.rationalMatrix x * c⁻¹ := by
  obtain ⟨f, hf⟩ := exists_normalizer_hom ρ hρ hc
  obtain ⟨g, hg⟩ := exists_normalizer_hom ρ hρ (Subgroup.inv_mem _ hc)
  let : Mono ρ := (Grp.forget _).mono_of_mono_map (f := ρ) hρ.mono_overHom
  let a := (GLScheme).innerIso (matrixPoint c)
  have hpoint : matrixPoint c⁻¹ = (matrixPoint c)⁻¹ := map_inv glRationalPointEquiv.symm c
  have hf' : f ≫ ρ = ρ ≫ a.hom := hf
  have hg' : g ≫ ρ = ρ ≫ a.inv := by
    rw [hg, MatrixRepresentation.conjugate]
    rw [hpoint, innerIso_inv_hom]
  refine ⟨⟨f, g, ?_, ?_⟩, fun x => ?_⟩
  · apply (cancel_mono ρ).mp
    rw [Category.assoc, hg', ← Category.assoc, hf', Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono ρ).mp
    rw [Category.assoc, hf', ← Category.assoc, hg', Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · change ρ.rationalMatrix (rationalPoints.map f x) = _
    rw [rationalPoints.map_apply, ← ρ.rationalMatrix_restrict]
    change MatrixRepresentation.rationalMatrix (f ≫ ρ) x = _
    rw [hf, rationalMatrix_conjugate]

end Langlands.GroupScheme.RealCompactForm
