import Langlands.GroupScheme.Rational.PointedFamilyParameters
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.SmoothProducts
import Langlands.AlgebraicGeometry.PointTopology.SeparablyClosedDensity

/-! # Smooth universal sources and their scalar extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.PointedCommutatorFamily

variable {B B' : Scheme.{u}}

/-- Every nested source is smooth when its initial source and its group are smooth. -/
theorem source_smooth (G : GroupScheme B) (V : Over B)
    [Smooth G.X.hom] [Smooth V.hom] (n : ℕ) : Smooth (source G V n).hom := by
  induction n with
  | zero => exact inferInstanceAs (Smooth V.hom)
  | succ n ih => exact smooth_tensor _ _ ih inferInstance

/-- Scalar extension commutes with the entire nested universal source. -/
def sourceBaseChangeIso (b : B' ⟶ B) (G : GroupScheme B) (V : Over B) :
    (n : ℕ) → (Over.pullback b).obj (source G V n) ≅
      source ((GroupScheme.baseChange b).obj G) ((Over.pullback b).obj V) n
  | 0 => Iso.refl _
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback b) (source G V n) G.X).symm ≪≫
      (sourceBaseChangeIso b G V n ⊗ᵢ Iso.refl _)

/-- Scalar extension commutes with the full parameter scheme, including its
terminal factor at index zero. -/
def parametersBaseChangeIso (b : B' ⟶ B) (G : GroupScheme B) :
    (n : ℕ) → (Over.pullback b).obj (parameters G n) ≅
      parameters ((GroupScheme.baseChange b).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback b)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback b) (parameters G n) G.X).symm ≪≫
      (parametersBaseChangeIso b G n ⊗ᵢ Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- These comparisons preserve the entire basepoint section, with the
basepoint transported through the terminal comparison. -/
theorem basepointSection_baseChange (b : B' ⟶ B) (G : GroupScheme B)
    {V : Over B} (v₀ : 𝟙_ (Over B) ⟶ V) (n : ℕ) :
    (Over.pullback b).map (basepointSection (G := G) v₀ n) ≫
        (sourceBaseChangeIso b G V n).hom =
      (parametersBaseChangeIso b G n).hom ≫
        basepointSection (G := (GroupScheme.baseChange b).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback b) ≫ (Over.pullback b).map v₀) n := by
  induction n with
  | zero =>
    simp [sourceBaseChangeIso, parametersBaseChangeIso, basepointSection]
  | succ n ih =>
    change ((Over.pullback b).map (basepointSection v₀ n ⊗ₘ 𝟙 G.X) ≫
        Functor.OplaxMonoidal.δ (Over.pullback b) (source G V n) G.X) ≫
          ((sourceBaseChangeIso b G V n).hom ⊗ₘ 𝟙 _) =
      (Functor.OplaxMonoidal.δ (Over.pullback b) (parameters G n) G.X ≫
          ((parametersBaseChangeIso b G n).hom ⊗ₘ 𝟙 _)) ≫
        (basepointSection (G := (GroupScheme.baseChange b).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback b) ≫ (Over.pullback b).map v₀) n ⊗ₘ 𝟙 _)
    rw [← Functor.OplaxMonoidal.δ_natural]
    rw [(Over.pullback b).map_id]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, ih]

section Field

variable {k : Type u} [Field k] [IsSepClosed k]
    {G W : GroupScheme (Spec (CommRingCat.of k))}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

/-- The explicit algebraic rational-point proposition discharges the source
density premise for smooth nested sources over a separably closed field. -/
theorem family_eq_one_of_smooth_of_rationalPointStatement
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    [Smooth G.X.hom] [IsSeparated W.X.hom]
    (hW : HasConstantAffineLineMaps W) (n : ℕ)
    (f : source G A n ⟶ W.X)
    (h₀ : basepointSection (G := G) z n ≫ f = 1) : f = 1 := by
  have : Smooth (A).hom := by dsimp [AffineLine.scheme]; infer_instance
  have : Smooth (source G A n).hom := source_smooth G A n
  have : IsReduced (source G A n).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (source G A n).hom
  exact family_eq_one_of_basepointSection hW n
    (hasDenseRationalPoints_of_smooth_of_rationalPointStatement hP k _) f h₀

end Field

end Langlands.GroupScheme.PointedCommutatorFamily
