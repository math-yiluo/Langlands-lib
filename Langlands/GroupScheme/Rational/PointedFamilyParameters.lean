import Langlands.GroupScheme.Rational.PointedCommutatorFamily
import Langlands.GroupScheme.Rational.WoundParameterFamilies
import Langlands.AlgebraicGeometry.PointTopology.AffineDensity

/-! # Separating the initial variable from universal commutator parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.PointedCommutatorFamily

variable {B : Scheme.{u}}

/-- Regroup the universal source into its initial variable and all its
parameters, retaining the terminal parameter factor when the index is zero. -/
def sourceProductIso (G : GroupScheme B) (V : Over B) :
    (n : ℕ) → source G V n ≅ V ⊗ parameters G n
  | 0 => (ρ_ V).symm
  | n + 1 => whiskerRightIso (sourceProductIso G V n) G.X ≪≫
      α_ V (parameters G n) G.X

/-- Under regrouping, the original basepoint section sets only the initial
variable and is the identity on the complete parameter scheme. -/
theorem basepointSection_sourceProductIso (G : GroupScheme B) {V : Over B}
    (v₀ : 𝟙_ (Over B) ⟶ V) (n : ℕ) :
    basepointSection (G := G) v₀ n ≫ (sourceProductIso G V n).hom =
      lift (toUnit (parameters G n) ≫ v₀) (𝟙 (parameters G n)) := by
  induction n with
  | zero =>
    apply hom_ext
    · simp [sourceProductIso, basepointSection, parameters]
    · exact toUnit_unique _ _
  | succ n ih =>
    change (basepointSection v₀ n ⊗ₘ 𝟙 G.X) ≫
      ((sourceProductIso G V n).hom ▷ G.X ≫
        (α_ V (parameters G n) G.X).hom) = _
    rw [← Category.assoc, tensorHom_comp_whiskerRight, ih]
    apply hom_ext
    · simp [Category.assoc]
    · apply hom_ext <;> simp [Category.assoc]

section Field

variable {k : Type u} [Field k]
    {G W : GroupScheme (Spec (CommRingCat.of k))}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

/-- The whole nested-source family is the identity if its whole basepoint
section is the identity and the target is wound. Reducedness and density of
the actual source are retained as hypotheses. -/
theorem family_eq_one_of_basepointSection (hW : HasConstantAffineLineMaps W)
    (n : ℕ) [IsReduced (source G A n).left] [IsSeparated W.X.hom]
    (hD : HasDenseRationalPoints k (source G A n))
    (f : source G A n ⟶ W.X)
    (h₀ : basepointSection (G := G) z n ≫ f = 1) : f = 1 := by
  let e := sourceProductIso G A n
  have : IsIso e.inv.left := by
    change IsIso ((Over.forget _).map e.inv)
    infer_instance
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have : IsReduced (A ⊗ parameters G n).left :=
    isReduced_of_isOpenImmersion e.inv.left
  have hD' : HasDenseRationalPoints k (A ⊗ parameters G n) :=
    hasDenseRationalPoints_of_denseRange e.hom e.hom.left.denseRange hD
  have h₀' : affineLineParameterZeroSection (parameters G n) ≫ e.inv ≫ f = 1 := by
    change lift (toUnit (parameters G n) ≫ z) (𝟙 (parameters G n)) ≫
      (sourceProductIso G A n).inv ≫ f = 1
    rw [← basepointSection_sourceProductIso G z n]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h₀
  have h := hW.family_eq_one_of_zeroSection hD' (e.inv ≫ f) h₀'
  have h' := congrArg (fun t => e.hom ≫ t) h
  simpa only [Iso.hom_inv_id_assoc, MonObj.comp_one] using h'

end Field

end Langlands.GroupScheme.PointedCommutatorFamily
