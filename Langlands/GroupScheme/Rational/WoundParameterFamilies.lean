import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.GroupScheme.Rational.AffineLineExtensions

/-! # Parameter families of affine-line maps into a wound target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

private theorem toUnit_base :
    toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
  toUnit_unique _ _

/-- Keep all parameters and set only the affine-line coordinate to zero. -/
def affineLineParameterZeroSection (P : Over (Spec (CommRingCat.of k))) :
    P ⟶ A ⊗ P :=
  lift (toUnit P ≫ z) (𝟙 P)

/-- The affine-line slice at an actual rational parameter. -/
def affineLineParameterSlice {P : Over (Spec (CommRingCat.of k))}
    (p : RationalPoint k P) : A ⟶ A ⊗ P :=
  lift (𝟙 A) (toUnit A ≫ p)

theorem zeroSection_comp_affineLineParameterSlice
    {P : Over (Spec (CommRingCat.of k))} (p : RationalPoint k P) :
    z ≫ affineLineParameterSlice p = p ≫ affineLineParameterZeroSection P := by
  apply hom_ext <;>
    simp [affineLineParameterSlice, affineLineParameterZeroSection,
      comp_lift, ← Category.assoc, comp_toUnit, toUnit_base]

/-- Every rational point of the product lies on its rational-parameter slice. -/
theorem rationalPoint_factor_affineLineParameterSlice
    {P : Over (Spec (CommRingCat.of k))} (x : RationalPoint k (A ⊗ P)) :
    (x ≫ fst A P) ≫ affineLineParameterSlice (x ≫ snd A P) = x := by
  apply hom_ext <;>
    simp [affineLineParameterSlice, comp_lift, ← Category.assoc,
      comp_toUnit, toUnit_base]

namespace HasConstantAffineLineMaps

variable {W : GroupScheme (Spec (CommRingCat.of k))}

/-- On a reduced product with dense rational points, every affine-line
parameter family into a wound separated group is independent of the
affine-line variable, with its entire parameter restriction retained. -/
theorem family_eq_parameter_restriction (hW : HasConstantAffineLineMaps W)
    {P : Over (Spec (CommRingCat.of k))}
    [IsReduced (A ⊗ P).left] [IsSeparated W.X.hom]
    (hD : HasDenseRationalPoints k (A ⊗ P)) (f : A ⊗ P ⟶ W.X) :
    f = snd A P ≫ (affineLineParameterZeroSection P ≫ f) := by
  apply hom_ext_of_denseRationalPoints hD
  intro x
  have hs := hW.eq_to_zeroSection (affineLineParameterSlice (x ≫ snd A P) ≫ f)
  have hx := congrArg (fun t => (x ≫ fst A P) ≫ t) hs
  simpa only [← Category.assoc, rationalPoint_factor_affineLineParameterSlice,
    comp_toUnit, toUnit_base, Category.id_comp,
    zeroSection_comp_affineLineParameterSlice] using hx

/-- If the whole zero section of such a parameter family is the group
identity, then the entire family is the group identity. -/
theorem family_eq_one_of_zeroSection (hW : HasConstantAffineLineMaps W)
    {P : Over (Spec (CommRingCat.of k))}
    [IsReduced (A ⊗ P).left] [IsSeparated W.X.hom]
    (hD : HasDenseRationalPoints k (A ⊗ P)) (f : A ⊗ P ⟶ W.X)
    (h₀ : affineLineParameterZeroSection P ≫ f = 1) : f = 1 := by
  rw [hW.family_eq_parameter_restriction hD f, h₀, MonObj.comp_one]

end HasConstantAffineLineMaps

end Langlands.GroupScheme
