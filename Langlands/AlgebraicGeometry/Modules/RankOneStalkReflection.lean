import Langlands.AlgebraicGeometry.Modules.RankOneStalkSpreading
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Langlands.AlgebraicGeometry.StalkEssFinitePresentation
import Langlands.AlgebraicGeometry.FiberStalkFlatness
import Langlands.Algebra.LocalFiberRankOneReflection
import Langlands.AlgebraicGeometry.Modules.StalkTrivialization

/-! # Rank-one reflection for actual module stalks -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- Every actual stalk of a locally finitely presented module sheaf is a
finitely presented module over its actual local ring. -/
lemma finitePresentation_stalk (M : X.Modules) [M.IsFinitePresentation] (x : X) :
    Module.FinitePresentation (X.presheaf.stalk x) (stalk M x) := by
  obtain ⟨R, f, hf, y, hy, hM⟩ := exists_Spec_finitePresentation_sections M x
  let := hf
  let := hM
  subst x
  let := (f.stalkMap y).hom.toAlgebra
  let := relativeStalkModule f (M.restrict f) y
  have : IsScalarTower (X.presheaf.stalk (f y)) ((Spec R).presheaf.stalk y)
      (stalk (M.restrict f) y) := .of_algebraMap_smul (fun _ _ => rfl)
  let eR := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  let e : ((Spec R).presheaf.stalk y) ≃ₗ[X.presheaf.stalk (f y)]
      X.presheaf.stalk (f y) :=
    { __ := eR.symm.toAddEquiv
      map_smul' := by
        intro r s
        change eR.symm (eR r * s) = r * eR.symm s
        rw [map_mul, eR.symm_apply_apply] }
  have : Module.FinitePresentation (X.presheaf.stalk (f y))
      ((Spec R).presheaf.stalk y) := Module.FinitePresentation.of_equiv e.symm
  have : Module.FinitePresentation ((Spec R).presheaf.stalk y)
      (stalk (M.restrict f) y) := finitePresentation_spec_stalk (M.restrict f) y
  have : Module.FinitePresentation (X.presheaf.stalk (f y))
      (stalk (M.restrict f) y) :=
    Module.FinitePresentation.trans (X.presheaf.stalk (f y))
      (stalk (M.restrict f) y) ((Spec R).presheaf.stalk y)
  exact Module.FinitePresentation.of_equiv (restrictStalkLinearEquiv f M y)

/-- A trivialization on a neighbourhood gives a rank-one basis of the actual
stalk, over the actual local ring. -/
def stalkRankOneEquivOfMem (M : X.Modules) (x : X)
    (hx : x ∈ Picard.rankOneLocus M) :
    stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let h := (Picard.mem_rankOneLocus M x).mp hx
  let U := h.choose
  let hxU := h.choose_spec.1
  let e := h.choose_spec.2.some
  exact ofRestrictStalkRankOneEquiv U.ι M ⟨x, hxU⟩
    ((stalkIso e ⟨x, hxU⟩).trans (unitStalkLinearEquiv U.toScheme ⟨x, hxU⟩))

/-- Reflection of an actual rank-one stalk under an ordinary pullback whose
induced map on the original residue fibre is flat. -/
def stalkRankOneEquivOfFiberwiseFlatPullback
    {S Y Xs Ys : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ S)
    [LocallyOfFinitePresentation q] (M : Y.Modules) [M.IsFinitePresentation]
    (hM : IsFlatOver q M) (x : X)
    {aX : Xs ⟶ X} {bX : Xs ⟶ Spec (S.residueField (q (p x)))}
    {aY : Ys ⟶ Y} {bY : Ys ⟶ Spec (S.residueField (q (p x)))}
    (HX : IsPullback aX bX (p ≫ q) (S.fromSpecResidueField (q (p x))))
    (HY : IsPullback aY bY q (S.fromSpecResidueField (q (p x))))
    (fs : Xs ⟶ Ys) (h₁ : fs ≫ aY = aX ≫ p) (h₂ : fs ≫ bY = bX) [Flat fs]
    (e : stalk ((Scheme.Modules.pullback p).obj M) x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) :
    stalk M (p x) ≃ₗ[Y.presheaf.stalk (p x)] Y.presheaf.stalk (p x) := by
  let := (q.stalkMap (p x)).hom.toAlgebra
  let := (p.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (S.presheaf.stalk (q (p x)))
      (Y.presheaf.stalk (p x))) :=
    inferInstanceAs (IsLocalHom (q.stalkMap (p x)).hom)
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (p x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap x).hom)
  let := relativeStalkModule q M (p x)
  have : IsScalarTower (S.presheaf.stalk (q (p x))) (Y.presheaf.stalk (p x))
      (stalk M (p x)) := .of_algebraMap_smul (fun _ _ => rfl)
  have : Module.FinitePresentation (Y.presheaf.stalk (p x)) (stalk M (p x)) :=
    finitePresentation_stalk M (p x)
  have : Module.Flat (S.presheaf.stalk (q (p x))) (stalk M (p x)) := hM (p x)
  have := FiberStalkFlatness.flat_fiber_stalk p q (p ≫ q) rfl x HX HY fs h₁ h₂
  exact Langlands.Algebra.LocalFiberRankOne.linearEquivOfFiberwiseFlatBaseChange
    (S.presheaf.stalk (q (p x))) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x)
    (stalk M (p x)) (stalkEssFinitePresentation Y S q (p x) inferInstance)
    ((StalkPullback.pullbackStalkTensorEquiv p x M).symm.trans e)

end Langlands.AlgebraicGeometry.Modules
