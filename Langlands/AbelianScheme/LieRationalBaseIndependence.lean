import Langlands.AbelianScheme.LieRationalTrace
import Mathlib.Algebra.Algebra.Rat

/-! # Independence of rational Lie maps from the chosen rational base -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}}
    {R R' : CommRingCat.{u}} [Algebra ℚ R] [Algebra ℚ R']
    (p : S ⟶ Spec R) (q : S ⟶ Spec R')

/-- Two actual rational bases give the identical rational-linear structure on sheaves. -/
theorem rationalLinearOverBase_eq : rationalLinearOverBase p = rationalLinearOverBase q := by
  unfold rationalLinearOverBase
  congr 1
  exact Subsingleton.elim _ _

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}
    {R R' : CommRingCat.{u}} [Algebra ℚ R] [Algebra ℚ R']
    (p : S ⟶ Spec R) (q : S ⟶ Spec R')

/-- The rational differential is independent of the actual map supplying rational scalars. -/
theorem lieMap0_base_independent {B B' : AbelianScheme S} (f : Hom0 B B') :
    lieMap0 p f = lieMap0 q f := by
  unfold lieMap0 rationalLieFunctor
  rw [Langlands.Scheme.Modules.rationalLinearOverBase_eq p q]

/-- The two rational Lie functors are compared by the identity on every actual Lie sheaf. -/
def rationalLieBaseIso : rationalLieFunctor p ≅ rationalLieFunctor q :=
  NatIso.ofComponents (fun B => Iso.refl B.obj.Lie) (by
    intro B B' f
    change lieMap0 p f ≫ 𝟙 _ = 𝟙 _ ≫ lieMap0 q f
    rw [Category.comp_id, Category.id_comp]
    exact lieMap0_base_independent p q f)

@[simp] theorem rationalLieBaseIso_hom_app (B : RationalCategory S) :
    (rationalLieBaseIso p q).hom.app B = 𝟙 B.obj.Lie := rfl

@[simp] theorem rationalLieBaseIso_inv_app (B : RationalCategory S) :
    (rationalLieBaseIso p q).inv.app B = 𝟙 B.obj.Lie := rfl

variable (B : AbelianScheme S) {O : Type v} [Ring O] (α : O →+* End0 B)

/-- The rational action on the fixed relative Lie sheaf is independent of the rational base. -/
theorem lieRationalOrderAction_base_independent :
    lieRationalOrderAction p B α = lieRationalOrderAction q B α := by
  ext a
  exact lieMap0_base_independent p q (α a)

/-- The restricted rational action on a fixed open is independent of the rational base. -/
theorem lieRationalLocalOrderAction_base_independent (U : S.Opens) :
    lieRationalLocalOrderAction p B α U = lieRationalLocalOrderAction q B α U := by
  unfold lieRationalLocalOrderAction
  simp only [lieRationalOrderAction_base_independent p q B α]

/-- The actual action on sections is independent of the map supplying rational scalars. -/
theorem lieRationalSectionOrderAction_base_independent {U : S.Opens} (V : Over U) :
    lieRationalSectionOrderAction p B α V = lieRationalSectionOrderAction q B α V := by
  unfold lieRationalSectionOrderAction
  rw [lieRationalLocalOrderAction_base_independent p q B α]

variable {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)

/-- The fixed-chart polynomial uses the same rational differential for either base. -/
theorem lieRationalSectionDeterminant_base_independent
    {ι : Type w} [Fintype ι] (a : ι → O) (V : Over U) :
    lieRationalSectionDeterminant p B α e a V =
      lieRationalSectionDeterminant q B α e a V := by
  unfold lieRationalSectionDeterminant
  rw [lieRationalLocalOrderAction_base_independent p q B α]

/-- The fixed-chart trace likewise uses the same rational differential for either base. -/
theorem lieRationalSectionTrace_base_independent (a : O) (V : Over U) :
    lieRationalSectionTrace p B α e a V = lieRationalSectionTrace q B α e a V := by
  unfold lieRationalSectionTrace
  rw [lieRationalLocalOrderAction_base_independent p q B α]

end Langlands.AbelianScheme
