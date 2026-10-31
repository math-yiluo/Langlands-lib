import Langlands.AbelianScheme.LieRational
import Langlands.AbelianScheme.LieDeterminant
import Langlands.AlgebraicGeometry.LocalSectionIso

/-! # Section determinants of rational actions on actual relative Lie modules -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}} {R : CommRingCat.{u}}
    [Algebra ℚ R] (p : S ⟶ Spec R)
    {O : Type v} [Ring O] {ι : Type w} [Fintype ι]

/-- Restrict the actual rational Lie action to a genuine open. -/
def lieRationalLocalOrderAction (A : AbelianScheme S) (α : O →+* End0 A)
    (U : S.Opens) : O →+* CategoryTheory.End (A.Lie.over U) where
  toFun a := (lieRationalOrderAction p A α a).over U
  map_zero' := by rw [map_zero]; rfl
  map_one' := by rw [map_one]; rfl
  map_add' a b := by rw [map_add]; rfl
  map_mul' a b := by rw [map_mul]; rfl

/-- The constructed rational endomorphism action on actual Lie sections. -/
def lieRationalSectionOrderAction (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} (V : Over U) :
    O →+* Module.End Γ(S, V.left) Γ(A.Lie, V.left) :=
  (localSectionEndomorphism A.Lie V).comp (lieRationalLocalOrderAction p A α U)

@[simp]
theorem lieRationalSectionOrderAction_apply (A : AbelianScheme S)
    (α : O →+* End0 A) {U : S.Opens} (V : Over U) (a : O)
    (x : Γ(A.Lie, V.left)) :
    lieRationalSectionOrderAction p A α V a x = (lieMap0 p (α a)).app V.left x :=
  rfl

/-- The rational action on sections commutes with actual restrictions. -/
theorem lieRationalSectionOrderAction_restrict (A : AbelianScheme S)
    (α : O →+* End0 A) {U : S.Opens} {V W : Over U} (j : V ⟶ W)
    (a : O) (x : Γ(A.Lie, W.left)) :
    lieRationalSectionOrderAction p A α V a (A.Lie.presheaf.map j.left.op x) =
      A.Lie.presheaf.map j.left.op (lieRationalSectionOrderAction p A α W a x) :=
  localSectionEndomorphism_restrict j (lieRationalLocalOrderAction p A α U a) x

/-- The polynomial of a finite family of actual rational endomorphism actions. -/
def lieRationalSectionDeterminant (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) : MvPolynomial ι Γ(S, V.left) :=
  localSectionDeterminant e (fun i => lieRationalLocalOrderAction p A α U (a i)) V

/-- The constructed polynomial is independent of any other finite section basis. -/
theorem lieRationalSectionDeterminant_eq_basis (A : AbelianScheme S)
    (α : O →+* End0 A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) {J : Type u} [Fintype J] [DecidableEq J]
    (b : Module.Basis J Γ(S, V.left) Γ(A.Lie, V.left)) :
    lieRationalSectionDeterminant p A α e a V =
      Langlands.Shimura.HodgeDeterminant.polynomial b
        (fun i => lieRationalSectionOrderAction p A α V (a i)) :=
  localSectionDeterminant_eq_basis e _ V b

/-- The coefficient restriction maps preserve the rational Lie polynomial. -/
theorem lieRationalSectionDeterminant_restrict (A : AbelianScheme S)
    (α : O →+* End0 A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) {V W : Over U} (j : V ⟶ W) :
    MvPolynomial.map (S.presheaf.map j.left.op).hom
        (lieRationalSectionDeterminant p A α e a W) =
      lieRationalSectionDeterminant p A α e a V :=
  localSectionDeterminant_restrict e _ j

/-- Evaluation gives the determinant of each scalar linear combination on sections. -/
theorem eval_lieRationalSectionDeterminant (A : AbelianScheme S)
    (α : O →+* End0 A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) (x : ι → Γ(S, V.left)) :
    eval x (lieRationalSectionDeterminant p A α e a V) =
      LinearMap.det (∑ i, x i • lieRationalSectionOrderAction p A α V (a i)) :=
  eval_localSectionDeterminant e _ V x

/-- Extending an integral action to rational endomorphisms preserves its local action. -/
theorem lieRationalLocalOrderAction_integral (A : AbelianScheme S)
    (α : O →+* End A) (U : S.Opens) :
    lieRationalLocalOrderAction p A ((endToEnd0 A).comp α) U =
      lieLocalOrderAction A α U := by
  ext a
  exact congrArg (fun f : CategoryTheory.End A.Lie => f.over U)
    (RingHom.congr_fun (lieRationalOrderAction_integral p A α) a)

/-- The polynomial for an integral action is the published integral Lie polynomial. -/
theorem lieRationalSectionDeterminant_integral (A : AbelianScheme S)
    (α : O →+* End A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : ι → O) (V : Over U) :
    lieRationalSectionDeterminant p A ((endToEnd0 A).comp α) e a V =
      lieSectionDeterminant A α e a V := by
  unfold lieRationalSectionDeterminant lieSectionDeterminant
  rw [lieRationalLocalOrderAction_integral]

/-- Restriction of the actual Lie isomorphism induced by a rational isomorphism. -/
def lieLocalIso0 {A B : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B)
    (U : S.Opens) : A.Lie.over U ≅ B.Lie.over U :=
  (SheafOfModules.overFunctor S.ringCatSheaf U).mapIso (lieIso0 p e)

/-- Actual rational intertwining restricts to the constructed local Lie isomorphism. -/
theorem lieLocalIso0_intertwines {A B : AbelianScheme S}
    (α : O →+* End0 A) (β : O →+* End0 B)
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B)
    (he : ∀ a, comp0 A A B (α a) e.hom = comp0 A B B e.hom (β a))
    (U : S.Opens) (a : O) :
    lieRationalLocalOrderAction p A α U a ≫ (lieLocalIso0 p e U).hom =
      (lieLocalIso0 p e U).hom ≫ lieRationalLocalOrderAction p B β U a := by
  exact congrArg ((SheafOfModules.overFunctor S.ringCatSheaf U).map)
    (lieMap0_intertwines p α β e.hom he a)

/-- Rational isomorphisms preserving the actual actions preserve every chart polynomial. -/
theorem lieRationalSectionDeterminant_iso {A B : AbelianScheme S}
    (α : O →+* End0 A) (β : O →+* End0 B)
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B)
    (he : ∀ a, comp0 A A B (α a) e.hom = comp0 A B B e.hom (β a))
    {U : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (eA : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (eB : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : ι → O) (V : Over U) :
    lieRationalSectionDeterminant p A α eA a V =
      lieRationalSectionDeterminant p B β eB a V :=
  localSectionDeterminant_iso_any_chart eA (lieLocalIso0 p e U) eB _ _
    (fun i => lieLocalIso0_intertwines p α β e he U (a i)) V

end Langlands.AbelianScheme
