import Langlands.AbelianScheme.LieRationalDeterminant
import Langlands.AlgebraicGeometry.LocalSectionTrace

/-! # Section traces of rational actions on actual relative Lie modules -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}} {R : CommRingCat.{u}}
    [Algebra ℚ R] (p : S ⟶ Spec R)
    {O : Type v} [Ring O]

/-- The actual rational Lie action traced in a finite free chart on a smaller open. -/
def lieRationalSectionTrace (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : O) (V : Over U) : Γ(S, V.left) :=
  localSectionTrace e (lieRationalLocalOrderAction p A α U a) V

/-- The constructed trace is the intrinsic trace of the actual rational section action. -/
theorem lieRationalSectionTrace_eq_trace (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : O) (V : Over U) :
    lieRationalSectionTrace p A α e a V =
      LinearMap.trace Γ(S, V.left) Γ(A.Lie, V.left)
        (lieRationalSectionOrderAction p A α V a) :=
  localSectionTrace_eq_trace e _ V

/-- The actual Lie trace is independent of any finite Lie chart. -/
theorem lieRationalSectionTrace_trivialization_independent
    (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ A.Lie.over U)
    (a : O) (V : Over U) :
    lieRationalSectionTrace p A α e a V = lieRationalSectionTrace p A α e' a V :=
  localSectionTrace_trivialization_independent e e' _ V

/-- The trace of the action is an actual additive map into structure-sheaf sections. -/
def lieRationalSectionTraceAddHom (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (V : Over U) : O →+ Γ(S, V.left) :=
  (localSectionTraceAddHom e V).comp (lieRationalLocalOrderAction p A α U).toAddMonoidHom

@[simp]
theorem lieRationalSectionTraceAddHom_apply (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (V : Over U) (a : O) :
    lieRationalSectionTraceAddHom p A α e V a = lieRationalSectionTrace p A α e a V :=
  localSectionTraceAddHom_apply e V _

/-- The unital action has trace equal to the finite chart rank. -/
@[simp]
theorem lieRationalSectionTrace_one (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (V : Over U) :
    lieRationalSectionTrace p A α e 1 V = (Fintype.card I : Γ(S, V.left)) := by
  unfold lieRationalSectionTrace
  rw [map_one, localSectionTrace_one]

/-- Actual rational Lie traces commute with every smaller-open restriction. -/
theorem lieRationalSectionTrace_restrict (A : AbelianScheme S) (α : O →+* End0 A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (a : O) {V W : Over U} (j : V ⟶ W) :
    S.presheaf.map j.left.op (lieRationalSectionTrace p A α e a W) =
      lieRationalSectionTrace p A α e a V :=
  localSectionTrace_restrict e _ j

/-- Equivariant actual rational isomorphisms preserve traces in any finite Lie charts. -/
theorem lieRationalSectionTrace_iso {A B : AbelianScheme S}
    (α : O →+* End0 A) (β : O →+* End0 B)
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B)
    (he : ∀ a, comp0 A A B (α a) e.hom = comp0 A B B e.hom (β a))
    {U : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (eA : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (eB : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : O) (V : Over U) :
    lieRationalSectionTrace p A α eA a V = lieRationalSectionTrace p B β eB a V :=
  localSectionTrace_iso_any_chart eA (lieLocalIso0 p e U) eB _ _
    (lieLocalIso0_intertwines p α β e he U a) V

end Langlands.AbelianScheme
