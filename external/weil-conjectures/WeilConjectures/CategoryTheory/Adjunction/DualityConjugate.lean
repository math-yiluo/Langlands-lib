/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Equivalence

/-!
# Conjugating an adjunction by dualities

Let `D_X : Cₓᵒᵖ ⥤ Cₓ` and `D_Y : C_Yᵒᵖ ⥤ C_Y` be *dualities*: contravariant functors with
`𝟭 ≅ D ∘ D`. Then `D.rightOp ⊣ D`
(`CategoryTheory.Functor.rightOpAdjunctionOfIsoRightOpComp`). Let `F ⊣ G` with
`F : C_Y ⥤ Cₓ`, and let `S : Cₓ ⥤ C_Y` be a functor with `D_Y ∘ S ≅ G ∘ D_X`. Then every right
adjoint `R` of `S` is isomorphic to `D_X ∘ F ∘ D_Y`
(`CategoryTheory.Adjunction.nonempty_iso_rightOp_comp_op_comp_of_duality`).

For Weil complexes, with `F = f^*`, `G = Rf_*` and `S = Rf_!`, this gives `Rf^! ≅ 𝔻_X f^* 𝔻_Y`
from Verdier biduality and the Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` (blueprint
`theorem-verdier-biduality`).
-/

@[expose] public section

namespace CategoryTheory

open Opposite

variable {C D : Type*} [Category* C] [Category* D]

/-- A duality `D : Cᵒᵖ ⥤ C` with `𝟭 ≅ D.rightOp ⋙ D` is an equivalence `C ≌ Cᵒᵖ`, with
functor `D.rightOp` and inverse `D`. -/
noncomputable def Functor.rightOpEquivalenceOfIsoRightOpComp (Dl : Cᵒᵖ ⥤ C)
    (e : 𝟭 C ≅ Dl.rightOp ⋙ Dl) : C ≌ Cᵒᵖ :=
  Equivalence.mk Dl.rightOp Dl e
    (NatIso.ofComponents (fun A ↦ (e.app A.unop).op) fun {A B} f ↦ by
      apply Quiver.Hom.unop_inj
      simpa using (e.hom.naturality f.unop).symm)

/-- A duality `D : Cᵒᵖ ⥤ C` with `𝟭 ≅ D.rightOp ⋙ D` is self-adjoint on the right:
`D.rightOp ⊣ D`, that is `Hom(B, D A) ≃ Hom(A, D B)`. -/
noncomputable def Functor.rightOpAdjunctionOfIsoRightOpComp (Dl : Cᵒᵖ ⥤ C)
    (e : 𝟭 C ≅ Dl.rightOp ⋙ Dl) : Dl.rightOp ⊣ Dl :=
  (Dl.rightOpEquivalenceOfIsoRightOpComp e).toAdjunction

/-- With `D : Cᵒᵖ ⥤ C` a duality, also `D ⊣ D.rightOp`. -/
noncomputable def Functor.adjunctionRightOpOfIsoRightOpComp (Dl : Cᵒᵖ ⥤ C)
    (e : 𝟭 C ≅ Dl.rightOp ⋙ Dl) : Dl ⊣ Dl.rightOp :=
  (Dl.rightOpEquivalenceOfIsoRightOpComp e).symm.toAdjunction

/-- **Conjugating an adjunction by dualities.** Let `D_X`, `D_Y` be dualities, `F ⊣ G` with
`F : C_Y ⥤ Cₓ`, and `S : Cₓ ⥤ C_Y` with `D_Y ∘ S ≅ G ∘ D_X`. Then a right adjoint `R` of `S` is
isomorphic to `D_X ∘ F ∘ D_Y`:
```
        Sᵒᵖ                          D_Yᵒᵖ        Fᵒᵖ
  Cᵒᵖ ──────▶ Dᵒᵖ                D ──────▶ Dᵒᵖ ──────▶ Cᵒᵖ
   │           │                 │                    │
  D_X    ≅    D_Y       ⟹        R          ≅        D_X
   ▼           ▼                 ▼                    ▼
   C  ───────▶ D                 C ══════════════════ C
         G
```
As the dualities are anti-equivalences, the left square exhibits `S` as the conjugate of `G` by
them, so the conjugate of its left adjoint `F` is a right adjoint of `S`. -/
theorem Adjunction.nonempty_iso_rightOp_comp_op_comp_of_duality
    (DX : Cᵒᵖ ⥤ C) (eX : 𝟭 C ≅ DX.rightOp ⋙ DX) (DY : Dᵒᵖ ⥤ D) (eY : 𝟭 D ≅ DY.rightOp ⋙ DY)
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {S : C ⥤ D} {R : D ⥤ C} (adjS : S ⊣ R)
    (ex : S.op ⋙ DY ≅ DX ⋙ G) :
    Nonempty (R ≅ DY.rightOp ⋙ F.op ⋙ DX) := by
  let adj' : (DX.rightOp ⋙ G.op) ⋙ DY ⊣ DY.rightOp ⋙ F.op ⋙ DX :=
    ((DX.rightOpAdjunctionOfIsoRightOpComp eX).comp adj.op).comp
      (DY.adjunctionRightOpOfIsoRightOpComp eY)
  let i : S ≅ (DX.rightOp ⋙ G.op) ⋙ DY :=
    NatIso.ofComponents
      (fun K ↦ eY.app (S.obj K) ≪≫ (DY.mapIso (ex.app (Opposite.op K)).op).symm)
      fun {K L} f ↦ by
        have h := ex.inv.naturality f.op
        dsimp at h ⊢
        simp only [Iso.op_inv]
        rw [Category.assoc, ← DY.map_comp, ← op_comp]
        simp only [Iso.app_inv]
        rw [h, op_comp, DY.map_comp, ← Category.assoc, ← Category.assoc]
        congr 1
        exact eY.hom.naturality (S.map f)
  exact ⟨adjS.rightAdjointUniq (adj'.ofNatIsoLeft i.symm)⟩

end CategoryTheory
