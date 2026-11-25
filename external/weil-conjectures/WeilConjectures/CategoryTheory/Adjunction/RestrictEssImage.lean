/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Left adjoints restricted along fully faithful functors

Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be fully faithful, let `L' ⊣ R'` be an adjunction
`C' ⇄ D'`, and let `L : C ⥤ D` be a functor with `iC ⋙ L' ≅ L ⋙ iD`:
```
       L
   C ────→ D
   │       │
 iC│       │iD
   ↓       ↓
   C' ───→ D'
       L'
```
If `R'` maps the image of `iD` into the essential image of `iC`, then `L` is a left adjoint: its
right adjoint is the lift of `iD ⋙ R'` along `iC`
(`CategoryTheory.Adjunction.isLeftAdjoint_of_essImage`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'} {L : C ⥤ D}

/-- Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be fully faithful and `L' ⊣ R'`. If `L : C ⥤ D`
satisfies `iC ⋙ L' ≅ L ⋙ iD` and `R'` maps the image of `iD` into the essential image of `iC`,
then the lift of `iD ⋙ R'` along `iC` is right adjoint to `L`. -/
noncomputable def ofEssImage (adj : L' ⊣ R') (hC : iC.FullyFaithful) (hD : iD.FullyFaithful)
    (e : iC ⋙ L' ≅ L ⋙ iD) (h : ∀ Y, iC.essImage (R'.obj (iD.obj Y))) :
    have := hC.full
    have := hC.faithful
    L ⊣ Functor.essImage.liftFunctor (iD ⋙ R') iC h :=
  have := hC.full
  have := hC.faithful
  adj.restrictFullyFaithful hC hD e (Functor.essImage.liftFunctorCompIso _ _ _).symm

/-- Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be fully faithful and `L' ⊣ R'`. If `L : C ⥤ D`
satisfies `iC ⋙ L' ≅ L ⋙ iD` and `R'` maps the image of `iD` into the essential image of `iC`,
then `L` is a left adjoint. -/
lemma isLeftAdjoint_of_essImage (adj : L' ⊣ R') (hC : iC.FullyFaithful) (hD : iD.FullyFaithful)
    (e : iC ⋙ L' ≅ L ⋙ iD) (h : ∀ Y, iC.essImage (R'.obj (iD.obj Y))) : L.IsLeftAdjoint :=
  (ofEssImage adj hC hD e h).isLeftAdjoint

end CategoryTheory.Adjunction
