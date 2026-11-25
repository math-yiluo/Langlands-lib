/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Filtered-colimit preservation by tensor totalization

The tensor-totalization clause of `lem-pc-module-filtered-colimits-tensor`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "Mod" R => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Tensor totalization with a fixed complex preserves filtered colimits.
Source: Stacks Project, Modules on Sites, Lemma 03EP, together with the direct-sum
construction of total complexes (blueprint: lem-pc-module-filtered-colimits-tensor-preserves).

Proof: Tensoring with a fixed module is a left adjoint by
`lem-pc-sheaf-modules-tensor-closed`, using symmetry for the right tensor factor.
Colimits of complexes are computed degreewise. Thus, for each pair of degrees
(a,b), tensoring the degree-a colimit with P in degree b is canonically the
colimit of the corresponding tensors. In total degree n, take the coproduct
of these identifications over all pairs (a,b) with a+b=n. Interchanging the
filtered colimit and this coproduct gives a colimit cocone in degree n.
The identifications are natural in both degrees and commute with each tensor
differential; hence they commute with the signed sum defining the total
differential. Degreewise colimit cocones therefore assemble to a colimit
cocone of total complexes. It is the image of the original colimit cocone
under the displayed functor, so this proves preservation of the canonical
colimit, rather than just existence of an isomorphism of objects. No
boundedness or flatness is needed, since the totalization uses coproducts. -/
theorem preservesFilteredColimitsTensorTotal
    (C : Type u) [Category.{u} C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (I : Type u) [Category.{u} I] [IsFiltered I] :
    ∀ P : CochainComplex (Mod R) ℤ,
      PreservesColimitsOfShape I
        ((((@curriedTensor (Mod R) _ (monoidalCategory R)).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj P) ⋙
          HomologicalComplex₂.totalFunctor (Mod R) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  classical
  let := monoidalCategory R
  let := symmetricCategory R
  let := (tensorClosed R).2.1.some
  have hright (M : Mod R) : PreservesColimitsOfShape I (tensorRight M) := by
    exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  intro P
  let B := ((curriedTensor (Mod R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj P
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let S := {ij : ℤ × ℤ |
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ij = n}
  let E : CochainComplex (Mod R) ℤ ⥤ (Discrete S ⥤ Mod R) :=
    { obj := fun K => Discrete.functor fun ij => ((B.obj K).X ij.val.1).X ij.val.2
      map := fun f => Discrete.natTrans fun ij => ((B.map f).f ij.as.val.1).f ij.as.val.2
      map_id := fun K => by ext ij; simp
      map_comp := fun f g => by ext ij; simp }
  have : PreservesColimitsOfShape I E := by
    apply preservesColimitsOfShape_of_evaluation E I
    intro ij
    have := hright (P.X ij.as.val.2)
    let e : HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) ij.as.val.1 ⋙
        tensorRight (P.X ij.as.val.2) ≅
          E ⋙ (CategoryTheory.evaluation (Discrete S) (Mod R)).obj ij :=
      NatIso.ofComponents (fun K => Iso.refl _) (by intros; simp; rfl)
    exact preservesColimitsOfShape_of_natIso e
  let e : E ⋙ colim ≅ (B ⋙ HomologicalComplex₂.totalFunctor (Mod R)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
      HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n :=
    NatIso.ofComponents (fun K => Iso.refl _) (by
      intro K L f
      simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply colimit.hom_ext
      intro ij
      rw [colimit.ι_map]
      change ((B.map f).f ij.as.val.1).f ij.as.val.2 ≫ _ = _
      symm
      exact HomologicalComplex₂.ιTotal_map (B.obj K) (B.obj L) (B.map f)
        (ComplexShape.up ℤ) ij.as.val.1 ij.as.val.2 n ij.as.property)
  exact preservesColimitsOfShape_of_natIso e

end SheafOfModules
