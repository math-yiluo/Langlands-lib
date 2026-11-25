/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech

/-! # Addition of complete local sections

Source: Stacks Project, Tags 0997 and 0998.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Completeness is closed under addition of local sections.

Proof: Put h=f+g and work on the slice over U. In O[1/h], the images of f and g
generate the unit ideal. The binary localization Cech sequence is short exact:
0 → O[1/h] → O[1/(fh)] ⊕ O[1/(gh)] → O[1/(fgh)] → 0.
Injectivity and middle exactness follow from standard-covering gluing. For
surjectivity, write a fraction with denominator (fg)^n and use a binomial
expansion of (f/h+g/h)^(2*n-1)=1 to express 1 as u*f^n+v*g^n. Sheafification
is exact, so this sectionwise sequence gives the displayed sheaf sequence.
Multiplication closure makes the derived internal Homs from the last three
localizations zero. Apply derived internal Hom into K to its distinguished
triangle; exactness makes the internal Hom from O[1/h] zero too. This argument
also applies when f, g, or h is zero, and imposes no bound on K.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998;
sites-cohomology.tex, Tag 08JB.
(auxiliary; not a blueprint node). -/
theorem ringedSite_completeElement_add
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) (f g : R.obj.obj (op U))
    (hf : IsRingedSiteCompleteElement J R K U f)
    (hg : IsRingedSiteCompleteElement J R K U g) :
    IsRingedSiteCompleteElement J R K U (f + g) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let A := SheafOfModules.{u} (O.over U)
  let : ∀ W : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
    fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (O.over W)))
  let N := ringedSiteDerivedRestriction O U K
  let single := DerivedCategory.singleFunctor A 0
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N
  obtain ⟨shift, htri⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let : H.CommShift ℤ := shift
  have : H.IsTriangulated := htri
  have : H.Additive := inferInstance
  let F := single.op ⋙ H
  have : F.Additive := inferInstance
  let L := fun a ↦ ringedSiteSectionLocalization O U a
  have h₁ : IsZero (F.obj (op (L ((f + g) * f)))) :=
    ringedSite_completeElement_mul J R K U (f + g) f hf
  have h₂ : IsZero (F.obj (op (L ((f + g) * g)))) :=
    ringedSite_completeElement_mul J R K U (f + g) g hg
  have h₃ : IsZero (F.obj (op (L (((f + g) * f) * g)))) := by
    change IsRingedSiteCompleteElement J R K U (((f + g) * f) * g)
    have h := ringedSite_completeElement_mul J R K U g ((f + g) * f)
      (ringedSite_completeElement_mul J R K U (f + g) f hf)
    rwa [show g * ((f + g) * f) = ((f + g) * f) * g from mul_comm _ _] at h
  have hB : IsZero (F.obj (op (L ((f + g) * f) ⊞ L ((f + g) * g)))) := by
    rw [IsZero.iff_id_eq_zero, ← F.map_id]
    have ht : 𝟙 (op (L ((f + g) * f) ⊞ L ((f + g) * g))) =
        (biprod.inl : L ((f + g) * f) ⟶ _).op ≫ biprod.fst.op +
          (biprod.inr : L ((f + g) * g) ⟶ _).op ≫ biprod.snd.op := by
      simpa only [op_add, op_comp, op_id] using
        congrArg Quiver.Hom.op (biprod.total
          (X := L ((f + g) * f)) (Y := L ((f + g) * g))).symm
    rw [ht, F.map_add, F.map_comp, F.map_comp,
      h₁.eq_of_tgt (F.map biprod.inl.op) 0, h₂.eq_of_tgt (F.map biprod.inr.op) 0,
      zero_comp, zero_comp, add_zero]
  obtain ⟨i, p, hp, he⟩ := ringedSite_localization_cech J R U f g
  let T := he.singleTriangle
  let T' := (Pretriangulated.triangleOpEquivalence (DerivedCategory A)).functor.obj (op T)
  have hT := Pretriangulated.op_distinguished T he.singleTriangle_distinguished
  have hHT := H.map_distinguished T' hT
  exact (H.mapTriangle.obj T').isZero₃_of_isZero₁₂ hHT h₃ hB

end CategoryTheory
