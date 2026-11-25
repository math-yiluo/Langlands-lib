/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.CategoryTheory.RingedSectionLocalization

/-!
# The augmented extended localization Cech complex

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node).

The alternating complex is constructed as the ordered total tensor product of
`[O → O[1/f_i]]` in degrees zero and one. Tensoring localizations identifies the summand
for a subset with localization at its product. The tensor differential gives the alternating
sign, and the tensor of the projections gives the augmentation. The empty tensor is `O[0]`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open scoped ZeroObject

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- Complexes of module sheaves over the given ring sheaf, with integer degrees.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node). -/
abbrev ringedSiteComplex :=
  CochainComplex (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ

/-- The degree-zero ring complex.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node). -/
abbrev ringedSiteRingComplex : ringedSiteComplex O :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))

/-- Terms of the one-section localization complex.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedLocalizationTwoTermX (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  if n = 0 then SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  else if n = 1 then ringedSectionLocalization O s else 0

/-- The degree-zero term is the ring sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: evaluate the first branch of the definition of the graded terms. -/
theorem ringedLocalizationTwoTermX_zero
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ringedLocalizationTwoTermX O s 0 =
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) := by
  simp [ringedLocalizationTwoTermX]

/-- The degree-one term is the localization sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: zero and one are distinct integers, so the second branch gives the localization. -/
theorem ringedLocalizationTwoTermX_one
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ringedLocalizationTwoTermX O s 1 = ringedSectionLocalization O s := by
  simp [ringedLocalizationTwoTermX]

/-- The differential of the one-section complex is localization in degree zero.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedLocalizationTwoTermD (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    ringedLocalizationTwoTermX O s n ⟶ ringedLocalizationTwoTermX O s (n + 1) :=
  if h : n = 0 then
    eqToHom (congrArg (ringedLocalizationTwoTermX O s) h) ≫
      eqToHom (ringedLocalizationTwoTermX_zero O s) ≫
      ringedSectionLocalizationUnit O s ≫
        eqToHom (ringedLocalizationTwoTermX_one O s).symm ≫
        eqToHom (congrArg (ringedLocalizationTwoTermX O s) (congrArg (· + 1) h).symm)
  else 0

/-- The localization differential squares to zero.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: the only possibly nonzero differential has source degree zero and target degree one;
its two neighbours vanish, so every composite is zero. -/
theorem ringedLocalizationTwoTermD_comp
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    ringedLocalizationTwoTermD O s n ≫ ringedLocalizationTwoTermD O s (n + 1) = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [ringedLocalizationTwoTermD]
  · simp [ringedLocalizationTwoTermD, hn]

/-- The actual two-term localization complex, with no chosen or postponed data.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedLocalizationTwoTerm (s : (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O :=
  CochainComplex.of (ringedLocalizationTwoTermX O s) (ringedLocalizationTwoTermD O s)
    (ringedLocalizationTwoTermD_comp O s)

/-- Components of the projection to the ring complex.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedLocalizationTwoTermAugmentationF
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    (ringedLocalizationTwoTerm O s).X n ⟶ (ringedSiteRingComplex O).X n :=
  if h : n = 0 then
    eqToHom (congrArg (ringedLocalizationTwoTermX O s) h) ≫
      eqToHom (ringedLocalizationTwoTermX_zero O s) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      eqToHom (congrArg (ringedSiteRingComplex O).X h.symm)
  else 0

/-- The projection to `O[0]` is a chain map.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: in degree zero the target differential and the degree-one projection are both zero;
in all other degrees the assertion follows from a zero component or a zero differential. -/
theorem ringedLocalizationTwoTermAugmentationF_comm
    (s : (O.obj ⋙ forget CommRingCat).sections) (n m : ℤ)
    (h : (ComplexShape.up ℤ).Rel n m) :
    ringedLocalizationTwoTermAugmentationF O s n ≫ (ringedSiteRingComplex O).d n m =
      (ringedLocalizationTwoTerm O s).d n m ≫ ringedLocalizationTwoTermAugmentationF O s m := by
  have hm : n + 1 = m := h
  subst m
  rw [show (ringedSiteRingComplex O).d n (n + 1) = 0 from
    HomologicalComplex.single_obj_d _ _ _ _ _, comp_zero]
  by_cases hn : n = 0
  · subst n
    simp [ringedLocalizationTwoTermAugmentationF]
  · change 0 = CochainComplex.of.d _ _ n (n + 1) ≫ _
    rw [CochainComplex.of_d]
    simp [ringedLocalizationTwoTermD, hn]

/-- The augmented one-section localization complex.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedLocalizationTwoTermAugmentation
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ringedLocalizationTwoTerm O s ⟶ ringedSiteRingComplex O where
  f := ringedLocalizationTwoTermAugmentationF O s
  comm' := ringedLocalizationTwoTermAugmentationF_comm O s

/-- The augmented extended alternating localization complex, realized by the ordered tensor
of the one-section complexes. Its degree-q summands are indexed by q-element subsets;
the localization tensor identity makes them `O[1/(∏ f_i)]`. Finite sums are also finite
products. The tensor differential gives the alternating localization maps. The augmentation
is the degree-zero identity under the unit identifications and zero in other degrees.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node). -/
def ringedExtendedCech :
    (r : ℕ) → (Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      Σ K : ringedSiteComplex O, K ⟶ ringedSiteRingComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  fun r ↦ Nat.rec
    (fun _ ↦ ⟨ringedSiteRingComplex O, 𝟙 _⟩)
    (fun _ ih f ↦
      ⟨HomologicalComplex.tensorObj
        (ringedLocalizationTwoTerm O (f 0)) (ih (fun i ↦ f i.succ)).1,
        HomologicalComplex.tensorHom
          (ringedLocalizationTwoTermAugmentation O (f 0)) (ih (fun i ↦ f i.succ)).2 ≫
            (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom⟩) r

end CategoryTheory
