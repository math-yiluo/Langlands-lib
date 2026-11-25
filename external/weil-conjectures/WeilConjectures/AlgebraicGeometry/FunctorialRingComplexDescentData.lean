/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
public import WeilConjectures.CategoryTheory.AugmentedComplexGluing
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexIdealDescent
import WeilConjectures.AlgebraicGeometry.RingedGeneratingListsLocalEquality

/-!
# Strict descent data for sheafified functorial ring complexes

Source: Stacks Project, algebraization.tex, Tag 099E, independence of generating ideals.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The explicit augmented model on a slice with a specified generating list.
Source: Stacks Project, Tag 099E, K_{U,I}.
(auxiliary; not a blueprint node). -/
abbrev ringFamilySliceModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (p : RingedIdealGeneratingIndex O I ι) :=
  ringFamilySheafModel (O.over p.U) K ε m hm p.r
    (fun i ↦ ringedSliceSection O p.U (p.f i))

/-- The sheafified ring-family slice complexes carry strict descent data, including their
augmentations. This assertion involves no Čech complex or derived comparison.
Source: Stacks Project, Tag 099E, second and third paragraphs.
(auxiliary; not a blueprint node).

Proof: for two finite generating ideals on slices, their extensions to a common test object
both generate the same ideal subsheaf. Locally each of the finitely many generators of one
is a linear combination of the other generators. Refine the finitely many covering sieves
in both directions. On the resulting covering the two section ideals are equal; they stay
equal after any further restriction. Consequently the ring-family presheaf complexes and
their augmentations are literally identified on these restricted sites. Sheafification
commutes with slice restriction, so these local identities glue to degreewise linear
isomorphisms of the sheafified complexes. Refining two choices simultaneously shows that
the resulting maps agree, by separatedness. The same argument for three lists proves the
cocycle equation. Naturality, the chain equation and augmentation compatibility hold on
the common refinements as the corresponding equations of the specified ring-family maps;
separatedness proves them globally. All refinements are finite intersections of covering
sieves, so no fibre products, points or global finite generating list are required. -/
theorem exists_ringFamily_descentData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι]
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m) :
    Nonempty (SheafOfModules.AugmentedComplexGlueData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      (fun p : RingedIdealGeneratingIndex O I ι ↦ p.U) (ringedSiteRingComplex O)
      (fun p ↦ (ringFamilySliceModel O K ε m hm I ι p).1)
      (fun p ↦ (ringFamilySliceModel O K ε m hm I ι p).2 ≫
        (ringedRestrictionRingComplexIso O p.U).inv)) := by
  apply exists_ringFamily_idealDescentData O K ε m hm
    (fun p : RingedIdealGeneratingIndex O I ι ↦ p.U)
    (fun p ↦ p.r) (fun p ↦ p.f)
  intro p q W a b
  exact exists_cover_generatingLists_ideal_eq O I ι
    p.U p.r p.f p.generates q.U q.r q.f q.generates W a b

end CategoryTheory
