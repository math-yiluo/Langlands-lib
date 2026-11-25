/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitLocalizationPresentationData
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitLocalizationCompletion

/-! # From local sheaf presentations to flat stalk coordinates

Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Affine-base presentations give stalk scalar-extension coordinates on arbitrary bases.
Source: Stacks Project, Tag 0DJ9, locality paragraph; Tags 06YB and 0D5S,
exact stalks and pullback-stalk comparison.
(blueprint: lem-pc-standard-single-flat-counit-localization).

Proof: Choose an affine neighbourhood S of g(a) and an affine neighbourhood T
of a inside g inverse-image S. Restrict p to p inverse-image S, M to that source,
and g to T -> S. Relative flatness, quasi-coherence and qcqs survive restriction.
The hypothesis at the top open of this restricted source gives a bounded flat
sheaf complex K on S and the two derived identifications with the counit equation.
The top-open isomorphism removes the redundant restriction of the source.
Apply the exact module-stalk functor at g(a) to K to construct P term by term.
Its upper bound survives since the stalk functor is additive and preserves zero
objects. Flat sheaves have flat stalks, giving termwise flatness of P.
Choose a universal scalar-extension pair for the stalk map O_S,g(a) -> O_T,a;
its existence follows from the base-derived tensor model. Deriving the ordinary
tensor-pullback stalk isomorphism gives the natural isomorphism between the stalk
of Lg* and left-derived scalar extension of the original stalk. On K-flat
representatives the equality of the two counits is the tensor-stalk pure-tensor
formula; localization and the universal property descend it to derived objects.
Combine this isomorphism with the stalk of e to obtain the source identification.
The ordinary pullback stalk formula followed by the stalk of t gives the target
identification. Apply degree-n homology to the stalk of the presentation equation;
exactness of stalks and the counit compatibility give exactly the displayed square.
Finally the open-immersion stalk ring isomorphisms transport P, its flatness, the
universal pair and both identifications to the original stalk rings. Derived
restriction commutes with direct image on inverse-image opens and with derived
pullback; the defining unit-and-counit equations identify the restricted canonical
map with the original map at a. Hence the equation is for the original comparison.
The same K works for every n, including negative n. No point is required when A
is empty. No global bound on B or flatness of g is used, and all choices occur
inside this existential proof. -/
theorem standardSingleFlatCounit_localization
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom := by
  obtain ⟨S, V, hS, hV, hSaff, hVaff, hVS, hpres⟩ :=
    standardSingleFlatCounit_localization_presentation_data h_affine p M hM g a
  exact standardSingleFlatCounit_localization_completion h_affine p M hM g a
    S V hS hV hSaff hVaff hVS hpres

end AlgebraicGeometry
