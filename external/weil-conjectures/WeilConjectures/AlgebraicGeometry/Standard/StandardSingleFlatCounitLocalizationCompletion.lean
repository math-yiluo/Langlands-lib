/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitLocalizationHomology

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Completion from the actual localized sheaf presentation data.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-completion).
Proof: unpack hpres into its bounded flat complex K on S, its direct-image
identification e, ordinary-pullback identification t, and counit equation. Take
K's termwise stalk at g(a), regarded as a point of S. Exactness and additivity of
stalks preserve the complex, zero terms and its upper bound. Flat sheaves have
flat stalks. Transport this complex along the open-stalk ring isomorphism
O_S,g(a) = O_B,g(a); this is the required P, not an arbitrary flat complex.
Choose a universal left-derived extension-of-scalars pair for g.stalkMap a.
The ordinary tensor-pullback stalk formula, derived using exact stalk functors,
identifies the stalk of derived pullback with that left-derived scalar extension.
Its counit agrees with the stalk of the sheaf counit: on flat representatives this
is the pure-tensor stalk formula, and localization descends that identity.
Apply these comparisons to e and t and then take degree-n homology. Exact stalks
commute with homology, so the presentation equation gives the required square.
Finally transport from V and S to A and B by their open-stalk ring isomorphisms.
Derived direct image commutes with restriction to full inverse-image opens,
and derived pullback commutes with open restriction; the unit-and-counit mate
identities identify the restricted standard base-change map with the original
one. Thus the resulting eL and eR have exactly the displayed endpoints and
factor the original map. One complex P works in every integer degree. No global
bound on B, flatness of g, or arbitrary witness of unproved existence is used. -/
theorem standardSingleFlatCounit_localization_completion
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hSaff : IsAffine S.toScheme) (hVaff : IsAffine V.toScheme)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (hpres : StandardSingleFlatCounitPresentation (p ∣_ S)
      (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)) :
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
  dsimp
  have hlocal := standardSingleFlatCounit_localization_homology
    h_affine p M hM g a S V hS hV hSaff hVaff hVS hpres
  rcases hlocal with ⟨P, hPident, hPbound, hPflat, LF, ε, hLF, hhom⟩
  exact ⟨P, hPbound, hPflat, LF, ε, hLF, hhom⟩

end AlgebraicGeometry
