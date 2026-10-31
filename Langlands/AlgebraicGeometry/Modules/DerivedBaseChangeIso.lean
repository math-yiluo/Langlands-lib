import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange

/-!
# Isomorphism criterion for the derived base change map

The derived base change map `derivedBaseChangeMap` is an isomorphism in the derived category of
`R`-modules if and only if the degreewise base change map `baseChangeMap` is an isomorphism in
every degree `n : ℕ` (`isIso_derivedBaseChangeMap_iff`). In that case `derivedBaseChangeIso` is
the isomorphism whose forward map is `derivedBaseChangeMap`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

set_option backward.isDefEq.respectTransparency false in
/-- The derived base change map is an isomorphism if and only if the degreewise base change map
is an isomorphism in every degree. -/
theorem isIso_derivedBaseChangeMap_iff (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M))) :
    IsIso (derivedBaseChangeMap φ f f' g w M hM) ↔
      ∀ n : ℕ, IsIso (baseChangeMap φ f f' g w M hM
        (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n) := by
  have key : ∀ n : ℕ, IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedBaseChangeMap φ f f' g w M hM)) ↔
      IsIso (baseChangeMap φ f f' g w M hM
        (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n) := by
    intro n
    have h := derivedBaseChangeMap_homology φ f f' g w M hM n
    rw [← isIso_comp_right_iff _
      ((DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ.hom)
          (n : ℤ)).hom.app
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback g).obj M)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback g).obj M)) n).hom), h,
      isIso_comp_left_iff]
  constructor
  · intro hiso n
    exact (key n).1 inferInstance
  · intro hiso
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    by_cases hn : n < 0
    · refine (DerivedPlus.isZero_homology_of_neg (relativeGlobalSections f) M hn).isIso ?_ _
      exact ((ModuleCat.restrictScalars φ.hom).map_isZero
        (DerivedPlus.isZero_homology_of_neg (relativeGlobalSections f')
          ((Scheme.Modules.pullback g).obj M) hn)).of_iso
        ((DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ.hom) n).app _)
    · lift n to ℕ using le_of_not_gt hn
      exact (key n).2 (hiso n)

/-- The derived base change isomorphism, when the degreewise base change map is an isomorphism
in every degree. Its forward map is `derivedBaseChangeMap`. -/
def derivedBaseChangeIso (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (h : ∀ n : ℕ, IsIso (baseChangeMap φ f f' g w M hM
      (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n)) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj M ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback g).obj M)) :=
  have := (isIso_derivedBaseChangeMap_iff φ f f' g w M hM).2 h
  asIso (derivedBaseChangeMap φ f f' g w M hM)

@[simp]
lemma derivedBaseChangeIso_hom (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (h : ∀ n : ℕ, IsIso (baseChangeMap φ f f' g w M hM
      (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n)) :
    (derivedBaseChangeIso φ f f' g w M hM h).hom = derivedBaseChangeMap φ f f' g w M hM :=
  rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
