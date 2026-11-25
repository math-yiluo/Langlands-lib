/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage

/-!
# Finite module dévissage for direct images

Source: Stacks Project, `more-etale.tex`, Tag 0GKW, proof of
`lemma-proper-smooth-family-curves-modules`, lines 4379--4395
(blueprint: lem-fd-finite-module-direct-image-devissage).

The theorem states that constructibility of all cohomology sheaves of the derived
étale direct image for the successive quotients of a finite module filtration
implies constructibility for the whole module.  The proof uses the exact constant
sheaf sequence, the long exact sequence of derived direct images, and closure of
constructible sheaves under kernels, cokernels, and extensions, with the
zero-filtration and negative-degree cases included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Constructibility is preserved by finite coefficient-module dévissage.

Source: Stacks Project, `more-etale.tex`, Tag 0GKW, proof of
`lemma-proper-smooth-family-curves-modules`, lines 4379--4395
(blueprint: lem-fd-finite-module-direct-image-devissage).

Proof: first compare the displayed bounded-below formulation with the unbounded one:
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`
(`lem-weil-pbc-constructible-etale-module-sheaf-comparison`) and `H^q` of
`rightDerivedFunctorPlusCompatibility` (`src-right-derived-functor-plus-compatibility`)
identify both sides, in every integer degree.  Then induct over `Fin (r + 1)` on the
property `constructibleHomology` of `Rf_*(underline(F i))`.  At `i = 0` the module `F 0 = ⊥`
is zero, so its derived direct image is zero.  For the step, the inclusion
`F i.castSucc → F i.succ` and the quotient map onto `F i.succ ⧸ (F i.castSucc).comap _` form a
short exact sequence of finite modules, and
`Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact`
(`lem-fd-constant-module-direct-image-extension`) gives the middle term from the induction
hypothesis and `hgraded i`.  At `Fin.last r`, `hwhole` identifies `F (Fin.last r)` with `M`.
-/
theorem finiteModule_directImage_devissage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (r : ℕ) (F : Fin (r + 1) → Submodule Λ (M : Type (u + 1)))
    (hzero : F 0 = ⊥)
    (hwhole : F (Fin.last r) = ⊤)
    (hincreasing : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hgraded : ∀ (i : Fin r) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          ((Etale.rightDerivedLowerStarPlus
              (ModuleCat.{u + 1} Λ) f).obj
            ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              ((constantSheaf X.smallEtaleTopology
                  (ModuleCat.{u + 1} Λ)).obj
                (ModuleCat.of Λ
                  ((F i.succ : Type (u + 1)) ⧸
                    ((F i.castSucc).comap (F i.succ).subtype))))))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerStarPlus
            (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let G := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  let T := C ⋙ _root_.DerivedCategory.singleFunctor _ 0 ⋙ G
  have : G.Additive := inferInstanceAs
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.Additive
  have : T.Additive := inferInstance
  let P := Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
  have compare (N : ModuleCat.{u + 1} Λ) (n : ℤ) :
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj (C.obj N)))) ↔
        Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ n).obj (T.obj N)) := by
    rw [Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf]
    let e := (_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (C.obj N)))
    exact ⟨fun h ↦ by
      have := h
      exact Scheme.IsConstructibleSheaf.of_iso
        (F := (DerivedCategory.Plus.homologyFunctor _ n).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj (C.obj N)))) e,
      fun h ↦ by
        have := h
        exact Scheme.IsConstructibleSheaf.of_iso
          (F := (_root_.DerivedCategory.homologyFunctor _ n).obj (T.obj N)) e.symm⟩
  have hF : ∀ i : Fin (r + 1), P (T.obj (ModuleCat.of Λ (F i))) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have : Subsingleton (F 0) := by
        rw [hzero]
        infer_instance
      exact ObjectProperty.prop_of_isZero P
        (Functor.map_isZero T (ModuleCat.isZero_of_subsingleton (ModuleCat.of Λ (F 0))))
    | succ i hi =>
      let A := F i.castSucc
      let B := F i.succ
      let Q := A.comap B.subtype
      let a := Submodule.inclusion (hincreasing i)
      let S := ModuleCat.shortComplexOfCompEqZero a Q.mkQ (by
        ext x
        exact (Submodule.Quotient.mk_eq_zero Q).2 x.property)
      have : Finite (B ⧸ Q) := Finite.of_surjective _ (Submodule.mkQ_surjective Q)
      have : Finite S.X₃ := inferInstanceAs (Finite (B ⧸ Q))
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_iff.2 (by
          change Q.mkQ.ker = a.range
          rw [Submodule.ker_mkQ, Submodule.range_inclusion]))
        (Submodule.inclusion_injective (hincreasing i)) (Submodule.mkQ_surjective Q)
      exact Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact
        f hS hi (fun n ↦ (compare _ n).1 (hgraded i n))
  have hM : P (T.obj M) := P.prop_of_iso
    (T.mapIso (LinearEquiv.ofTop (F (Fin.last r)) hwhole).toModuleIso) (hF (Fin.last r))
  exact (compare M q).2 (hM q)

end AlgebraicGeometry
