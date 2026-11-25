/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit

/-! # Koszul perfect objects represent cohomology classes on a principal open

Source: Stacks Project, Section 36.9, Tags 08CX, 08DC, and 08DD
(blueprint: lem-sc-affine-perfect-open-represent-cohomology).
-/

@[expose] public section

universe uMain wMain

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Every Koszul tail is perfect, its augmentation is invertible on the finite
principal open, and the restriction cocone represents the filtered colimit of Hom.
The target is `Hom(O_U,E|_U)`, the degree-zero cohomology identification in Tag 08DC.
Restriction to `U` is first to the localized site and then transported by the
canonical equivalence `Scheme.Modules.overEquiv U`, so the target lives in `D(O_U)`.
Indices `e : ℕ` here correspond to positive exponents `e+1` in the source.
Source: Stacks, Tags 08CX, 08DC, and Proposition 08DD
(blueprint: lem-sc-affine-perfect-open-represent-cohomology).

Proof:
1. The tail is bounded finite free, hence perfect. Inverting any `f_i` makes
   the Koszul complex contractible, so the augmentation on the union is invertible
   (`lem-sc-affine-perfect-koszul-principal-unit`).
2. The exterior-power diagonal maps give the inverse system; the contraction formula
   proves that the augmentation commutes with each transition.
3. Represent `E` by a complex of quasi-coherent sheaves using
   `lem-pc-affine-qcoh-derived-equivalence`. Apply
   `lem-sc-affine-koszul-cech-derived-comparison` and take degree-zero cohomology,
   which commutes with filtered colimits. The bounded finite free tail is K-projective
   (`lem-sc-bounded-above-projective-kprojective`), so degree-zero Hom-complex
   cohomology is derived Hom even for unbounded `E`. Full faithfulness of the affine
   equivalence identifies these with the sheaf-derived Hom sets.
4. The resulting comparison is restriction followed by the inverse augmentation.
   Its compatibility makes it the displayed cocone; bijectivity identifies that
   cocone as a colimit. The empty family and zero object both give zero Hom groups. -/
theorem affine_perfect_open_represent_cohomology
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    (∀ e : ℕ, ∃ δ : koszulOpenKoszulObject A r f e ⟶
      (koszulOpenObject A r f e)⟦(1 : ℤ)⟧,
      Triangle.mk (koszulOpenUnit A r f e) (koszulOpenKoszulUnit A r f e) δ ∈
        distTriang (schemeDerivedCategory (Spec (.of A)))) ∧
    (∀ e : ℕ, Scheme.IsPerfect (Spec (.of A)) (koszulOpenObject A r f e)) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      koszulOpenMap A r f a b h ≫ koszulOpenUnit A r f a = koszulOpenUnit A r f b) ∧
    ∃ v : ∀ e : ℕ,
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenStructure A) ⟶
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenObject A r f e),
      (∀ e : ℕ,
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) ≫ v e = 𝟙 _) ∧
      (∀ e : ℕ, v e ≫
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) = 𝟙 _) ∧
      ∃ ι : koszulOpenHomDiagram A r f E.1 ⟶
        (Functor.const ℕ).obj
          (((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
              (koszulOpenStructure A) ⟶
           ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj E.1),
        (∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1),
          ι.app e φ = v e ≫
            ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                      (koszulOpen A r f)) ⋙
                    Equivalence.functor
                      (C := SheafOfModules.{uMain}
                        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                      (D := SheafOfModules.{uMain}
                        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map φ) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  obtain ⟨htri, hperf, hmap⟩ :=
    affine_perfect_open_represent_cohomology_core A r f
  have hcol := affine_perfect_open_represent_cohomology_colimit A r f E
  exact ⟨htri, hperf, hmap, hcol⟩

end AlgebraicGeometry
