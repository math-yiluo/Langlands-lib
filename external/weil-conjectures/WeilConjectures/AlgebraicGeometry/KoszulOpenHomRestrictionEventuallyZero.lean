/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomHomologyComparison
import WeilConjectures.Algebra.Homology.FilteredModuleComplexHomologyZero

/-! # Degree-zero consequences of the Koszul-to-Čech comparison

Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
-/

@[expose] public section

universe uMain wMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A derived morphism killed by restriction vanishes after a Koszul power transition.
Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
(blueprint: lem-sc-koszul-open-hom-restriction-eventually-zero)

Proof: Use the affine derived equivalence (Tag 06Z0) to represent E by a termwise
quasi-coherent complex F, corresponding to an A-module complex M. Since each tail is
bounded finite free, its Hom-complex H^0 is derived Hom (K-projectivity). These
identifications respect precomposition by the power transitions. Exactness of filtered
colimits identifies the colimit of these Hom groups with H^0 of their Hom-complex
colimit. The canonical Koszul/Čech/derived-sections comparison is a quasi-isomorphism
(Tags 08D1, 08D2), hence injective on H^0. The image of a morphism is its restriction
composed with the inverse restricted augmentation, so a restriction-zero morphism has
zero image. Injectivity makes its colimit class zero. The element criterion for a
filtered colimit of modules gives a later stage b and equality to zero after the
transition I_b to I_e. For r=0 all tails vanish; if the open is empty because all f_i
are nilpotent, sufficiently large power transitions vanish. The zero morphism works
with b=e, and the case E=0 is immediate. -/
theorem koszulOpenHom_restriction_eventually_zero
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
 :
    let R := ((SheafOfModules.overFunctor.{uMain}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uMain}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{uMain}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1), R.map φ = 0 →
      ∃ (b : ℕ) (h : e ≤ b), koszulOpenMap A r f e b h ≫ φ = 0 := by
  intro R
  let := HasDerivedCategory.standard (ModuleCat.{uMain} A)
  obtain ⟨a, ⟨ha⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core A
  let M := DerivedCategory.Q.objPreimage (a.inverse.obj E)
  let γ := a.functor.mapIso (DerivedCategory.Q.objObjPreimageIso (a.inverse.obj E)) ≪≫
    a.counitIso.app E
  let F := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj M
  let eF : DerivedCategory.Q.obj F ≅ E.obj :=
    (ha.app M).symm ≪≫ (schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso γ
  have hF (n : ℤ) : (F.X n).IsQuasicoherent := by
    change ((tilde.functor (.of A)).obj (M.X n)).IsQuasicoherent
    exact (presentationTilde (R := .of A) (M.X n) .univ (by simp) _
      (Submodule.span_eq _)).isQuasicoherent
  obtain ⟨α, hα, hz⟩ := koszulOpenHom_homology_comparison A r f F hF E eF
  let N := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let D := koszulCechHomDiagram A r f N
  let C := koszulCechHomColimit A r f N
  let cmp := koszulCechDerivedComparison A r f F ≫
    (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom
  have : IsIso cmp := affine_koszul_cech_derived_comparison A r f F hF E eF
  let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{uMain} A) 0).app C).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{uMain} A) 0).map cmp
  have : IsIso β := inferInstance
  have hβ : Function.Injective β := (ConcreteCategory.isIso_iff_bijective β).mp
    inferInstance |>.1
  intro e φ hφ
  have hx : HomologicalComplex.homologyMap (colimit.ι D e) 0 (α e φ) = 0 := by
    apply hβ
    exact (hz e φ hφ).trans (map_zero β.hom).symm
  obtain ⟨b, h, hb⟩ := filteredModuleComplex_homology_eventually_zero A D 0 e (α e φ) hx
  refine ⟨b, h, (α b).injective ?_⟩
  rw [hα e b h φ, hb, map_zero]

end AlgebraicGeometry
