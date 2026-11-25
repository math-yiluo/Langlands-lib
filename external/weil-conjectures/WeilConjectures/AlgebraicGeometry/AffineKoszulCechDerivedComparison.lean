/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonIsIso
import WeilConjectures.AlgebraicGeometry.PrincipalCechResolutionQuasiIso

/-! # Koszul Hom colimits compute derived sections on a principal-open union

Source: Stacks Project, Tags 08D1 and 08D2
(blueprint: lem-sc-affine-koszul-cech-derived-comparison).
-/

@[expose] public section

universe uT wT vT

open CategoryTheory

namespace AlgebraicGeometry

/-- For an unbounded complex of quasi-coherent modules on Spec(A), the canonical
Koszul-to-alternating-Čech map followed by the Čech-to-derived-sections map is an
isomorphism in D(A), equivalently a quasi-isomorphism of its complex representatives.
The positive exponent e is indexed by e-1 in the natural-number diagram.

Source: Stacks, Tags 08D1 and 08D2
(blueprint: lem-sc-affine-koszul-cech-derived-comparison).

Proof:
1. Identify F with the termwise associated sheaf of its global-section complex M
by affine quasi-coherence (Tags 01IA and 01HV). The tails I_e are bounded finite free,
and precomposition with their power-transition maps gives koszulCechHomDiagram.
The localization formula, including the sign (-1)^(pq+p(p-1)/2), identifies its
colimit with the alternating Čech total complex (lem-sc-affine-koszul-hom-alternating-cech,
Tag 08D1). The identification respects every face map and the vertical differential.
2. Each intersection of the finite principal-open cover is affine (Tag 01HS).
The unbounded alternating Čech derived-section comparison applies by affine vanishing
(Tag 01XB): lem-sc-qcoh-complex-alternating-cech-derived-sections, Tag 08D2/08C2.
It identifies the same total complex with RΓ(U,F), in D(A) by restriction of scalars.
3. Compose these canonical comparisons and transport along the chosen representation
of E by F. This is the map in the statement. For r=0 all alternating rows and the
Koszul Hom colimit vanish and U is empty; for F=0 both sides are zero. -/
theorem affine_koszul_cech_derived_comparison
    (A : Type uT) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wT}
      (SheafOfModules.{uT} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{vT} (ModuleCat.{uT} A)]
    (F : CochainComplex
      (SheafOfModules.{uT} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (e : DerivedCategory.Q.obj F ≅ E.obj) :
    IsIso (koszulCechDerivedComparison A r f F ≫
      (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map e.hom) := by
  have : IsIso (koszulCechComparison A r f F) :=
    koszulCechComparison_isIso A r f F hF
  obtain ⟨J, hJ, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective F
  let _ := hJ
  let _ := hi
  have : QuasiIso ((principalCechFunctor r f).map i) :=
    principalCech_resolution_quasiIso A r f F J hF i
  have : QuasiIso ((principalCechAugmentation r f).app J) :=
    principalCechAugmentation_quasiIso r f J
  have hβ := (principalCechDerivedComparison_exists r f F).choose_spec J i
  have : IsIso (principalCechDerivedComparison r f F ≫
      (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map
        (DerivedCategory.Q.map i) ≫
      ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((principalCechAugmentation r f).app J)) := by
    dsimp only [koszulOpen, principalCechDerivedComparison]
    rw [hβ]
    infer_instance
  have : IsIso (principalCechDerivedComparison r f F) :=
    IsIso.of_isIso_comp_right _
      ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map
          (DerivedCategory.Q.map i) ≫
        ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((principalCechAugmentation r f).app J))
  dsimp only [koszulCechDerivedComparison]
  infer_instance

end AlgebraicGeometry
