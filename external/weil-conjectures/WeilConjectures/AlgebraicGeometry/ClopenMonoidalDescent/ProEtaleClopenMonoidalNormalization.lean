/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenTotalTensorKFlatDetection
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import Mathlib.CategoryTheory.Pi.Monoidal

/-! # Normalization interface for clopen derived tensor restriction

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7D, 06YU and 0FPT;
finite-clopen application, steps 8-9 of the tensor-calculus construction
(blueprint: lem-pur-clopen-kflat-monoidal-descent).

Restriction and its localization comparison are those of the module-gluing and unbounded
localization nodes. The native derived tensor carries the prescribed total-tensor constraints.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

/-- The existing abelian structure with the module universe fixed explicitly.
Source: Stacks 03D7 (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
instance modulesAbelian {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Abelian (clopenTensorModules.{t, u} R) :=
  ClopenLocalization.modulesAbelian.{t, max u (t + 1), u, 0} _

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (clopenTensorRestriction.{t, u} j R) :=
  ClopenLocalization.restrictionLimits.{t, max u (t + 1), u, 0} j _

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteColimits (clopenTensorRestriction.{t, u} j R) :=
  ClopenLocalization.restrictionColimits.{t, max u (t + 1), u, 0} j _

/-- Standard unbounded localization in the fixed module universe.
Source: Stacks 05RU (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (clopenTensorModules.{t, u} R) :=
  HasDerivedCategory.standard (clopenTensorModules.{t, u} R)

/-- The existing native K-flat monoidal structure, with its prescribed associator and units.
Source: Stacks 06YU, 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
@[instance_reducible]
instance monoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (clopenTensorModules.{t, u} R)) :=
  RingedDerivedNative.monoidal.{t + 1, t, u} (topology X) R

/-- The existing native Koszul symmetry, including its involutivity.
Source: Stacks 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
@[instance_reducible]
instance symmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (clopenTensorModules.{t, u} R)) :=
  RingedDerivedNative.symmetric.{t + 1, t, u} (topology X) R

/-- The specified exact localization of the dependency's actual restriction.
No representatives, roofs or derived equivalences are chosen here.
Source: Stacks 015F, 06YU (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    DerivedCategory (clopenTensorModules.{t, u} R) ⥤
      DerivedCategory (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) :=
  ClopenLocalization.derivedRestriction.{t, max u (t + 1), u, 0} j
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)

/-- The canonical degreewise localization comparison of the recorded exact restriction.
Source: Stacks 015F, 06YU (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def factors {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (DerivedCategory.Q.{max (u + 1) (t + 2)} :
      CochainComplex (clopenTensorModules.{t, u} R) ℤ ⥤ _) ⋙
        derivedRestriction.{t, u} j R ≅
      clopenTensorComplexRestriction.{t, u} j R ⋙
        (DerivedCategory.Q.{max (u + 1) (t + 2)} :
          CochainComplex (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) ℤ
            ⥤ _) :=
  (clopenTensorRestriction.{t, u} j R).mapDerivedCategoryFactors

/-- The bifunctor type of the displayed comparison, for all derived objects and morphisms.
Source: Stacks 06YU, 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
abbrev Comparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  tensor (DerivedCategory (clopenTensorModules.{t, u} R)) ⋙ derivedRestriction.{t, u} j R ≅
    ((derivedRestriction.{t, u} j R).prod (derivedRestriction.{t, u} j R)) ⋙
      tensor (DerivedCategory (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)))

/-- The normalized total-complex comparison is exactly the dependency's one: ordinary
local pure tensors and every direct-sum summand fix it. No bounds on complexes are imposed.
Source: Stacks 0GMW, 06YN, 0FPQ
(blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def TotalNormalization {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y) ((clopenTensorRings.{t, u} j).obj R)) :
    Prop :=
  (∀ (F H : clopenTensorModules.{t, u} R) (U : Y.ProEt)
    (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).obj U)))
    (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).obj U))),
    (clopenTensorComparison.{t, u} j R h F H).hom.val.app (op U)
        (clopenTensorPure.{t, u} R F H _ x y) =
      clopenTensorPure.{t, u} ((clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorRestriction.{t, u} j R).obj F) ((clopenTensorRestriction.{t, u} j R).obj H)
        (op U) x y) ∧
  (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (U : Y.ProEt)
    (x : (P.X p).val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).obj U)))
    (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).obj U))),
    (((b.hom.app (P, Q)).f n).val.app (op U))
        (coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq _ x y) =
      coefficientTensorGenerator.{u, t + 1, t} (topology Y) ((clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P)
        ((clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq (op U) x y)

/-- The K-flat computation square, with the canonical localization comparisons on all
three complexes. The two routes are maps from restricted localized total tensor to the
component derived tensor. Flatness is required degreewise, and K-flatness is unbounded.
Source: Stacks 06YS, 0G7D, 06YU
(blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def ModelNormalization {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y) ((clopenTensorRings.{t, u} j).obj R))
    (c : Comparison.{t, u} j R) : Prop :=
  ∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
    (_hflatP : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (P.X n))
    (_hflatQ : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (Q.X n))
    (hiP : CochainComplex.IsKFlatIndependentCoefficients (J := topology Y)
      (R := (clopenTensorRings.{t, u} j).obj R)
      ((clopenTensorComplexRestriction.{t, u} j R).obj P)),
    (derivedRestriction.{t, u} j R).map
        (RingedDerivedNative.tensorIso.{t + 1, t, u, max (u + 1) (t + 2)}
          (topology X) R P Q (Or.inl hP)).hom ≫
      c.hom.app (DerivedCategory.Q.{max (u + 1) (t + 2)}.obj P,
        DerivedCategory.Q.{max (u + 1) (t + 2)}.obj Q) ≫
      tensorHom ((factors.{t, u} j R).hom.app P)
        ((factors.{t, u} j R).hom.app Q) =
    (factors.{t, u} j R).hom.app
        ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
      DerivedCategory.Q.{max (u + 1) (t + 2)}.map (b.hom.app (P, Q)) ≫
      (RingedDerivedNative.tensorIso.{t + 1, t, u, max (u + 1) (t + 2)} (topology Y)
        ((clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P)
        ((clopenTensorComplexRestriction.{t, u} j R).obj Q) (Or.inl hiP)).hom

/-- The inverse tensorator of a strong braided derived restriction, as a bifunctor iso.
Source: Stacks 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def braidedComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (d : (derivedRestriction.{t, u} j R).Braided) : Comparison.{t, u} j R :=
  letI := d
  (Functor.Monoidal.μNatIso (derivedRestriction.{t, u} j R)).symm

/-- The unit isomorphism is the localization of ordinary restriction of the ring module,
with the canonical comparison for the degree-zero single complex.
Source: Stacks 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def unitComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) :
    (derivedRestriction.{t, u} j R).obj
        (𝟙_ (DerivedCategory (clopenTensorModules.{t, u} R))) ≅
      𝟙_ (DerivedCategory (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R))) := by
  letI : HasDerivedCategory.{max (u + 1) (t + 2)} (clopenTensorModules.{t, u} R) :=
    hasDerived.{t, u} R
  letI : HasDerivedCategory.{max (u + 1) (t + 2)}
      (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) :=
    hasDerived.{t, u} ((clopenTensorRings.{t, u} j).obj R)
  letI : MonoidalCategory (clopenTensorModules.{t, u} R) :=
    SheafOfModules.cochainModulesMonoidal R
  letI : MonoidalCategory
      (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) :=
    SheafOfModules.cochainModulesMonoidal ((clopenTensorRings.{t, u} j).obj R)
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact (derivedRestriction.{t, u} j R).mapIso
      (RingedDerivedNative.unitIso.{t + 1, t, u, max (u + 1) (t + 2)} (topology X) R) ≪≫
    (factors.{t, u} j R).app (𝟙_ (CochainComplex (clopenTensorModules.{t, u} R) ℤ)) ≪≫
    DerivedCategory.Q.{max (u + 1) (t + 2)}.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
          (𝟙_ (clopenTensorModules.{t, u} R))) ≪≫
    DerivedCategory.Q.{max (u + 1) (t + 2)}.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso
        (clopenTensorUnitComparison.{t, u} j R h)) ≪≫
    (RingedDerivedNative.unitIso.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) ((clopenTensorRings.{t, u} j).obj R)).symm

/-- The unit isomorphism supplied by a strong braided functor.
Source: Stacks 0FPT (blueprint: lem-pur-clopen-kflat-monoidal-descent). -/
def braidedUnit {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (d : (derivedRestriction.{t, u} j R).Braided) :
    (derivedRestriction.{t, u} j R).obj
        (𝟙_ (DerivedCategory (clopenTensorModules.{t, u} R))) ≅
      𝟙_ (DerivedCategory (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R))) :=
  letI := d
  (Functor.Monoidal.εIso (derivedRestriction.{t, u} j R)).symm

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
