/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparison
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Naturality of the localized comparison into derived pullback

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-pullback-naturality).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem map_conjugate_comp_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (L : D ⥤ E) (G : C ⥤ E) (j : F ⋙ L ⟶ G)
    {P Q : C} {U V : D} (s : F.obj P ≅ U) (t : F.obj Q ≅ V) (a : P ⟶ Q) :
    L.map (s.inv ≫ F.map a ≫ t.hom) ≫ (L.map t.inv ≫ j.app Q) =
      (L.map s.inv ≫ j.app P) ≫ G.map a := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc t.hom, t.hom_inv_id, L.map_id, Category.id_comp]
  exact congrArg (fun k ↦ L.map s.inv ≫ k) (j.naturality a)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- The comparison with the cohomology of the canonical derived pullback.
Its construction uses the invertible pullback counit on the representative, the
specified tensor-stalk isomorphism, and the localization comparison; no target
complex or morphism to a target is involved.
(blueprint: lem-pc-stalk-comparison-pullback-naturality)
-/
def comparisonIntoPullback (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  letI := hP
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
    (comparisonStalkCohomology X' z i).map
      (cast (by rfl)
        (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
        (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ⟶
          (derivedPullback g').obj (DerivedCategory.Q.obj P))

/-- The comparison into derived pullback is natural for derived isomorphisms of
K-flat sheaf representatives, using any tensor-algebra lift of the specified
underlying cohomology transport.

Proof: stalk K-flatness follows from the K-flat stalk criterion. Ordinary extension
from A to C therefore computes derived extension on each stalk representative.
The derived stalk of sheaf pullback identifies with this derived extension: on
complexes this is tensorStalkIso, and the two universal derived counits determine
the identification on the localized category. The transformation from base-derived
tensor to A-derived extension is induced by scalar extension and tensor
associativity. Its naturality holds on complexes and descends through localization;
thus it holds for the derived isomorphism a, without choosing a chain map for a.
Apply cohomology and use the counit-compatible comparison between the two base
derived tensor functors. The equations comparison_eq identify their cohomology
comparisons with these counits, and localized_eq transposes these comparisons
through extension/restriction adjunction. Naturality of tensorStalkIso and the
homology localization factors then gives the displayed equation. Faithfulness of
restriction to B identifies the given e with the tensor-algebra transport. Extend
e to C; functoriality of extension and the preceding adjunction equation yield
exactly the square below. No isomorphism assertion about localizedComparison is
used, and no flatness over R or Tor-independence of the square is required.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8; Cohomology,
Tag 06YB (K-flat stalks), and Tag 06Y6 (derived tensor functoriality).
(blueprint: lem-pc-stalk-comparison-pullback-naturality). -/
theorem comparisonIntoPullback_naturality (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∀ e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom →
      comparisonIntoPullback f f' g g' sq z P hcP i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map a.hom) =
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))).map e.hom ≫
        comparisonIntoPullback f f' g g' sq z Q hcQ i := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  intro e he
  obtain ⟨L, ε, hL, j, hj⟩ := exists_stalkDerivedExtensionComparison f f' g g' sq z
  obtain ⟨hsP, hjP⟩ := hj P hP hcP
  obtain ⟨hsQ, hjQ⟩ := hj Q hQ hcQ
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
  let b : DerivedCategory.Q.obj (stalkComplex g' z P) ≅
      DerivedCategory.Q.obj (stalkComplex g' z Q) :=
    T.mapDerivedCategoryFactors.symm.app P ≪≫
      (comparisonDerivedStalk X (g' z)).mapIso a ≪≫
      T.mapDerivedCategoryFactors.app Q
  have he' :
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
      (ModuleCat.baseTensorSourceIso (R f g' z) (A g' z) (B f' z) (C z)
        (cohomologyModel f f' g g' sq z P) (cohomologyModel f f' g g' sq z Q) b i).hom := by
    rw [he]
    simp only [comparisonSourceUnderlyingIso, comparisonModelInputIso,
      comparisonModelDerivedIso, comparisonBaseRestriction, comparisonDerivedStalk,
      ModuleCat.baseTensorSourceIso, ModuleCat.baseTensorInputIso, b, T,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Functor.map_comp, Category.assoc]
  have hn := ModuleCat.baseDerivedTensor_localized_naturality
    (R f g' z) (A g' z) (B f' z) (C z)
    (cohomologyModel f f' g g' sq z P) (cohomologyModel f f' g g' sq z Q)
    L ε hL hsP hsQ b i e he'
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (C z)) i
  let kP := L.map (T.mapDerivedCategoryFactors.inv.app P) ≫
    j.hom.app (DerivedCategory.Q.obj P)
  let kQ := L.map (T.mapDerivedCategoryFactors.inv.app Q) ≫
    j.hom.app (DerivedCategory.Q.obj Q)
  have hk : L.map b.hom ≫ kQ =
      kP ≫ (comparisonDerivedStalk X' z).map ((derivedPullback g').map a.hom) := by
    exact map_conjugate_comp_naturality (comparisonDerivedStalk X (g' z)) L
      (derivedPullback g' ⋙ comparisonDerivedStalk X' z) j.hom
      (T.mapDerivedCategoryFactors.app P) (T.mapDerivedCategoryFactors.app Q) a.hom
  have hkH : H.map (L.map b.hom) ≫ H.map kQ =
      H.map kP ≫ (comparisonStalkCohomology X' z i).map
        ((derivedPullback g').map a.hom) := by
    simpa only [← Functor.map_comp, H, comparisonStalkCohomology, Functor.comp_map]
      using congrArg H.map hk
  have hcompP : comparisonIntoPullback f f' g g' sq z P hcP i =
      (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
        (ModuleCat.scalarExtensionHomologyIso _ L ε (stalkComplex g' z P) hsP i).inv ≫
          H.map kP := by
    simpa only [comparisonIntoPullback, H, kP, T, Category.assoc]
      using (congrArg (fun t =>
        (cohomologyModel f f' g g' sq z P).localizedComparison i ≫ t) (hjP i)).symm
  have hcompQ : comparisonIntoPullback f f' g g' sq z Q hcQ i =
      (cohomologyModel f f' g g' sq z Q).localizedComparison i ≫
        (ModuleCat.scalarExtensionHomologyIso _ L ε (stalkComplex g' z Q) hsQ i).inv ≫
          H.map kQ := by
    simpa only [comparisonIntoPullback, H, kQ, T, Category.assoc]
      using (congrArg (fun t =>
        (cohomologyModel f f' g g' sq z Q).localizedComparison i ≫ t) (hjQ i)).symm
  rw [hcompP, hcompQ]
  have hn' := congrArg (fun t => t ≫ H.map kQ) hn
  simp only [Category.assoc] at hn' ⊢
  rw [hkH] at hn'
  exact hn'

end AlgebraicGeometry.SingleComplexBaseChange
