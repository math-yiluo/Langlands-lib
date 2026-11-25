/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Bounded residue fibre cohomology of a strictly perfect neighbourhood

## References

* Stacks Project, More on Algebra, Tag 0BCD
* Stacks Project, Cohomology of Sheaves, Tag 08C4 (strictly perfect complexes)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A finite-free retract of structure-sheaf modules is flat. -/
private theorem flat_of_finiteFree_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (ι : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
    (π : SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ M)
    (h : ι ≫ π = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨ι, π, h⟩ hf).2

/-- A strictly perfect neighbourhood gives common finite support bounds for
residue-fibre Betti numbers. -/
theorem finiteFiberCohomologyBounded
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P)) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0 := by
  obtain ⟨V, hx, P, hP, ⟨e⟩⟩ := hlocal
  let T := Spec (X.residueField x)
  let W : T.Opens := ⊤
  let g := X.fromSpecResidueField x
  have hWV : W ≤ g ⁻¹ᵁ V := by
    intro t _
    change g t ∈ V
    simpa only [g, X.fromSpecResidueField_apply] using hx
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let A : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Modules.overEquiv V).functor
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let S := SheafOfModules.overFunctor.{u} (moduleRings T.toRingedSpace) W
  let B : SheafOfModules.{u} ((moduleRings T.toRingedSpace).over W) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    (Modules.overEquiv W).functor
  have : B.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (R ⋙ A) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ A) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (S ⋙ B) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (S ⋙ B) := comp_preservesFiniteColimits _ _
  let C := (A.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hP
  have hCbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (C.X n) :=
    ⟨b, fun n hn ↦ A.map_isZero (hb n (Or.inr hn))⟩
  have hCflat : ∀ n : ℤ, SheafOfModules.IsFlat (C.X n) := by
    intro n
    obtain ⟨m, ι, π, hιπ⟩ := hp n
    let ei : A.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free (R := moduleRings V.toScheme.toRingedSpace)
          (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison A (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over V)))).symm ≪≫
      Sigma.mapIso (fun _ ↦ V.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
    apply flat_of_finiteFree_retract V.toScheme (C.X n) m
      (A.map ι ≫ ei.hom) (ei.inv ≫ A.map π)
    change (A.map ι ≫ ei.hom) ≫ ei.inv ≫ A.map π = 𝟙 (A.obj (P.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hιπ]
    exact A.map_id _
  let f := g.resLE V W hWV
  obtain ⟨F, _, _, hFadd, _, _, ⟨eF, _⟩⟩ :=
    flatComplexDerivedPullback f C hCbounded hCflat
  let := hFadd
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let q : (derivedPullback f).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj FC :=
    (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso _).app C).symm ≪≫
      eF.symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app C) ≪≫
      (DerivedCategory.quotientCompQhIso _).app FC
  let eC : (R ⋙ A).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj C :=
    (Functor.mapDerivedCategoryCompIso R A).symm.app E ≪≫
      A.mapDerivedCategory.mapIso e ≪≫ A.mapDerivedCategoryFactors.app P
  obtain ⟨θ⟩ := derivedPullback_openRestriction_iso_universes g W V hWV
  let eFC : (S ⋙ B).mapDerivedCategory.obj ((derivedPullback g).obj E) ≅
      DerivedCategory.Q.obj FC :=
    θ.app E ≪≫ (derivedPullback f).mapIso eC ≪≫ q
  have hS : S.Faithful := by
    constructor
    intro M N α β h
    ext U s
    exact congrArg
      (fun γ ↦ γ.val.app (Opposite.op (Over.mk (homOfLE (le_top : U.unop ≤ ⊤)))) s) h
  have : (S ⋙ B).Faithful := inferInstance
  refine ⟨a, b, ?_⟩
  intro i hi
  have hFC : IsZero (FC.X i) := F.map_isZero (A.map_isZero (hb i hi))
  have hhom : IsZero (FC.homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hFC
  have hder : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((S ⋙ B).mapDerivedCategory.obj ((derivedPullback g).obj E))) :=
    hhom.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eFC ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app FC)
  have hzero := (S ⋙ B).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    hder
  have : (SheafOfModules.evaluation.{u} (moduleRings T.toRingedSpace)
      (Opposite.op ⊤)).Additive :=
    inferInstanceAs ((SheafOfModules.forget _ ⋙
      PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)
  have hcoh : IsZero (derivedFiberCohomology X E i x) :=
    (ModuleCat.restrictScalars (ΓSpecIso (X.residueField x)).inv.hom).map_isZero
      ((SheafOfModules.evaluation.{u} (moduleRings T.toRingedSpace) (Opposite.op ⊤)).map_isZero
        hzero)
  let := ModuleCat.subsingleton_of_isZero hcoh
  exact Module.finrank_zero_of_subsingleton

end
end AlgebraicGeometry.Scheme
