/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import WeilConjectures.AlgebraicGeometry.DerivedGlobalSectionsCohomologyCoproduct
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Compactness of the derived structure sheaf

Source: Stacks Project, Tag 09M1, proof of Proposition
perfect-proposition-compact-is-perfect, first paragraph
(blueprint: lem-pc-derived-tensor-unit-compact).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

private theorem qc_single (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) [M.IsQuasicoherent] :
    schemeDerivedQCohProperty X
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) := by
  intro n
  by_cases hn : n = 0
  · subst n
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app M
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm ‹M.IsQuasicoherent›
  · let e := (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).app
        ((CochainComplex.singleFunctor _ 0).obj M)
    have hz := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 M n hn
    have : CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      CategoryTheory.Limits.IsZero.of_iso hz e
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      SheafOfModules.free PEmpty.{u+1}
    have hf : CategoryTheory.Limits.IsZero F := by
      rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      exact PEmpty.elim i
    have hF : F.IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hf.iso this) hF


/-- The derived tensor unit is represented by a compact quasi-coherent object.
Source: Stacks Project, Tag 09M1, proof of Proposition
perfect-proposition-compact-is-perfect, first paragraph
(blueprint: lem-pc-derived-tensor-unit-compact).
Proof: The derived tensor unit is the structure sheaf in degree zero, since the
structure sheaf is flat; its cohomology is quasi-coherent. Let a be the structure
morphism to Spec(Z), using a universe lift of Z when necessary. It is quasi-compact
and quasi-separated. Derived pullback takes the structure sheaf of Spec(Z) to
that of X. The derived adjunction therefore identifies Hom(O_X,N) naturally with
Hom(O_Spec(Z),Ra_*N). Derived direct image preserves coproducts of quasi-coherent
objects. The affine derived equivalence identifies the latter Hom group with
H^0 of a complex of Z-modules. Direct sums in that derived category are represented
termwise; exactness of direct sums of modules shows H^0 preserves them. These
identifications are additive and natural, so on each summand the comparison is
composition with its coproduct inclusion. Thus the canonical Hom direct-sum map
is bijective, including the empty family. -/
theorem exists_compact_derivedTensorUnit (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∃ U : schemeDerivedQCohCategory X,
      Nonempty (U.obj ≅ 𝟙_ (schemeDerivedCategory X)) ∧ IsCompactObject U := by
  classical
  let : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  let O := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings X.toRingedSpace))
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hO : schemeDerivedQCohProperty X O := qc_single X _
  let U : schemeDerivedQCohCategory X := ⟨O, hO⟩
  refine ⟨U, ⟨Iso.refl _⟩, ?_⟩
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))
  let F := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤))) 0 ⋙
    forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))
      AddCommGrpCat
  obtain ⟨e, he⟩ := derivedStructureSheaf_hom_hypercohomology X
  intro I E
  let : HasCoproducts.{u} (schemeDerivedCategory X) := derivedAmbientHasCoproducts X
  let : (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  let inc := (schemeDerivedQCohProperty X).ι
  have hc : IsColimit (Cofan.mk (∐ E).obj (fun i ↦ (Sigma.ι E i).hom)) := by
    exact (Cofan.isColimitMapCoconeEquiv inc E
      (Cofan.mk (∐ E) (Sigma.ι E))).toFun
      (isColimitOfPreserves inc (coproductIsCoproduct E))
  have hbij := derivedGlobalSections_cohomology_coproduct X I E (∐ E).obj
    (fun i ↦ (Sigma.ι E i).hom) hc
  let e' (N : schemeDerivedQCohCategory X) : (U ⟶ N) ≃+ F.obj N.obj :=
    { toFun := fun f ↦ e N.obj f.hom
      invFun := fun x ↦ ObjectProperty.homMk ((e N.obj).symm x)
      left_inv := by intro f; apply inc.map_injective; exact (e N.obj).symm_apply_apply _
      right_inv := by intro x; exact (e N.obj).apply_symm_apply x
      map_add' := by intro f g; exact (e N.obj).map_add _ _ }
  let d := DirectSum.map (fun i ↦ (e' (E i)).toAddMonoidHom)
  have hd : Function.Bijective d := ⟨
    (DirectSum.map_injective _).2 (fun i ↦ (e' (E i)).injective),
    (DirectSum.map_surjective _).2 (fun i ↦ (e' (E i)).surjective)⟩
  let c := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp U (Sigma.ι E i))
  let b := DirectSum.toAddMonoid (fun i ↦ (F.map (Sigma.ι E i).hom).hom)
  have hs : (e' (∐ E)).toAddMonoidHom.comp c = b.comp d := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply, c, b, d, DirectSum.toAddMonoid_of,
      DirectSum.map_of]
    exact he _ _ (Sigma.ι E i).hom f.hom
  have hcomp : Function.Bijective ((e' (∐ E)).toAddMonoidHom.comp c) := by
    rw [hs]
    exact hbij.comp hd
  exact ⟨fun x y h ↦ hcomp.1 (congrArg (e' (∐ E)) h), fun y ↦ by
    obtain ⟨x, hx⟩ := hcomp.2 (e' (∐ E) y)
    exact ⟨x, (e' (∐ E)).injective hx⟩⟩

end AlgebraicGeometry
