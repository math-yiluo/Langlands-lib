/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceDerivedStalkComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Recovering algebraic constant values on a nonempty slice

Source: Stacks Project, Tags 03CY, 0F6B and 05RU.
(blueprint: lem-weil-pbc-finite-constant-slice-iso-reflects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem ulift_preservesColimits (B : Type t) [CommRing B] :
    PreservesColimitsOfSize.{t, t} (ModuleCat.uliftFunctor.{t + 1, t} B) := by
  let U := forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1}
  have : PreservesColimitsOfSize.{t, t} (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ U) := by
    change PreservesColimitsOfSize.{t, t}
      (forget₂ (ModuleCat.{t} B) AddCommGrpCat.{t} ⋙ AddCommGrpCat.uliftFunctor.{t + 1, t})
    infer_instance
  have : ReflectsColimitsOfSize.{t, t} U :=
    { reflectsColimitsOfShape := fun {_} _ ↦
        reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesColimits_of_reflects_of_preserves _ U

private theorem lifted_resolution (B : Type t) [CommRing B]
    (M : CochainComplex (ModuleCat.{t} B) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{t} B) ℤ) (q : P ⟶ M),
      QuasiIso q ∧
      CochainComplex.IsKProjective
        (((ModuleCat.uliftFunctor.{t + 1, t} B).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let L := ModuleCat.uliftFunctor.{t + 1, t} B
  let C := L.mapHomologicalComplex (.up ℤ)
  have (I : Type t) : HasColimitsOfShape (Discrete I) (ModuleCat.{t + 1} B) :=
    ModuleCat.hasColimitsOfShape _ _
  have (I : Type (t + 1)) : HasColimitsOfShape (Discrete I) (ModuleCat.{t + 1} B) :=
    ModuleCat.hasColimitsOfShape _ _
  have (I : Type t) : HasColimitsOfShape (Discrete I)
      (CochainComplex (ModuleCat.{t + 1} B) ℤ) :=
    ⟨fun F ↦ ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩⟩
  have (I : Type (t + 1)) : HasColimitsOfShape (Discrete I)
      (CochainComplex (ModuleCat.{t + 1} B) ℤ) :=
    ⟨fun F ↦ ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩⟩
  have : PreservesColimitsOfSize.{t, t} L := ulift_preservesColimits B
  obtain ⟨P, q, hq, F, ι, step, hz, hm, hc, he, hs, hquot⟩ :=
    CochainComplex.exists_large_filtered_free_resolution.{t, t} M
  refine ⟨P, q, hq, ?_⟩
  apply CochainComplex.isKProjective_of_filtered_free.{t, t + 1}
    (C.obj P) (fun n ↦ C.obj (F n)) (fun n ↦ C.map (ι n)) (fun n ↦ C.map (step n))
  · exact C.map_isZero hz
  · intro n
    have := hm n
    infer_instance
  · intro n
    rw [← C.map_comp, hc]
  · intro k x
    obtain ⟨n, y, hy⟩ := he k x.down
    exact ⟨n, ULift.up y, congrArg ULift.up hy⟩
  · intro n k
    obtain ⟨r, hr⟩ := hs n k
    refine ⟨L.map r, ?_⟩
    change L.map ((step n).f k) ≫ L.map r = _
    rw [← L.map_comp, hr, L.map_id]
    rfl
  · intro n
    obtain ⟨I, d, ⟨e⟩⟩ := hquot n
    let S (i : I) :=
      (HomologicalComplex.single (ModuleCat.{t} B) (.up ℤ) (d i)).obj
        (ModuleCat.of B (ULift.{t} B))
    refine ⟨ULift.{t + 1} I, fun i ↦ d i.down, ⟨?_⟩⟩
    refine (PreservesCokernel.iso C (step n)).symm ≪≫ C.mapIso e ≪≫
      (asIso (sigmaComparison C S)).symm ≪≫
      (Sigma.reindex (Equiv.ulift : ULift.{t + 1} I ≃ I) (fun i ↦ C.obj (S i))).symm ≪≫
      Sigma.mapIso (fun i ↦ ?_)
    refine (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) (d i.down)).app _ ≪≫
      (HomologicalComplex.single (ModuleCat.{t + 1} B) (.up ℤ) (d i.down)).mapIso ?_
    exact ((ULift.moduleEquiv.trans ULift.moduleEquiv).trans
      ULift.moduleEquiv.symm).toModuleIso

private theorem ulift_reflects_derived_iso (B : Type t) [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{t + 1} B)]
    (P Q : CochainComplex (ModuleCat.{t} B) ℤ)
    (e : DerivedCategory.Q.obj
        (((ModuleCat.uliftFunctor.{t + 1, t} B).mapHomologicalComplex (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.uliftFunctor.{t + 1, t} B).mapHomologicalComplex (.up ℤ)).obj Q)) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  let C := (ModuleCat.uliftFunctor.{t + 1, t} B).mapHomologicalComplex (.up ℤ)
  obtain ⟨P', q, hq, hP'⟩ := lifted_resolution B P
  have : QuasiIso q := hq
  have : CochainComplex.IsKProjective (C.obj P') := hP'
  let a : DerivedCategory.Q.obj (C.obj P') ≅ DerivedCategory.Q.obj (C.obj Q) :=
    asIso (DerivedCategory.Q.map (C.map q)) ≪≫ e
  obtain ⟨f, hf⟩ := CochainComplex.IsKProjective.exists_Q_map_eq
    (C.obj P') (C.obj Q) a.hom
  obtain ⟨g, hg⟩ := C.map_surjective f
  have : IsIso (DerivedCategory.Q.map (C.map g)) := by
    rw [hg, hf]
    infer_instance
  have : QuasiIso (C.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (C.map g)).mp inferInstance
  have : QuasiIso g :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology g
      (ModuleCat.uliftFunctor.{t + 1, t} B)).mp inferInstance
  exact ⟨(asIso (DerivedCategory.Q.map q)).symm ≪≫ asIso (DerivedCategory.Q.map g)⟩

/-- Isomorphic constant realizations on a nonempty slice have isomorphic algebraic
values. The coefficient change is an isomorphism; no finite generation, bounds,
projectivity, adic datum, or residue hypothesis is used.

Source: Stacks Project, Tags 03CY, 0F6B, 00Y8(3) and 05RU.
(blueprint: lem-weil-pbc-finite-constant-slice-iso-reflects).

Proof: choose a geometric point of W by algebraically closing the residue field
of any point of W. Identify the slice at W with the pro-etale site of W. Restrict
scalars along the supplied coefficient isomorphism and apply the
exact geometric module stalk functor. The constant-germ maps identify its composite
with constant realization with the universe-lift functor, naturally in module maps,
hence in every differential. Exactness lets this identification descend to the
unbounded derived categories. Apply the resulting derived stalk functor to the given
isomorphism. Finally choose a small filtered-free resolution of P. Its universe lift
remains filtered free and hence K-projective. Represent the resulting large derived
isomorphism by a chain map out of that resolution. Fullness of universe lift on
complexes descends the chain map, and exact fully faithful universe lift reflects its
quasi-isomorphism property. Localizing this map and the resolution gives the required
small derived isomorphism.
This argument needs a point only on W, and applies to zero rings and zero complexes. -/
theorem finiteConstantSlice_iso_reflects
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ)
    (W : X.Etale) (hW : Nonempty W.left)
    (P Q : CochainComplex (ModuleCat.{t} B) ℤ)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
          ((toProEt X).obj W) ((completedAdicDerivedChange X φ).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≅
        ringedSiteDerivedRestrictionOfUniverses
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
          ((toProEt X).obj W) ((completedAdicDerivedChange X φ).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X B Q))))) :
    Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  classical
  let : HasDerivedCategory (ModuleCat.{t + 1} B) := HasDerivedCategory.standard _
  let x : W.left := hW.some
  let Ω := AlgebraicClosure (W.left.residueField x)
  let y : Spec (.of Ω) ⟶ W.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (W.left.residueField x) Ω)) ≫
      W.left.fromSpecResidueField x
  obtain ⟨F, hF⟩ := finiteConstantSlice_derivedStalk_comparison X B R φ hφ W y
  obtain ⟨eP⟩ := hF P
  obtain ⟨eQ⟩ := hF Q
  obtain ⟨e⟩ := e
  exact ulift_reflects_derived_iso B P Q (eP.symm ≪≫ F.mapIso e ≪≫ eQ)

end AlgebraicGeometry.Scheme
