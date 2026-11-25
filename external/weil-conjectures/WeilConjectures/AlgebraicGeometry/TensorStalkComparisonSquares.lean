/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.TensorStalkFixedMapSquare
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Ring coordinates for tensor stalk comparisons

Source: Stacks Project, perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-stalk-comparison-squares).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false

namespace AlgebraicGeometry

private theorem spec_stalkCongr_fromSpecStalk {S : Scheme.{u}} {s t : S} (h : s = t) :
    Spec.map (S.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ S.fromSpecStalk s =
      S.fromSpecStalk t := by
  subst t
  simp

private theorem preimmersion_pullback_map
    {A B R X T S : Scheme.{u}} (a : A ⟶ R) (b : B ⟶ R)
    (f : X ⟶ S) (g : T ⟶ S) (iA : A ⟶ X) (iB : B ⟶ T) (iR : R ⟶ S)
    [IsPreimmersion iA] [IsPreimmersion iB] [Mono iR]
    (ha : a ≫ iR = iA ≫ f) (hb : b ≫ iR = iB ≫ g) :
    IsPreimmersion (pullback.map a b f g iA iB iR ha hb) := by
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

private theorem stalkTensor_flat
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    Module.Flat (TensorProduct (SingleComplexBaseChange.R f g' z)
      (SingleComplexBaseChange.A g' z) (SingleComplexBaseChange.B f' z))
      (SingleComplexBaseChange.C z) := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let R := SingleComplexBaseChange.R f g' z
  let A := SingleComplexBaseChange.A g' z
  let B := SingleComplexBaseChange.B f' z
  let C := SingleComplexBaseChange.C z
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let iA := X.fromSpecStalk (g' z)
  let iB := S'.fromSpecStalk (f' z)
  let iR := S.fromSpecStalk (f (g' z))
  have ha : a ≫ iR = iA ≫ f := by
    dsimp [a, iR, iA]
    change Spec.map (f.stalkMap (g' z)) ≫ _ = _
    exact Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hb : b ≫ iR = iB ≫ g := by
    dsimp [b, iR, iB]
    change Spec.map ((S.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun φ : X' ⟶ S ↦ φ z) sq.w))).hom ≫
        g.stalkMap (f' z)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have hp : f (g' z) = g (f' z) :=
      congrArg (fun φ : X' ⟶ S ↦ φ z) sq.w
    change Spec.map (g.stalkMap (f' z)) ≫
      Spec.map (S.presheaf.stalkCongr (Inseparable.of_eq hp)).hom ≫
        S.fromSpecStalk (f (g' z)) = _
    rw [spec_stalkCongr_fromSpecStalk hp]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk g
  let m := pullback.map a b f g iA iB iR ha hb
  have hm : IsPreimmersion m := preimmersion_pullback_map a b f g iA iB iR ha hb
  let h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R A B)
  let k : Spec (.of (TensorProduct R A B)) ⟶ X' := h.isoPullback.hom ≫ m ≫ sq.isoPullback.inv
  have hk : IsPreimmersion k := by
    dsimp [k]
    infer_instance
  let j := Spec.map (CommRingCat.ofHom (algebraMap (TensorProduct R A B) C))
  have hj : j ≫ k = X'.fromSpecStalk z := by
    apply sq.hom_ext
    · dsimp only [k]
      simp only [Category.assoc, sq.isoPullback_inv_fst]
      dsimp only [m, pullback.map]
      simp only [pullback.lift_fst]
      rw [h.isoPullback_hom_fst_assoc, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))) ≫ iA = _
      have hAC : (algebraMap (TensorProduct R A B) C).comp (algebraMap A (TensorProduct R A B)) =
          (g'.stalkMap z).hom :=
        (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).1
      rw [hAC]
      exact Scheme.SpecMap_stalkMap_fromSpecStalk g'
    · dsimp only [k]
      simp only [Category.assoc, sq.isoPullback_inv_snd]
      dsimp only [m, pullback.map]
      simp only [pullback.lift_snd]
      rw [h.isoPullback_hom_snd_assoc, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((algebraMap (TensorProduct R A B) C).comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫ iB = _
      have hBC : (algebraMap (TensorProduct R A B) C).comp
          Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap z).hom :=
        (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f f' g g' sq z)).2
      rw [hBC]
      exact Scheme.SpecMap_stalkMap_fromSpecStalk f'
  have hflat : Flat (j ≫ k) := by
    rw [hj]
    exact Scheme.flat_fromSpecStalk X' z
  have hjflat : Flat j :=
    MorphismProperty.of_postcomp (W := @Flat)
      (W' := MorphismProperty.monomorphisms Scheme) j k (inferInstance : Mono k) hflat
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hjflat)


/-- Simultaneous ring coordinates for the original and tensor comparison maps.
No invertibility of a comparison is asserted.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation using Tag 0BYJ.
Proof: take existing coordinates e for the identity map on the pullback of E.
Set U to the stalk of e.P, Q to the stalk of c.P, N to the stalk of c.N,
and t to tensorStalkIso(c.P) followed by the stalk of c.t. The stalk K-flat
criterion proves both acyclicity assertions. Construct the local-spectrum map
from Spec(A tensor_R B) to X' using the given cartesian square. It is a
preimmersion, and its composite with Spec C is the canonical local-spectrum
map of X'. Flatness of that composite, cancellation along a monomorphism,
and the affine flatness criterion prove C flat over A tensor_R B.
Use cohomologyModel(c.P) for m and the canonical model for U tensor Q for mU.
The first square uses identity vertical isomorphisms and homologyMap_comp.
The tensor square is the remaining fixed-map obligation
 tensorStalkComparison_fixedMap_square, applied to e.P, e.e and e.isKFlat.
No invertibility of a horizontal comparison is asserted.
(blueprint: lem-pc-tensor-stalk-comparison-squares). -/
theorem exists_tensorStalkComparison_squares
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (E K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hτ : IsCanonicalPullbackTensorComparison g' τ)
    (c : SingleComplexBaseChange.Coordinates g' K.obj K'.obj φ)
    (d : SingleComplexBaseChange.Coordinates g' (E.obj ⊗ K.obj)
      (((derivedPullback g').obj E.obj) ⊗ K'.obj)
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ))) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let G := ModuleCat.extendScalars.{u, u, u} (algebraMap (TensorProduct R A B) C)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    Module.Flat (TensorProduct R A B) C ∧
    ∃ (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : CochainComplex (ModuleCat.{u} C) ℤ)
      (_ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
      (_ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
      (t : F.obj Q ⟶ N)
      (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : ModuleCat.BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C),
      ∀ i : ℤ,
      ∃ (a : G.obj (m.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z c.P).cohomology i))
        (b : N.homology i ≅ (S.obj c.N).homology i)
        (aU : G.obj (mU.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P).cohomology i))
        (bU : (F.obj U ⊗ N).homology i ≅ (S.obj d.N).homology i),
        a.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq c z i =
          m.localizedComparison i ≫ HomologicalComplex.homologyMap t i ≫ b.hom ∧
        aU.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq d z i =
          mU.localizedComparison i ≫ HomologicalComplex.homologyMap
            ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i ≫ bU.hom := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  obtain ⟨e⟩ := SingleComplexBaseChange.nonempty_coordinates g' E.obj
    ((derivedPullback g').obj E.obj) (𝟙 _)
  let U := SingleComplexBaseChange.stalkComplex g' z e.P
  let Q := SingleComplexBaseChange.stalkComplex g' z c.P
  let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex (.up ℤ)
  let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z c.P).hom ≫ S.map c.t
  let m := SingleComplexBaseChange.cohomologyModel f f' g g' sq z c.P
  let mU := ModuleCat.baseDerivedTensorCohomologyModel
    (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
    (SingleComplexBaseChange.B f' z) (U ⊗ Q) (SingleComplexBaseChange.C z)
  refine ⟨stalkTensor_flat f f' g g' sq z, U, Q, S.obj c.N, ?_, ?_, t, m, mU, ?_⟩
  · exact (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace e.P).mp e.isKFlat (g' z)
  · exact (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace c.P).mp c.isKFlat (g' z)
  · intro i
    obtain ⟨aU, bU, hU⟩ := tensorStalkComparison_fixedMap_square f f' g g' sq
      E K K' φ τ hτ c d e.P e.e e.isKFlat z i
    refine ⟨Iso.refl _, Iso.refl _, aU, bU, ?_, hU⟩
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      SingleComplexBaseChange.stalkComparison, t, m, S, HomologicalComplex.homologyMap_comp]


end AlgebraicGeometry
