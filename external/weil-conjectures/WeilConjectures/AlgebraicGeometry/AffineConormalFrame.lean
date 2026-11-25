/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Sheafifying an affine conormal basis

Source: Stacks Project, Morphisms, Tag 01R3, and Modules, Tag 01C6.
(blueprint: lem-sc-affine-conormal-frame). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

-- Local coordinate germs, following the proved stalk calculation of
-- WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank (group S3).
variable {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)

/-- Coordinate germs on neighbourhoods intersected with the trivializing open. -/
private noncomputable def coordinateCocone
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (((X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩).hom.toAddMonoidHom).comp
          (((π.val.app (op (Over.mk
            (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom.toAddMonoidHom).comp
            (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op).hom))
      naturality := by
        intro V W f
        ext m
        let a : W.unop.1 ⊓ U ⟶ V.unop.1 ⊓ U := homOfLE (inf_le_inf f.unop.le le_rfl)
        let a' : Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U) ⟶
            Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U) := Over.homMk a
        have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op)
          (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m)
        change X.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
          ((π.val.app (op (Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U)))).hom
            (M.presheaf.map (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op
              (M.presheaf.map (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op m))) =
          X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩
            ((π.val.app (op (Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom
              (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m))
        rw [← M.presheaf.map_comp_apply]
        have hw : (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op ≫
            (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op =
            (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op ≫ a.op :=
          Subsingleton.elim _ _
        rw [hw, M.presheaf.map_comp_apply]
        rw [← X.presheaf.germ_res_apply a x ⟨W.unop.2, hx⟩]
        congr 1 }

/-- The additive map on stalks determined by local coordinate germs. -/
private noncomputable def coordinateAdd
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (coordinateCocone M x U hx π)).hom

/-- The coordinate cocone computes its stalk map on a representative germ. -/
private lemma coordinateAdd_germ
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(M, V)) (_h : True) :
    coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩
        ((π.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
          (M.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)) := by
  change (colimit.ι _ (op (⟨V, hxV⟩ : OpenNhds x)) ≫
    colimit.desc _ (coordinateCocone M x U hx π)) m = _
  rw [colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate germs respect the action of the structure-ring stalk. -/
private noncomputable def coordinateLinear
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  stalkLinearMapMk (coordinateAdd M x U hx π) fun V hxV r m ↦ by
    rw [coordinateAdd_germ (_h := trivial), coordinateAdd_germ (_h := trivial),
      Scheme.Modules.map_smul]
    rw [(π.val.app _).hom.map_smul]
    change X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (_ * _) = _
    rw [map_mul, X.presheaf.germ_res_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Within the trivializing open, coordinates can be computed without intersecting. -/
private lemma coordinateLinear_germ_of_le
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) (m : Γ(M, V)) (_h : True) :
    coordinateLinear M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ V x hxV
        ((π.val.app (op (Over.mk (homOfLE hVU)))).hom m) := by
  change coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) = _
  rw [coordinateAdd_germ (_h := trivial)]
  let a : V ⊓ U ⟶ V := homOfLE inf_le_left
  let a' : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶
      Over.mk (homOfLE hVU : V ⟶ U) := Over.homMk a
  have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op) m
  have he : (π.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
      (M.presheaf.map a.op m) =
      X.presheaf.map a.op ((π.val.app (op (Over.mk (homOfLE hVU)))).hom m) :=
    hπ
  rw [he, X.presheaf.germ_res_apply]

/-- A coordinate projection in the chosen local trivialization. -/
private noncomputable def localProjection {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.hom ≫ SheafOfModules.freeπ j

/-- A coordinate inclusion in the chosen local trivialization. -/
private noncomputable def localInclusion {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  SheafOfModules.ιFree j ≫ e.inv

/-- The germ of a local coordinate vector. -/
private noncomputable def localBasisGerm {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) : M.presheaf.stalk x :=
  M.presheaf.germ U x hx
    ((localInclusion M U e j).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate vectors give the same germ after restriction. -/
private lemma localBasisGerm_eq {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I)
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) (_h : True) :
    localBasisGerm M x U hx e j = M.presheaf.germ V x hxV
      ((localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU))) (1 : Γ(X, V))) := by
  let a' : Over.mk (homOfLE hVU : V ⟶ U) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU)
  have he := ConcreteCategory.congr_hom
    ((localInclusion M U e j).val.naturality a'.op) (1 : Γ(X, U))
  change localBasisGerm M x U hx e j = _
  unfold localBasisGerm
  rw [← M.presheaf.germ_res_apply (homOfLE hVU) x hxV]
  congr 1
  change (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
      (X.presheaf.map (homOfLE hVU).op (1 : Γ(X, U))) =
    M.presheaf.map (homOfLE hVU).op
      ((localInclusion M U e j).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at he
  rw [map_one] at he
  exact he.symm

/-- The sum of the coordinate projection-inclusion composites is the identity. -/
private lemma local_sum {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (_h : True) :
    ∑ j, localProjection M U e j ≫ localInclusion M U e j = 𝟙 (M.over U) := by
  simp only [localProjection, localInclusion, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, SheafOfModules.sum_freeπ_ιFree,
    Category.id_comp, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk coordinate vectors have Kronecker-delta coordinates. -/
private lemma coordinate_basis {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j k : I) (_h : True) :
    coordinateLinear M x U hx (localProjection M U e j)
      (localBasisGerm M x U hx e k) = if k = j then 1 else 0 := by
  unfold localBasisGerm
  rw [coordinateLinear_germ_of_le M x U hx _ U hx le_rfl (_h := trivial)]
  have hp : localInclusion M U e k ≫ localProjection M U e j =
      if k = j then 𝟙 _ else 0 := by
    simp only [localInclusion, localProjection, Category.assoc, Iso.inv_hom_id_assoc,
      SheafOfModules.ιFree_freeπ]
  have he := congrArg (fun g ↦
    (g.val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) hp
  change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
    _ at he
  change X.presheaf.germ U x hx
    ((localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))) = _
  split_ifs at he ⊢ with h
  · change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (1 : Γ(X, U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_one _)
  · change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (0 : Γ(X, U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- Every germ is the sum of its coordinates times the local basis germs. -/
private lemma sum_coordinate_basis {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (m : M.presheaf.stalk x) (_h : True) :
    ∑ j, coordinateLinear M x U hx (localProjection M U e j) m •
      localBasisGerm M x U hx e j = m := by
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
  simp_rw [coordinateLinear_germ_of_le M x U hx _ V hxV hVU (_h := trivial),
    localBasisGerm_eq M x U hx e _ V hxV hVU (_h := trivial), ← Scheme.Modules.germ_smul]
  rw [← map_sum]
  congr 1
  have he := congrArg (fun g ↦
    (g.val.app (op (Over.mk (homOfLE hVU)))).hom m) (local_sum M U e trivial)
  rw [SheafOfModules.sum_val_app_apply] at he
  change ∑ j, (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
      ((localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m) = m at he
  calc
    _ = ∑ j, (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
        ((localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← ((localInclusion M U e j).val.app _).hom.map_smul]
      congr 1
      exact mul_one (show Γ(X, V) from
        (localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m)
    _ = m := he

/-- A finite local trivialization induces an explicit linear equivalence on stalks. -/
private noncomputable def localStalkEquiv {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (I → X.presheaf.stalk x) :=
  LinearEquiv.ofBijective (LinearMap.pi fun j ↦
    coordinateLinear M x U hx (localProjection M U e j)) (by
    constructor
    · intro m n h
      rw [← sum_coordinate_basis M x U hx e m trivial, ← sum_coordinate_basis M x U hx e n trivial]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun a ↦ a • localBasisGerm M x U hx e j) (congrFun h j)
    · intro c
      refine ⟨∑ j, c j • localBasisGerm M x U hx e j, ?_⟩
      ext k
      change coordinateLinear M x U hx (localProjection M U e k) _ = c k
      rw [map_sum]
      simp_rw [LinearMap.map_smul, coordinate_basis M x U hx e _ _ trivial]
      simp)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A basis of an affine conormal module gives a frame of the conormal sheaf,
and its cardinality computes stalk finrank at points of that affine chart.
Source: Stacks Project, Morphisms, Tag 01R3 (2), and Modules, Tag 01C6 (3).
(blueprint: lem-sc-affine-conormal-frame).

Proof: Put A = O_Y(U), I = i.ker.ideal U and V = i^{-1}(U). A closed immersion
has affine inverse images and a surjective section map A -> O_Z(V) with kernel I.
Thus B = A/I identifies with O_Z(V). By affine_conormal_sections the conormal C
is quasi-coherent and its sections on V identify with I/I^2. The A-linear equivalence
in that lemma is B-linear: both modules are annihilated by I, and one can lift every
scalar of B to A. Transport the supplied basis b along this equivalence and the
quotient-ring identification to a basis of C(V) over O_Z(V). The equivalence between
quasi-coherent sheaves on the affine V and modules sends its coordinate isomorphism
to C|_V = O_V^m. Transport this isomorphism to the over-V site and reindex the basis
along ULift. This gives the first assertion. Coordinate projections and inclusions
commute with restriction on all subopens of V. At any z in V their germs give
mutually inverse O_{Z,z}-linear maps between C_z and the m-fold product of O_{Z,z}:
take germs of the finite coordinate-sum identity and the projection-inclusion
identities. The scheme stalk ring is nontrivial, so the coordinate basis computes
finrank as m. For m = 0 these are empty sums and zero modules. If V is empty,
the stalk assertion is vacuous and its sheaf category has only the zero object,
so the frame still exists. The lemma uses no regularity or Noetherian hypothesis. -/
theorem affine_conormal_frame {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.affineOpens) (m : ℕ)
    (b : Module.Basis (Fin m) (Γ(Y, U.1) ⧸ i.ker.ideal U) (i.ker.ideal U).Cotangent) :
    Nonempty ((((Scheme.Modules.tensorPullback i).obj i.ker.toModules).over
        (i ⁻¹ᵁ U.1)) ≅ SheafOfModules.free (ULift.{u} (Fin m))) ∧
      ∀ z : Z, i z ∈ U.1 →
        Module.finrank (Z.presheaf.stalk z)
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) = m := by
  classical
  let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  have hq := (Scheme.Modules.affine_conormal_sections.{u, u} i).1
  obtain ⟨e, _⟩ := (Scheme.Modules.affine_conormal_sections.{u, u} i).2 U Γ(Y, U.1)
    (RingEquiv.refl _) (i.ker.ideal U) (by simp)
  let q := (Ideal.quotEquivOfEq (i.ker_apply U)).trans
    ((i.app U.1).hom.quotientKerEquivOfSurjective (i.app_surjective U.1 U.2))
  have hV : IsAffineOpen (i ⁻¹ᵁ U.1) := U.2.preimage i
  have hqmk (a : Γ(Y, U.1)) :
      q (Ideal.Quotient.mk (i.ker.ideal U) a) = i.app U.1 a := by
    simp [q]
  let Eadd : (Fin m →₀ Γ(Z, i ⁻¹ᵁ U.1)) ≃+ Γ(C, i ⁻¹ᵁ U.1) :=
    (Finsupp.mapRange.addEquiv q.symm.toAddEquiv).trans
      (b.repr.symm.toAddEquiv.trans e.toAddEquiv)
  let E : (Fin m →₀ Γ(Z, i ⁻¹ᵁ U.1)) ≃ₗ[Γ(Z, i ⁻¹ᵁ U.1)] Γ(C, i ⁻¹ᵁ U.1) :=
    { Eadd with
      map_smul' := by
        intro c v
        obtain ⟨a, rfl⟩ := i.app_surjective U.1 U.2 c
        have hqa : q.symm (i.app U.1 a) = Ideal.Quotient.mk (i.ker.ideal U) a :=
          q.symm_apply_eq.mpr (hqmk a).symm
        have hmap : Finsupp.mapRange q.symm q.symm.map_zero ((i.app U.1 a) • v) =
            (Ideal.Quotient.mk (i.ker.ideal U) a) •
              Finsupp.mapRange q.symm q.symm.map_zero v := by
          ext j
          simp [hqa]
        change e (b.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero
          ((i.app U.1 a) • v))) = (i.app U.1 a) •
            (show Γ(C, i ⁻¹ᵁ U.1) from
              e (b.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v)))
        rw [hmap, b.repr.symm.map_smul]
        change e (a • b.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v)) =
          a • e (b.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v))
        exact e.map_smul a _ }
  let N := C.restrict hV.fromSpec
  let EN := (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv C hV).trans E.symm ≪≫ₗ
    Finsupp.domLCongr Equiv.ulift.symm
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let eN : N ≅ SheafOfModules.free (ULift.{u} (Fin m)) :=
    (asIso N.fromTildeΓ).symm ≪≫
      (tilde.functor Γ(Z, i ⁻¹ᵁ U.1)).mapIso EN.toModuleIso ≪≫
      tildeFinsupp (ULift.{u} (Fin m))
  let eV : C.restrict (i ⁻¹ᵁ U.1).ι ≅ SheafOfModules.free (ULift.{u} (Fin m)) :=
    Scheme.Modules.restrictCompIso C hV.fromSpec hV.isoSpec.hom (i ⁻¹ᵁ U.1).ι
      hV.isoSpec_hom_fromSpec ≪≫
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso eN ≪≫
      Scheme.Modules.restrictFreeIso hV.isoSpec.hom (ULift.{u} (Fin m))
  let eOver := (Scheme.Modules.overIsoFreeEquiv C (i ⁻¹ᵁ U.1)
    (ULift.{u} (Fin m))).symm eV
  refine ⟨⟨eOver⟩, fun z hz ↦ ?_⟩
  let EStalk := Scheme.Modules.localStalkEquiv C z (i ⁻¹ᵁ U.1) hz eOver
  change Module.finrank (Z.presheaf.stalk z) (C.presheaf.stalk z) = m
  rw [EStalk.finrank_eq]
  simp

end AlgebraicGeometry
