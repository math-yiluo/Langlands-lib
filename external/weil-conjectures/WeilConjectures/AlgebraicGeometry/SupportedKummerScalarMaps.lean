/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-! Normalized constant coefficient maps for supported scalar extension.
Source: Stacks Project, Tags 03QP and 06YY
(auxiliary; not a blueprint node). -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The constant coefficient map adjoint to the linear map sending one to the target unit.
Source: the constant-sheaf adjunction (auxiliary; not a blueprint node). -/
noncomputable def normalizedConstantMap {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (D : Scheme.{u}) :
    ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D) :=
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R) hT).homEquiv _ _).symm
    (ModuleCat.ofHom
      (Y := ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        (ordinaryFiniteConstant S D)).obj.obj
          (op (Scheme.Etale.mk (𝟙 D))))
      (LinearMap.toSpanSingleton R _
        ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} S) hT).unit.app
            (ModuleCat.of S S) (1 : S))))

private theorem normalizedConstantMap_top {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (D : Scheme.{u}) (r : R) :
    (normalizedConstantMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app (op (Scheme.Etale.mk (𝟙 D))) r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app (op (Scheme.Etale.mk (𝟙 D))) (φ r) := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let adj := constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R) hT
  have h := (adj.homEquiv (ModuleCat.of R R)
    ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
      (ordinaryFiniteConstant S D))).apply_symm_apply
    (ModuleCat.ofHom
      (Y := ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        (ordinaryFiniteConstant S D)).obj.obj
          (op (Scheme.Etale.mk (𝟙 D))))
      (LinearMap.toSpanSingleton R _
        ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} S) hT).unit.app
            (ModuleCat.of S S) (1 : S))))
  have h' := congrArg (fun f ↦ f r) h
  change (normalizedConstantMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
    ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).app (op (Scheme.Etale.mk (𝟙 D))) r) = _ at h'
  rw [h']
  change (φ r) • ((constantSheafAdj D.smallEtaleTopology
      (ModuleCat.{u + 1} S) (MorphismProperty.Over.mkIdTerminal _ _)).unit.app
      (ModuleCat.of S S) (1 : S)) = _
  rw [← map_smul]
  simp only [smul_eq_mul, mul_one]
  rfl

private theorem normalizedConstantMap_apply {R S : Type (u + 1)} [CommRing R]
    [CommRing S] (φ : R →+* S) (D : Scheme.{u}) (U : D.Etaleᵒᵖ) (r : R) :
    (normalizedConstantMap φ D).hom.app U
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r) := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let f := (hT.from U.unop).op
  let a := toSheafify D.smallEtaleTopology
    ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))
  let b := toSheafify D.smallEtaleTopology
    ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of S S))
  have hs := congrArg (fun q ↦ q r) (a.naturality f)
  have ht := congrArg (fun q ↦ q (φ r)) (b.naturality f)
  have hs2 : ((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).map f) (a.app (op (Scheme.Etale.mk (𝟙 D))) r) = (a.app U) r := by
    simpa [a, ModuleCat.comp_apply] using hs.symm
  have ht2 : ((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of S S))).map f) (b.app (op (Scheme.Etale.mk (𝟙 D))) (φ r)) =
      (b.app U) (φ r) := by
    simpa [b, ModuleCat.comp_apply] using ht.symm
  have hn := congrArg (fun q ↦ q (a.app (op (Scheme.Etale.mk (𝟙 D))) r))
    ((normalizedConstantMap φ D).hom.naturality f)
  change (normalizedConstantMap φ D).hom.app U
      (((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).map f) (a.app
          (op (Scheme.Etale.mk (𝟙 D))) r)) =
    ((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of S S))).map f)
      ((normalizedConstantMap φ D).hom.app
        (op (Scheme.Etale.mk (𝟙 D))) (a.app
          (op (Scheme.Etale.mk (𝟙 D))) r)) at hn
  change (normalizedConstantMap φ D).hom.app U (a.app U r) = (b.app U) (φ r)
  rw [← hs2, ← ht2]
  rw [normalizedConstantMap_top] at hn
  exact hn

/-- Construct the normalized coefficient maps by the constant-sheaf adjunction and record their
component formulas. Proof: use the adjunction hom-equivalence to define each map from the
terminal generator, then use naturality of the sheafification unit to transport the terminal
formula along every étale object. Source: Stacks Project, Tags 03QP and 06YY
(auxiliary; not a blueprint node). -/
theorem exists_supported_kummer_scalar_maps
    (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (φ : ULift.{u + 1} (ZMod N) →+* A)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          (ordinaryFiniteConstant A D))
      (ηT : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
          (ordinaryFiniteConstant A T)),
      (∀ (U : D.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (φ r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (φ r)) := by
  refine ⟨normalizedConstantMap φ D, normalizedConstantMap φ T, ?_⟩
  constructor
  · intro U r
    exact normalizedConstantMap_apply φ D U r
  · intro U r
    exact normalizedConstantMap_apply φ T U r
set_option backward.isDefEq.respectTransparency false in
private theorem supportedConstantUnit_generators (R : Type (u + 1)) [CommRing R]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R)) ≫
      (supportedConstantUnit R i).hom =
    Functor.whiskerLeft i.Etale.op
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))) := by
  simp only [supportedConstantUnit, Scheme.upperStarConstantSheafIso,
    Adjunction.homEquiv_unit]
  simp only [Functor.comp_obj, Adjunction.leftAdjointUniq, Iso.app_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, conjugateEquiv_symm_apply_app,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.comp_map, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.id_obj, Functor.whiskerRight_app, Adjunction.comp_counit_app,
    constantSheafAdj_counit_app, Functor.map_comp, Category.assoc, Category.id_comp,
    Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components,
    Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
    sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift]
  simp only [constantSheaf, Functor.comp_map]
  rw [← toSheafify_naturality_assoc, ← toSheafify_naturality_assoc,
    toSheafify_sheafifyLift]
  ext U
  simp only [Functor.const_obj_obj, Functor.comp_obj, constantSheafAdj, constantPresheafAdj,
    evaluation_obj_obj, Functor.id_obj, op_unop, Adjunction.comp_unit_app,
    ObjectProperty.ι_obj, Functor.constCompEvaluationObj_hom_app,
    sheafificationAdjunction_unit_app, evaluation_obj_map, Category.id_comp,
    lowerStarCompSheafSectionsTerminalIso, Functor.op_obj, Functor.mapIso_symm,
    NatIso.ofComponents_inv_app, Functor.flip_obj_obj, Iso.symm_inv, Functor.mapIso_hom,
    Iso.op_hom, PreservesTerminal.iso_hom, NatTrans.comp_app, Functor.const_map_app,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, Functor.whiskerLeft_app]
  let k := i.Etale.map (terminalIsTerminal.from U.unop) ≫ terminalComparison i.Etale
  have h := congrArg (fun q ↦ q (1 : R))
    ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).naturality k.op)
  change ((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).map ((i.Etale.map (terminalIsTerminal.from U.unop)).op))
    (((sheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).map (terminalComparison i.Etale).op)
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app (op (⊤_ D.Etale)) (1 : R))) = _
  simp only [k, op_comp, Functor.map_comp, ModuleCat.comp_apply,
    Functor.const_obj_map] at h
  exact h.symm
private theorem supportedConstantUnit_apply (R : Type (u + 1)) [CommRing R]
    {D T : Scheme.{u}} (i : D ⟶ T) (U : T.Etaleᵒᵖ) (r : R) :
    (supportedConstantUnit R i).hom.app U
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app (i.Etale.op.obj U) r := by
  exact congrArg (fun f ↦ f r) (NatTrans.congr_app (supportedConstantUnit_generators R i) U)

/-- Normalized coefficient maps commute with the adjunction unit on constants.
Proof: precompose with the constant-presheaf sheafification unit. The constant-pullback
comparison is characterized by the constants/global-sections adjunction; its unit sends
constant generators to the same generators on the pullback object. Both composites
therefore send r to φ(r). Source: Stacks Project, Tag 03Q1
(auxiliary; not a blueprint node). -/
theorem supported_kummer_scalar_units_commute {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T)
    (ηD : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (ηT : ordinaryFiniteConstant R T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T))
    (hD : ∀ (U : D.Etaleᵒᵖ) (r : R), ηD.hom.app U
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r))
    (hT : ∀ (U : T.Etaleᵒᵖ) (r : R), ηT.hom.app U
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) :
    ηT ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map (supportedConstantUnit S i) =
      supportedConstantUnit R i ≫ (lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
        (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant S D) := by
  let hterm : IsTerminal (Scheme.Etale.mk (𝟙 T)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  apply ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} R) hterm).homEquiv
    (ModuleCat.of R R) _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (supportedConstantUnit S i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (ηT.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app (op (Scheme.Etale.mk (𝟙 T))) (1 : R))) =
    ηD.hom.app (i.Etale.op.obj (op (Scheme.Etale.mk (𝟙 T))))
      ((supportedConstantUnit R i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app (op (Scheme.Etale.mk (𝟙 T))) (1 : R)))
  rw [hT, supportedConstantUnit_apply, supportedConstantUnit_apply, hD]

end AlgebraicGeometry.Etale
