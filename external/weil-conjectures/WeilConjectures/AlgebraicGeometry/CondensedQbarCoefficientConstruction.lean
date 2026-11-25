/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation

/-!
# Scalar functions and geometric evaluation for bounded condensed coefficients

This coefficient interface is independent of any module or finite presentation.
Source: RefactorInstruction.tex, Section 4, coefficient realization and geometric evaluation
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedQbarCoefficientRealization

section CoefficientUniverse
open Opposite CategoryTheory.MonObj CategoryTheory.MonoidalCategory

variable (E : Type) [NormedField E]
/-- Lift a coefficient field into the scheme universe without changing its topology.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
@[instance_reducible]
noncomputable def liftNormedField : NormedField (ULift.{u} E) :=
  NormedField.induced _ E ULift.ringEquiv.toRingHom ULift.down_injective

/-- The lifted field retains its normed scalar algebra.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
@[instance_reducible]
noncomputable def liftNormedAlgebra (K : Type) [NormedField K] [NormedAlgebra K E] :
    letI := liftNormedField.{u} E
    NormedAlgebra K (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  exact { norm_smul_le := fun c x ↦ norm_smul_le c x.down }

/-- The down map of the lifted coefficient field is continuous.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
lemma liftContinuousDown :
    letI := liftNormedField.{u} E
    Continuous (ULift.down : ULift.{u} E → E) := by
  let := liftNormedField.{u} E
  exact continuous_induced_dom

/-- The up map of the lifted coefficient field is continuous.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
lemma liftContinuousUp :
    letI := liftNormedField.{u} E
    Continuous (ULift.up : E → ULift.{u} E) := by
  let := liftNormedField.{u} E
  exact continuous_induced_rng.mpr continuous_id

/-- Continuous condensed coefficients are invariant under the explicit universe lift.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
noncomputable def liftCondensedRingIso :
    letI := liftNormedField.{u} E
    Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  let F (T : Type u) [TopologicalSpace T] :
      C(T, E) ≃+* C(T, ULift.{u} E) :=
    { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f x), (liftContinuousUp E).comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ (f x).down, (liftContinuousDown E).comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop).toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop).symm.toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    rfl
  · ext S f
    rfl

/-- Continuous scheme coefficients are invariant under the explicit universe lift.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
noncomputable def liftSchemeRingIso (X : AlgebraicGeometry.Scheme.{u}) :
    letI := liftNormedField.{u} E
    AlgebraicGeometry.ProEtale.continuousMapRingSheaf X E ≅
      AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf X (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  let F (T : Type u) [TopologicalSpace T] :
      C(T, E) ≃+* C(T, ULift.{u} E) :=
    { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f x), (liftContinuousUp E).comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ (f x).down, (liftContinuousDown E).comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop.left).toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop.left).symm.toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    rfl
  · ext S f
    rfl

/-- The canonical finite-extension realization, without a noetherian assumption.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def finiteFieldComparisonIso (ℓ : ℕ) [Fact ℓ.Prime]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    Mon.mk (condensedRingObj (Profinite.continuousMapRingObj E) X) ≅
      Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)) := by
  let := liftNormedField.{u} E
  let := liftNormedAlgebra.{u} E ℚ_[ℓ]
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm
  let e₀ := (Module.finBasis ℚ_[ℓ] (ULift.{u} E)).equivFunL.toHomeomorph
  have : TotallyDisconnectedSpace (ULift.{u} E) :=
    e₀.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let e := condensedFieldContinuousMapIso (ULift.{u} E) X
  let L := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftCondensedRingIso E)
  let M := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftSchemeRingIso E X)
  let L' := (upperStarFromPoint X).mapIso L
  have : IsMonHom L.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftCondensedRingIso E).hom
  have : IsMonHom L'.hom := by
    change IsMonHom ((upperStarFromPoint X).map L.hom)
    infer_instance
  have : IsMonHom M.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftSchemeRingIso E X).hom
  let d := Mon.mkIso' L' ≪≫ e ≪≫ (Mon.mkIso' M).symm
  exact d

/-- The finite-extension realization is normalized on profinite test functions.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
lemma finiteFieldComparison_test (ℓ : ℕ) [Fact ℓ.Prime]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    ∀ (S : Profinite.{u}) (f : C(S, E)),
      (((pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
          _ _ (finiteFieldComparisonIso E ℓ X).hom.hom).hom.app (op S)) (ULift.up f) =
        ULift.up (f.comp (profiniteTestProjection X S)) := by
  unfold finiteFieldComparisonIso
  let := liftNormedField.{u} E
  let := liftNormedAlgebra.{u} E ℚ_[ℓ]
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm
  let e₀ := (Module.finBasis ℚ_[ℓ] (ULift.{u} E)).equivFunL.toHomeomorph
  have : TotallyDisconnectedSpace (ULift.{u} E) :=
    e₀.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let e := condensedFieldContinuousMapIso (ULift.{u} E) X
  have he := condensedFieldContinuousMapIso_test (ULift.{u} E) X
  let L := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftCondensedRingIso E)
  let M := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftSchemeRingIso E X)
  let L' := (upperStarFromPoint X).mapIso L
  have : IsMonHom L.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftCondensedRingIso E).hom
  have : IsMonHom L'.hom := by
    change IsMonHom ((upperStarFromPoint X).map L.hom)
    infer_instance
  have : IsMonHom M.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftSchemeRingIso E X).hom
  let d := Mon.mkIso' L' ≪≫ e ≪≫ (Mon.mkIso' M).symm
  intro S f
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  change ((adj.homEquiv _ _
    (((pointUpperStar ⋙ upperStar AddCommGrpCat.{u + 1} (toSpecZ X)).map
      L.hom ≫ e.hom.hom) ≫ M.inv)).hom.app (op S))
      (ULift.up f) = _
  erw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  let f' : C(S, ULift.{u} E) :=
    ⟨fun s ↦ ULift.up (f s), (liftContinuousUp E).comp f.continuous⟩
  have hf := he S f'
  change _ = ULift.up (f'.comp (profiniteTestProjection X S)) at hf
  change ULift.up (⟨fun x ↦
    (((adj.homEquiv _ _ e.hom.hom).hom.app (op S)) (ULift.up f')).down x |>.down,
    _⟩ : C(_, E)) = _
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z ↦ (z.down x).down) hf

section Colimit
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {J : Type w} [Category.{z} J] [IsSifted J]
  {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  [MonObj c.pt] [∀ j, MonObj (F.obj j)]
  [PreservesColimit₂ F F (curriedTensor C)]
include hc in
/-- A sifted-colimit map is multiplicative when each cocone composite is.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
lemma isMonHom_of_colimit {R : C} [MonObj R] (g : c.pt ⟶ R)
    (hι : ∀ j, IsMonHom (show F.obj j ⟶ c.pt from c.ι.app j)) (hg : ∀ j, IsMonHom (c.ι.app j ≫ g)) :
    IsMonHom g := by
  have : Nonempty J := IsSifted.nonempty
  constructor
  · obtain ⟨j⟩ := ‹Nonempty J›
    have := hι j
    have := hg j
    rw [← IsMonHom.one_hom (c.ι.app j), Category.assoc]
    exact IsMonHom.one_hom (c.ι.app j ≫ g)
  · apply (IsColimit.tensor hc hc).hom_ext
    intro j
    have := hι j
    have := hg j
    change (c.ι.app j ⊗ₘ c.ι.app j) ≫ μ[c.pt] ≫ g =
      (c.ι.app j ⊗ₘ c.ι.app j) ≫ (g ⊗ₘ g) ≫ μ[R]
    rw [← IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Colimit

/-- The canonical realizations commute with inclusions of finite extensions.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def fieldDiagramIso (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X ≅
      padicSubfieldSheafFunctor X ℓ ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  let e (E : PadicAlgCl.FiniteIntermediateField ℓ) := finiteFieldComparisonIso E ℓ X
  have he (E : PadicAlgCl.FiniteIntermediateField ℓ) := finiteFieldComparison_test E ℓ X
  let d (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X).obj E ≅
        (padicSubfieldSheafFunctor X ℓ ⋙
          sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj E :=
    (Mon.forget _).mapIso (e E)
  refine NatIso.ofComponents d ?_
  intro E F a
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((pointUpperStar ⋙ upperStar AddCommGrpCat.{u + 1} (toSpecZ X)).map
      (Profinite.padicSubfieldRingObjMap ℓ (leOfHom a)) ≫ (e F).hom.hom) =
    adj.homEquiv _ _ ((e E).hom.hom ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          (padicSubfieldSheafMapOfLE X ℓ (leOfHom a)))
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  ext S f
  cases f with
  | up f =>
    change (((adj.homEquiv _ _ (e F).hom.hom).hom.app S)
      (ULift.up ⟨_, _⟩)) = _
    rw [he F S.unop]
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun z ↦ IntermediateField.inclusion (leOfHom a) (z.down x))
      (he E S.unop f).symm

/-- Each finite-extension comparison preserves the ring operations.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
lemma fieldDiagramIso_isMonHom (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsMonHom (show condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E) from (fieldDiagramIso ℓ X).hom.app E) := by
  unfold fieldDiagramIso
  change IsMonHom (finiteFieldComparisonIso E ℓ X).hom.hom
  infer_instance

noncomputable section
/-- The bounded condensed coefficient ring realizes as the bounded-function sheaf.
Source: RefactorInstruction, Section 4, finite-coefficient comparison and its filtered colimit
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def globalCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) :
    Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
      Mon.mk (padicAlgClSheaf X ℓ) := by
  let d := fieldDiagramIso ℓ X
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (toSpecZ X))).leftAdjoint_preservesColimits
  let h₁ := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone.{u} ℓ)
  let h₂ := (IsColimit.precomposeHomEquiv d (padicAlgClSheafCocone X ℓ)).symm
    (isColimitPadicAlgClSheafCocone X ℓ)
  let e : condensedRingObj (Profinite.padicAlgClRingObj ℓ) X ≅ padicAlgClSheaf X ℓ :=
    h₁.coconePointUniqueUpToIso h₂
  have he (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
        e.hom = d.hom.app E ≫ (padicAlgClSheafCocone X ℓ).ι.app E :=
    h₁.comp_coconePointUniqueUpToIso_hom h₂ E
  have : IsSifted (PadicAlgCl.FiniteIntermediateField ℓ) := IsFiltered.isSifted
  have : IsMonHom e.hom := by
    refine @isMonHom_of_colimit _ _ _ _ _ _ _
      ((upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone.{u} ℓ)) h₁
      (inferInstanceAs (MonObj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
      (fun E ↦ inferInstanceAs
        (MonObj (condensedRingObj (Profinite.continuousMapRingObj E) X)))
      _ _ _ e.hom ?_ ?_
    · intro E
      change IsMonHom ((upperStarFromPoint X).map
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E))
      infer_instance
    · intro E
      change IsMonHom
        ((upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ e.hom)
      rw [he E]
      change IsMonHom ((show condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
              (continuousMapRingSheaf X E) from d.hom.app E) ≫
        padicSubfieldSheafToPadicAlgClSheaf X ℓ E.1)
      have := fieldDiagramIso_isMonHom ℓ X E
      infer_instance
  exact Mon.mkIso' e

end
end CoefficientUniverse

end CondensedQbarCoefficientRealization

namespace CondensedQbarScalarConstruction

variable (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})

/-- The abelian presheaf underlying the bounded-function ring presheaf.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable abbrev boundedP := padicAlgClRingPresheaf Y ℓ ⋙ forget₂ RingCat Ab

/-- Precomposition preserves the finite-subextension bound.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def boundedComp {T T' : Type u} [TopologicalSpace T] [TopologicalSpace T']
    (g : C(T', T)) : PadicAlgCl.finiteIntermediateFieldValued ℓ T →+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ T' :=
  (((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) g).toRingHom.comp
    (PadicAlgCl.finiteIntermediateFieldValued ℓ T).subtype).codRestrict
      (PadicAlgCl.finiteIntermediateFieldValued ℓ T') (by
        rintro a
        obtain ⟨E, hE, ha⟩ := a.property
        exact ⟨E, hE, fun x ↦ ha (g x)⟩))

/-- Bounded continuous functions descend uniquely to the actual component quotient.
The quotient is surjective, so the same finite extension bounds the descended function.
This includes the empty space.
Source: RefactorInstruction, Section 4, coefficient realization on the component quotient
(auxiliary; not a blueprint node). -/
noncomputable def boundedComponentsIso (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Type u) [TopologicalSpace T] :
    PadicAlgCl.finiteIntermediateFieldValued ℓ (ConnectedComponents T) ≃+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ T := by
  let q : C(T, ConnectedComponents T) := ⟨ConnectedComponents.mk,
    ConnectedComponents.continuous_coe⟩
  refine RingEquiv.ofBijective (boundedComp ℓ q) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    ext t
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
    exact congrArg (fun c ↦ c.1 x) h
  · intro a
    let b : C(ConnectedComponents T, PadicAlgCl ℓ) :=
      ⟨a.1.continuous.connectedComponentsLift, a.1.continuous.connectedComponentsLift_continuous⟩
    have hb : b ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ (ConnectedComponents T) := by
      obtain ⟨E, hE, ha⟩ := a.property
      refine ⟨E, hE, ?_⟩
      intro t
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
      exact (Continuous.connectedComponentsLift_apply_coe a.1.continuous x) ▸ ha x
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    ext x
    exact Continuous.connectedComponentsLift_apply_coe a.1.continuous x

/-- Restriction of a bounded function to a small pro-etale object.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def restrictBounded (U : Y.ProEt) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ Y →+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ U.left :=
  boundedComp ℓ (show C(U.left, Y) from U.hom.base.hom)

/-- Multiplication by a restricted bounded function on each presheaf section.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def boundedMul (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    boundedP ℓ Y ⟶ boundedP ℓ Y where
  app U := AddCommGrpCat.ofHom
    { toFun s := ULift.up (s.down * restrictBounded ℓ Y U.unop a)
      map_zero' := by
        change ULift.up (0 * _) = ULift.up (0 : PadicAlgCl.finiteIntermediateFieldValued ℓ _)
        rw [zero_mul]
      map_add' s t := congrArg ULift.up (add_mul _ _ _) }
  naturality U V g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change s.down.1 (g.unop.left x) * a.1 (V.unop.hom x) =
      s.down.1 (g.unop.left x) * a.1 (U.unop.hom (g.unop.left x))
    congr 1
    exact congrArg a.1 (by rw [← MorphismProperty.Over.w g.unop]; rfl)

/-- Multiplication by a bounded function is internally linear.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
lemma boundedMul_linear (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    (MonObj.mul : boundedP ℓ Y ⊗ boundedP ℓ Y ⟶ _) ≫ boundedMul ℓ Y a =
      boundedP ℓ Y ◁ boundedMul ℓ Y a ≫ MonObj.mul := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext
  ext s t : 2
  change ULift.up ((s.down * t.down) * _) = ULift.up (s.down * (t.down * _))
  rw [mul_assoc]

/-- The explicit ring action of bounded functions on the regular presheaf module.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def presheafScalar : PadicAlgCl.finiteIntermediateFieldValued ℓ Y →+*
    End (Mod.regular (boundedP ℓ Y)) where
  toFun a := .of (Mod.homMk (boundedMul ℓ Y a) (boundedMul_linear ℓ Y a))
  map_one' := by
    apply End.ext
    apply Mod.hom_ext
    ext U s
    apply ULift.ext
    change s.down * restrictBounded ℓ Y U.unop 1 = s.down
    rw [map_one, mul_one]
  map_mul' a b := by
    apply End.ext
    apply Mod.hom_ext
    ext U s
    apply ULift.ext
    change s.down * (restrictBounded ℓ Y U.unop (a * b)) =
      (s.down * restrictBounded ℓ Y U.unop b) * restrictBounded ℓ Y U.unop a
    rw [map_mul, mul_assoc, mul_comm (restrictBounded ℓ Y U.unop a)]
  map_zero' := by
    apply End.ext
    apply Mod.hom_ext
    ext U s
    apply ULift.ext
    change s.down * restrictBounded ℓ Y U.unop 0 = 0
    rw [map_zero, mul_zero]
  map_add' a b := by
    apply End.ext
    apply Mod.hom_ext
    ext U s
    apply ULift.ext
    change s.down * restrictBounded ℓ Y U.unop (a + b) =
      s.down * restrictBounded ℓ Y U.unop a + s.down * restrictBounded ℓ Y U.unop b
    rw [map_add, mul_add]

/-- Every regular-module endomorphism of the bounded-function presheaf is multiplication
by a bounded function. Evaluate at one on the terminal object; naturality transports
this section and module linearity determines the endomorphism at every object.
Source: RefactorInstruction, Section 4, regular-module scalar realization
(auxiliary; not a blueprint node). -/
lemma presheafScalar_surjective (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    Function.Surjective (presheafScalar ℓ Y) := by
  intro f
  let T := Scheme.ProEt.mk (𝟙 Y)
  let a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y :=
    ((f.asHom.hom.app (op T)) (ULift.up 1)).down
  refine ⟨a, ?_⟩
  apply End.ext
  apply Mod.hom_ext
  ext U s
  let t : U.unop ⟶ T := MorphismProperty.Over.homMk U.unop.hom
  have hn := ConcreteCategory.congr_hom (f.asHom.hom.naturality t.op) (ULift.up 1)
  have hf := IsModHom.smul_hom (A := boundedP ℓ Y) (f := f.asHom.hom)
  have h := ConcreteCategory.congr_hom (congr_app hf U) (s ⊗ₜ[ℤ] ULift.up 1)
  change (f.asHom.hom.app U) (ULift.up (s.down * 1)) =
    ULift.up (s.down * ((f.asHom.hom.app U) (ULift.up 1)).down) at h
  rw [mul_one] at h
  change ((f.asHom.hom.app U) (ULift.up 1)) =
    (boundedP ℓ Y).map t.op ((f.asHom.hom.app (op T)) (ULift.up 1)) at hn
  rw [hn] at h
  exact h.symm


/-- Monoidal sheafification carries the regular module to the regular module.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def sheafificationRegularIso :
    ((presheafToSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapMod (boundedP ℓ Y)).obj
      (Mod.regular (boundedP ℓ Y)) ≅ Mod.regular (padicAlgClSheaf Y ℓ) :=
  Mod.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp])

/-- The bounded-function action after monoidal abelian sheafification.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable def sheafScalar : PadicAlgCl.finiteIntermediateFieldValued ℓ Y →+*
    End (Mod.regular (padicAlgClSheaf Y ℓ)) where
  toFun a := .of ((sheafificationRegularIso ℓ Y).inv ≫
    ((presheafToSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapMod (boundedP ℓ Y)).map
      (presheafScalar ℓ Y a).asHom ≫ (sheafificationRegularIso ℓ Y).hom)
  map_one' := by
    apply End.ext
    apply Mod.hom_ext
    change (presheafToSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).map
      (presheafScalar ℓ Y 1).asHom.hom = 𝟙 _
    rw [map_one]
    exact CategoryTheory.Functor.map_id _ _
  map_mul' a b := by
    apply End.ext
    simp only [map_mul, End.mul_asHom, Functor.map_comp]
    simp [Category.assoc]
  map_zero' := by
    apply End.ext
    rw [map_zero, End.zero_asHom, Functor.map_zero]
    simp
  map_add' a b := by
    apply End.ext
    apply Mod.hom_ext
    change (presheafToSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).map
      (presheafScalar ℓ Y (a + b)).asHom.hom = _
    rw [map_add]
    exact Functor.map_add _

/-- Transport the explicitly constructed bounded-function action through a ring-sheaf
realization. Every operation is constructed from multiplication and functoriality.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def transportedScalar
    (e : Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) ≅
      Mon.mk (padicAlgClSheaf Y ℓ)) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ Y →+*
      End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv e.inv.hom)
  let d := Mod.regularIsoOfIsIso e.inv.hom
  refine
    { toFun := fun a ↦ .of (d.inv ≫ F.map (sheafScalar ℓ Y a).asHom ≫ d.hom)
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
  · apply End.ext
    rw [map_one, End.one_asHom]
    change _ ≫ 𝟙 _ ≫ _ = _
    simp
  · intro a b
    apply End.ext
    simp only [map_mul, End.mul_asHom, CategoryTheory.Functor.map_comp]
    simp [Category.assoc]
  · apply End.ext
    rw [map_zero, End.zero_asHom, CategoryTheory.Functor.map_zero]
    simp
  · intro a b
    apply End.ext
    rw [map_add, End.add_asHom, CategoryTheory.Functor.map_add]
    simp only [End.add_asHom, Preadditive.comp_add, Preadditive.add_comp]

end CondensedQbarScalarConstruction

namespace CondensedQbarCoefficientRealization

/-- The global bounded realization agrees with every finite-extension inclusion.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
lemma globalCoefficientIso_fac (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
        (globalCoefficientIso ℓ X).hom.hom =
      (fieldDiagramIso ℓ X).hom.app E ≫
        (padicAlgClSheafCocone X ℓ).ι.app E := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (toSpecZ X))).leftAdjoint_preservesColimits
  unfold globalCoefficientIso
  exact (isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone.{u} ℓ)).comp_coconePointUniqueUpToIso_hom
      ((IsColimit.precomposeHomEquiv (fieldDiagramIso ℓ X)
        (padicAlgClSheafCocone X ℓ)).symm (isColimitPadicAlgClSheafCocone X ℓ)) E
/-- The bounded coefficient realization is normalized on every profinite test function.
Choose the finite extension bounding the function and use the finite comparison's
normalization; the sheafification unit-counit identity identifies the final inclusion.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
lemma globalCoefficientIso_test (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (S : Profinite.{u}) (a : PadicAlgCl.finiteIntermediateFieldValued ℓ S) :
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).homEquiv _ _
        (globalCoefficientIso ℓ X).hom.hom).hom.app (op S)) (ULift.up a) =
    (toSheafify (Scheme.ProEt.topology X)
      (CondensedQbarScalarConstruction.boundedP ℓ X)).app
        (op ((profiniteToProEtOf X).obj S))
          (ULift.up (CondensedQbarScalarConstruction.boundedComp ℓ
            (profiniteTestProjection X S) a)) := by
  obtain ⟨E, hE, ha⟩ := a.property
  let E' : PadicAlgCl.FiniteIntermediateField ℓ := ⟨E, hE⟩
  let b : C(S, E') := ⟨fun x ↦ ⟨a.1 x, ha x⟩, a.1.continuous.subtype_mk _⟩
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have hf := congrArg (adj.homEquiv _ _) (globalCoefficientIso_fac ℓ X E')
  change adj.homEquiv _ _
    ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).map
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E') ≫
        (globalCoefficientIso ℓ X).hom.hom) = _ at hf
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] at hf
  have h := congrArg (fun φ ↦ (φ.hom.app (op S)) (ULift.up b)) hf
  have ht := finiteFieldComparison_test E' ℓ X S b
  change (((adj.homEquiv _ _ (globalCoefficientIso ℓ X).hom.hom).hom.app (op S))
    (ULift.up a)) = _ at h
  rw [h]
  change ((padicSubfieldSheafToPadicAlgClSheaf X ℓ E'.1).hom.app
    (op ((profiniteToProEtOf X).obj S)))
      (((adj.homEquiv _ _ ((fieldDiagramIso ℓ X).hom.app E')).hom.app (op S))
        (ULift.up b)) = _
  have hd : (fieldDiagramIso ℓ X).hom.app E' = (finiteFieldComparisonIso E' ℓ X).hom.hom := by
    unfold fieldDiagramIso
    rfl
  rw [hd]
  erw [ht]
  let J := Scheme.ProEt.topology X
  let R := padicSubfieldSheaf X ℓ E'.1
  let RAb := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hu : (Sheaf.sheafifyRingPresheafIso J R).inv.hom = toSheafify J RAb.obj := by
    change (sheafToPresheaf J Ab.{u + 1}).map
      (inv ((sheafificationAdjunction J Ab.{u + 1}).counit.app RAb)) = _
    rw [Functor.map_inv]
    exact (sheafificationAdjunction J Ab.{u + 1}).inv_counit_map
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
    Sheaf.sheafComposeToSheafify
  change (((Sheaf.sheafifyRingPresheafIso J R).inv.hom ≫ _).app _) _ = _
  rw [hu]
  erw [← toSheafify_naturality]
  rfl

end CondensedQbarCoefficientRealization

/-- The canonical scalar action is obtained from the explicit bounded-function
multiplication and the filtered-colimit coefficient realization.
Source: RefactorInstruction, Section 4, coefficient realization
(auxiliary; not a blueprint node). -/
noncomputable abbrev condensedQbarScalar (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ Y →+*
      End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :=
  CondensedQbarScalarConstruction.transportedScalar ℓ Y
    (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y)

/-- The regular module is preserved by normalized condensed-coefficient pullback.
Source: the coefficient comparison in RefactorInstruction, Section 4
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def condensedQbarRegularPullbackIso
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ≅
        Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) :=
  (Mod.extendScalarsIsoComapInv (condensedPullbackHom
    (Profinite.padicAlgClRingObj ℓ) f)).app _ ≪≫
      Mod.regularIsoOfIsIso (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f)

namespace CondensedQbarGeometricEvaluation
open scoped CategoryTheory.Obj
variable (K : Type u) [Field K] [IsAlgClosed K]
/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
lemma cover_id (S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of K)) _) : S (𝟙 _) := by
  obtain ⟨U, f, s, hf, hs⟩ :=
    (geometric_field_proetale_evaluation_exact K).1 S.arrows (by
      simpa only [Sieve.generate_sieve] using hS)
  simpa only [hs] using S.downward_closed hf s

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
lemma unit_iso (P : (Spec (.of K)).ProEtᵒᵖ ⥤ Ab.{u + 1}) :
    IsIso ((toSheafify (Scheme.ProEt.topology (Spec (.of K))) P).app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
  let J := Scheme.ProEt.topology (Spec (.of K))
  let η := toSheafify J P
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    have h := cover_id K _ (Presheaf.equalizerSieve_mem J η x y hxy)
    change P.map (𝟙 _) x = P.map (𝟙 _) y at h
    simpa only [P.map_id, ConcreteCategory.id_apply] using h
  · intro t
    have h := cover_id K _ (Presheaf.imageSieve_mem J η t)
    obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using ha

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable instance evaluationMonoidal (U : (Spec (.of K)).ProEtᵒᵖ) :
    ((evaluation _ Ab.{u + 1}).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def boundedEval (ℓ : ℕ) [Fact ℓ.Prime] :
    PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K)) →+* PadicAlgCl ℓ where
  toFun a := a.1 default
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsAlgClosed K] in
/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
lemma boundedEval_bijective (ℓ : ℕ) [Fact ℓ.Prime] : Function.Bijective (boundedEval K ℓ) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    obtain rfl : x = default := Subsingleton.elim _ _
    exact h
  · intro a
    have ha : _root_.IsIntegral ℚ_[ℓ] a := Algebra.IsIntegral.isIntegral a
    refine ⟨⟨ContinuousMap.const _ a,
      ⟨IntermediateField.adjoin ℚ_[ℓ] {a}, IntermediateField.adjoin.finiteDimensional ha,
        fun _ ↦ IntermediateField.subset_adjoin ℚ_[ℓ] _ (Set.mem_singleton a)⟩⟩, rfl⟩

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def fieldUnitIso (ℓ : ℕ) [Fact ℓ.Prime] :
    let J := Scheme.ProEt.topology (Spec (.of K))
    let P := padicAlgClRingPresheaf (Spec (.of K)) ℓ ⋙ forget₂ RingCat Ab
    let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
    E.mapMon.obj (Mon.mk P) ≅
      E.mapMon.obj ((sheafToPresheaf J Ab).mapMon.obj
        (Mon.mk (padicAlgClSheaf (Spec (.of K)) ℓ))) := by
  dsimp only
  let J := Scheme.ProEt.topology (Spec (.of K))
  let P := padicAlgClRingPresheaf (Spec (.of K)) ℓ ⋙ forget₂ RingCat Ab
  let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  let φ := (sheafificationAdjunction J Ab.{u + 1}).unitAlgHom P
  have : IsIso (E.map φ) := unit_iso K P
  have : IsMonHom φ := by infer_instance
  let m := E.mapMon.map (Mon.ofHom φ)
  have : IsIso ((Mon.forget Ab.{u + 1}).map m) := unit_iso K P
  have : IsIso m := isIso_of_reflects_iso m (Mon.forget Ab.{u + 1})
  exact asIso m

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def boundedPointIso (ℓ : ℕ) [Fact ℓ.Prime] :
    let P := padicAlgClRingPresheaf (Spec (.of K)) ℓ ⋙ forget₂ RingCat Ab
    let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
    E.mapMon.obj (Mon.mk P) ≅ Mon.mk (AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ))) := by
  dsimp only
  let e : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K))) ≃+*
      ULift.{u + 1} (PadicAlgCl ℓ) :=
    ULift.ringEquiv.trans ((RingEquiv.ofBijective (boundedEval K ℓ)
      (boundedEval_bijective K ℓ)).trans ULift.ringEquiv.symm)
  let P := padicAlgClRingPresheaf (Spec (.of K)) ℓ ⋙ forget₂ RingCat Ab
  let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  letI : MonObj (E.obj P) := (E.mapMon.obj (Mon.mk P)).mon
  let f : E.obj P ⟶ AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ)) :=
    e.toAddEquiv.toAddCommGrpIso.hom
  have : IsMonHom f := by
    constructor
    · ext n
      change (e (n.down : ULift.{u + 1}
        (PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K))))).down =
          (n.down : PadicAlgCl ℓ)
      exact congrArg ULift.down (map_intCast e n.down)
    · apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro a b
      exact e.map_mul a b
  exact Mon.mkIso' (asIso f)

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def fieldCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime] :
    let J := Scheme.ProEt.topology (Spec (.of K))
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
    E.mapMon.obj ((sheafToPresheaf J Ab).mapMon.obj (Mon.mk A)) ≅
      Mon.mk (AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ))) := by
  dsimp only
  exact (Functor.mapIso _ ((sheafToPresheaf _ Ab).mapMon.mapIso
    (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ (Spec (.of K))))) ≪≫
      (fieldUnitIso K ℓ).symm ≪≫ boundedPointIso K ℓ

namespace Ordinary
open MonObj TensorProduct
variable (R : Type u) [Ring R] (M : Mod Ab.{u} (AddCommGrpCat.of R))

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable instance internalModule : Module R M.X where
  smul a m := (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)
  one_smul m := by
    have h := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ) ⊗ₜ[ℤ] m))
      (ModObj.one_smul_self (AddCommGrpCat.of R) M.X)
    simp only [AddCommGrpCat.comp_apply,
      AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul, one_zsmul] at h
    have hη : (η[AddCommGrpCat.of R]).hom (ULift.up (1 : ℤ)) = (1 : R) := by
      simpa using AddCommGrpCat.ringMonObj_one_apply R (ULift.up (1 : ℤ))
    rw [hη] at h
    exact h
  mul_smul a b m := by
    have h := congrArg (fun f ↦ f.hom ((a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] m))
      (ModObj.mul_smul (M := AddCommGrpCat.of R) M.X)
    exact h
  smul_zero a := by
    change (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] (0 : M.X)) = 0
    simp
  smul_add a m n := by
    change (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] (m + n)) = _
    simp only [TensorProduct.tmul_add, map_add]
    rfl
  zero_smul m := by
    change (γ[AddCommGrpCat.of R,M.X]).hom ((0 : R) ⊗ₜ[ℤ] m) = 0
    simp
  add_smul a b m := by
    change (γ[AddCommGrpCat.of R,M.X]).hom ((a + b) ⊗ₜ[ℤ] m) = _
    simp only [TensorProduct.add_tmul, map_add]
    rfl

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def internalToModule : Mod Ab.{u} (AddCommGrpCat.of R) ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R M.X
  map {M N} f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := map_add f.hom.hom
      map_smul' := fun a m ↦ by
        have h := congrArg (fun g ↦ g.hom (a ⊗ₜ[ℤ] m))
          (IsModHom.smul_hom (A := AddCommGrpCat.of R) (f := f.hom))
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m)
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m) at h
        exact h }
  map_id M := rfl
  map_comp f g := rfl

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def ordinaryAct (N : ModuleCat.{u} R) :
    AddCommGrpCat.of R ⊗ AddCommGrpCat.of N ⟶ AddCommGrpCat.of N :=
  AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : R) (m : N) ↦ a • m)
    (fun a b m ↦ add_smul a b m)
    (fun c a m ↦ smul_assoc c a m)
    (fun a m n ↦ smul_add a m n)
    (fun c a m ↦ smul_comm a c m))).toAddMonoidHom

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def moduleToInternalObj (N : ModuleCat.{u} R) :
    Mod Ab.{u} (AddCommGrpCat.of R) := by
  letI : ModObj (AddCommGrpCat.of R) (AddCommGrpCat.of N) :=
    ModObj.mk' (AddCommGrpCat.of R) (ordinaryAct R N)
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n m ↦ by
        change (n.down : R) • m = n.down • m
        exact Int.cast_smul_eq_zsmul R n.down m))
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun a b m ↦ by
        exact mul_smul a b m))
  exact ⟨AddCommGrpCat.of N⟩

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def moduleToInternalHom {M N : Mod Ab.{u} (AddCommGrpCat.of R)}
    (f : (internalToModule R).obj M ⟶ (internalToModule R).obj N) : M ⟶ N :=
  Mod.homMk (AddCommGrpCat.ofHom f.hom.toAddMonoidHom)
    (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a m ↦ by
      exact f.hom.map_smul a m))

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def internalToModuleFullyFaithful : (internalToModule R).FullyFaithful where
  preimage f := moduleToInternalHom R f
  map_preimage f := by ext m; rfl
  preimage_map f := Mod.hom_ext _ _ rfl

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance : (internalToModule R).Full := (internalToModuleFullyFaithful R).full
/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance : (internalToModule R).Faithful := (internalToModuleFullyFaithful R).faithful

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def realizationIso (N : ModuleCat.{u} R) :
    (internalToModule R).obj (moduleToInternalObj R N) ≅ N :=
  ModuleCat.isoMk (Iso.refl _) (fun _ ↦ rfl)

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance : (internalToModule R).EssSurj where
  mem_essImage N := ⟨moduleToInternalObj R N, ⟨realizationIso R N⟩⟩

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance : (internalToModule R).IsEquivalence where

end Ordinary

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def ordinary (R : Type u) [Ring R] :
    Mod Ab.{u} (AddCommGrpCat.of R) ⥤ ModuleCat.{u} R :=
  Ordinary.internalToModule R

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def fieldFiber (ℓ : ℕ) [Fact ℓ.Prime] :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ) := by
  let J := Scheme.ProEt.topology (Spec (.of K))
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
  let S := sheafToPresheaf J Ab.{u + 1}
  let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  exact (S ⋙ E).mapMod A ⋙
    Mod.comap (inv (fieldCoefficientIso K ℓ).hom.hom) ⋙
      ordinary (ULift.{u + 1} (PadicAlgCl ℓ)) ⋙
        ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv.symm.toRingHom :
          PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ))

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable instance ordinary_equivalence (R : Type u) [Ring R] :
    (ordinary R).IsEquivalence := by
  unfold ordinary
  infer_instance

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance ordinary_additive (R : Type u) [Ring R] : (ordinary R).Additive where
  map_add := by intros; rfl

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance fieldFiber_additive (ℓ : ℕ) [Fact ℓ.Prime] : (fieldFiber K ℓ).Additive := by
  unfold fieldFiber
  infer_instance

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance comap_colimits {A B : Ab.{u}} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] : PreservesFiniteColimits (Mod.comap (D := Ab.{u}) f) where
  preservesFiniteColimits I _ _ := by
    have : PreservesColimitsOfShape I (Mod.comap (D := Ab.{u}) f ⋙ Mod.forget A) :=
      inferInstanceAs (PreservesColimitsOfShape I (Mod.forget B))
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (Mod.comap (D := Ab.{u}) f) (Mod.forget A)

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance fieldFiber_colimits (ℓ : ℕ) [Fact ℓ.Prime] :
    PreservesFiniteColimits (fieldFiber K ℓ) := by
  let J := Scheme.ProEt.topology (Spec (.of K))
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
  let S := sheafToPresheaf J Ab.{u + 1}
  let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  have : PreservesFiniteColimits (S ⋙ E) :=
    (geometric_field_proetale_evaluation_exact K).2.2.1
  have : PreservesFiniteColimits ((S ⋙ E).mapMod A) := inferInstance
  have : PreservesFiniteColimits (Mod.comap (D := Ab.{u + 1})
    (inv (fieldCoefficientIso K ℓ).hom.hom)) := inferInstance
  have : PreservesFiniteColimits (ordinary (ULift.{u + 1} (PadicAlgCl ℓ))) := inferInstance
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ))) := by
    refine ⟨fun I _ _ ↦ ?_⟩
    have : PreservesColimitsOfShape I
        (ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.symm.toRingHom :
            PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ)) ⋙
            forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}) :=
      inferInstanceAs (PreservesColimitsOfShape I
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) Ab.{u + 1}))
    exact preservesColimitsOfShape_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1})
  unfold fieldFiber
  infer_instance

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def ordinaryRegularCoordinates (ℓ : ℕ) [Fact ℓ.Prime] :
    (ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv.symm.toRingHom :
      PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ))).obj
        ((ordinary (ULift.{u + 1} (PadicAlgCl ℓ))).obj
          (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ))))) ≃ₗ[PadicAlgCl ℓ]
            PadicAlgCl ℓ where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def fieldRegularCoordinates (ℓ : ℕ) [Fact ℓ.Prime] :
    (fieldFiber K ℓ).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) ≃ₗ[PadicAlgCl ℓ]
        PadicAlgCl ℓ := by
  let J := Scheme.ProEt.topology (Spec (.of K))
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
  let S := sheafToPresheaf J Ab.{u + 1}
  let E := (evaluation (Spec (.of K)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  let T := (S ⋙ E).mapMod A
  let V := Mod.comap (D := Ab.{u + 1}) (inv (fieldCoefficientIso K ℓ).hom.hom)
  let D := ordinary (ULift.{u + 1} (PadicAlgCl ℓ)) ⋙
    ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv.symm.toRingHom :
      PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ))
  let e₁ : T.obj (Mod.regular A) ≅ Mod.regular ((S ⋙ E).obj A) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp])
  let e₂ := Mod.regularIsoOfIsIso (fieldCoefficientIso K ℓ).hom.hom
  exact ((D.mapIso ((V.mapIso e₁) ≪≫ e₂)).toLinearEquiv).trans
    (ordinaryRegularCoordinates ℓ)

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
noncomputable def geometricPoint (Y : Scheme.{u}) (x : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField x))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x)
    (AlgebraicClosure (Y.residueField x)))) ≫ Y.fromSpecResidueField x

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def fiber (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (x : Y) :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (geometricPoint Y x) ⋙
    fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance fiber_additive (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (x : Y) :
    (fiber ℓ Y x).Additive := by unfold fiber; infer_instance

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
instance fiber_colimits (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (x : Y) :
    PreservesFiniteColimits (fiber ℓ Y x) := by unfold fiber; infer_instance

/-- Explicit geometric-field evaluation and its module-theoretic properties.
Source: RefactorInstruction, Section 4, geometric fibers; the ordinary-module
construction uses the tensor-action proof of internalModuleAb_equivalence
(auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def fiberRegularCoordinates (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (x : Y) :
    (fiber ℓ Y x).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ := by
  unfold fiber
  exact ((fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ).mapIso
    (condensedQbarRegularPullbackIso ℓ (geometricPoint Y x))).toLinearEquiv |>.trans
      (fieldRegularCoordinates (AlgebraicClosure (Y.residueField x)) ℓ)

end CondensedQbarGeometricEvaluation

/-- The value of a regular-module endomorphism in chosen linear coordinates.
Keeping this operation folded avoids reducing inverse-image module constructions
while comparing the same coordinate data.
Source: RefactorInstruction, Section 4, geometric scalar evaluation
(auxiliary; not a blueprint node). -/
noncomputable def regularScalarValue
    {R : Type w} [CommRing R] {C : Type v} [Category.{z} C]
    (F : C ⥤ ModuleCat.{u} R) {A : C} (c : F.obj A ≃ₗ[R] R) (f : A ⟶ A) : R :=
  c (F.map f (c.symm 1))

/-- Computation rule for the folded regular scalar value.
Source: RefactorInstruction, Section 4, geometric scalar evaluation
(auxiliary; not a blueprint node). -/
lemma regularScalarValue_def
    {R : Type w} [CommRing R] {C : Type v} [Category.{z} C]
    (F : C ⥤ ModuleCat.{u} R) {A : C} (c : F.obj A ≃ₗ[R] R) (f : A ⟶ A) :
    regularScalarValue F c f = c (F.map f (c.symm 1)) := by
  unfold regularScalarValue
  rfl

end AlgebraicGeometry.ProEtale
