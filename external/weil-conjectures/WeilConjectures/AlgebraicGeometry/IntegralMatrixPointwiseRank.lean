/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
public import Mathlib.LinearAlgebra.Matrix.Rank

import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import Mathlib.Algebra.Field.ULift
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # The geometric input to analytic integral matrix charts -/

@[expose] public section
universe u v w v₁ w₁
open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
@[instance_reducible] private noncomputable def liftedNormedField (E : Type) [NormedField E] :
    NormedField (ULift.{u} E) :=
  NormedField.induced _ E ULift.ringEquiv ULift.down_injective
attribute [local instance] liftedNormedField
private noncomputable def continuousLiftIso (Y : Scheme.{u}) (E : Type) [NormedField E] :
    continuousMapRingSheaf Y E ≅ continuousCoefficientRingSheaf Y (ULift.{u} E) where
  hom := ⟨{
    app := fun _ ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        (((ULift.ringEquiv : ULift.{u} E ≃+* E).symm.toRingHom.compLeftContinuous
          _ continuous_uliftUp).comp
          ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩
  inv := ⟨{
    app := fun _ ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        (((ULift.ringEquiv : ULift.{u} E ≃+* E).toRingHom.compLeftContinuous
          _ continuous_uliftDown).comp
          ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

private noncomputable def restrictLiftEquiv (E : Type) [Field E]
    (M : ModuleCat.{u + 1} (ULift.{u} E))
    (b : M ≃ₗ[ULift.{u} E] ULift.{u} E) :
    (ModuleCat.restrictScalars (ULift.ringEquiv.symm : E ≃+* ULift.{u} E).toRingHom).obj M
      ≃ₗ[E] E where
  toFun m := (b m).down
  invFun e := b.symm (ULift.up e)
  left_inv m := by exact b.symm_apply_apply m
  right_inv e := by simp
  map_add' m n := congrArg ULift.down (b.map_add m n)
  map_smul' r m := congrArg ULift.down (b.map_smul (ULift.up r) m)

private theorem exists_small_evaluation
    (E : Type) [NormedField E] [TotallyDisconnectedSpace E]
    (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω)) (x : Y) (ha : a z = x)
    (R : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
    [IsIso e] [IsMonHom e] :
    ∃ F : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) R ⥤ ModuleCat.{u + 1} E,
      F.Additive ∧ PreservesFiniteColimits F ∧
      ∃ b : F.obj (Mod.regular R) ≃ₗ[E] E,
        ∀ p : Mod.regular R ⟶ Mod.regular R,
          b (F.map p (b.symm 1)) =
            (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 Y))))
              (ULift.up 1)).down x := by
  subst x
  have : TotallyDisconnectedSpace (ULift.{u} E) :=
    Topology.IsEmbedding.uliftDown.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨F, G, hF, hG, hFc, hGc, hFG, b, c, hb, hc⟩ :=
    exists_condensedField_compatible_evaluations (ULift.{u} E) Y Y Y Ω
      (𝟙 Y) (𝟙 Y) a a rfl z
  have := hF
  have := hFc
  let B := (ProEtale.upperStar AddCommGrpCat.{u + 1} (𝟙 Y)).obj
    (condensedRingObj (Profinite.continuousCoefficientRingObj (ULift.{u} E)) Y)
  let eB := condensedFieldPullbackRealization (ULift.{u} E) (𝟙 Y)
  let L := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (continuousLiftIso Y E)
  let β : R ⟶ B := e ≫ L.hom ≫ inv eB
  have : IsMonHom β := by dsimp [β, L, eB]; infer_instance
  have : IsIso β := by dsimp [β, L, eB]; infer_instance
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) (inv β)
  let J : ModuleCat.{u + 1} (ULift.{u} E) ⥤ ModuleCat.{u + 1} E :=
    ModuleCat.restrictScalars
    (ULift.ringEquiv.symm : E ≃+* ULift.{u} E).toRingHom
  have : J.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv.{0, u, u + 1}
    (ULift.ringEquiv.symm : E ≃+* ULift.{u} E)
  have hQa : Q.Additive := inferInstance
  have hQc : PreservesFiniteColimits Q := inferInstance
  have hJa : J.Additive := inferInstance
  have hJc : PreservesFiniteColimits J :=
    ⟨fun I _ _ ↦ (Adjunction.isEquivalence_preservesColimits J).preservesColimitsOfShape⟩
  let H : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) R ⥤ ModuleCat.{u + 1} E :=
    Q ⋙ F ⋙ J
  have hHa : H.Additive := inferInstance
  have hHc : PreservesFiniteColimits H := inferInstance
  let r : Q.obj (Mod.regular R) ≅ Mod.regular B := Mod.regularIsoOfIsIso β
  let b₀ := (F.mapIso r).toLinearEquiv.trans b
  refine ⟨H, hHa, hHc, restrictLiftEquiv E _ b₀, ?_⟩
  intro p
  let q := r.inv ≫ Q.map p ≫ r.hom
  have hq : q.hom = inv β ≫ p.hom ≫ β := by rfl
  have h : inv eB ≫ q.hom ≫ eB = L.inv ≫ inv e ≫ p.hom ≫ e ≫ L.hom := by
    rw [hq]
    simp [β, Category.assoc]
  have hp := hb q
  rw [h] at hp
  have hp' := congrArg ULift.down hp
  change (b (F.map q (b.symm 1))).down =
    (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 Y))))
      (ULift.up 1)).down (a z) at hp'
  change (b₀ ((F.map (Q.map p)) (b₀.symm (ULift.up 1)))).down = _
  change (b ((F.map r.hom) ((F.map (Q.map p))
    ((F.map r.inv) (b.symm 1))))).down = _
  simpa only [q, Functor.map_comp, ModuleCat.comp_apply] using hp'

private theorem exists_continuous_evaluation
    (E : Type) [NormedField E] [TotallyDisconnectedSpace E]
    (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω)) (x : Y) (ha : a z = x) :
    let A := (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)
    ∃ F : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) A ⥤ ModuleCat.{u + 1} E,
      F.Additive ∧ PreservesFiniteColimits F ∧
      ∃ b : F.obj (Mod.regular A) ≃ₗ[E] E, ∀ p : Mod.regular A ⟶ Mod.regular A,
        b (F.map p (b.symm 1)) =
          ((p.hom.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down x := by
  let A := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)
  obtain ⟨F, hF, hFc, b, hb⟩ := exists_small_evaluation E Y Ω a z x ha A (𝟙 A)
  refine ⟨F, hF, hFc, b, ?_⟩
  intro p
  have hp := hb p
  have hid : inv (𝟙 A) ≫ p.hom ≫ 𝟙 A = p.hom := by
    rw [IsIso.inv_id]
    exact (Category.id_comp _).trans (Category.comp_id p.hom)
  rw [hid] at hp
  exact hp

private theorem linearEquiv_conjugate_map
    {E : Type v} [Field E] {C : Type v₁} [Category.{w₁} C]
    (F : C ⥤ ModuleCat.{w} E) {A B : C} (r : A ≅ B)
    (b : F.obj B ≃ₗ[E] E) (p : A ⟶ A) :
    let c := (F.mapIso r).toLinearEquiv.trans b
    c (F.map p (c.symm 1)) = b (F.map (r.inv ≫ p ≫ r.hom) (b.symm 1)) := by
  dsimp only
  change b ((F.map r.hom) ((F.map p) ((F.map r.inv) (b.symm 1)))) = _
  simp only [Functor.map_comp, ModuleCat.comp_apply]

private structure GeometricLift (Y : Scheme.{u}) (x : Y) where
  Ω : Type u
  field : Field Ω
  algClosed : @IsAlgClosed Ω field
  v : Spec (@CommRingCat.of Ω field.toCommRing) ⟶ Y
  z : Spec (@CommRingCat.of Ω field.toCommRing)
  point_eq : v z = x

attribute [local instance] GeometricLift.field GeometricLift.algClosed

private theorem exists_geometric_lift (Y : Scheme.{u}) (x : Y) :
    Nonempty (GeometricLift Y x) := by
  let Ω := AlgebraicClosure (Y.residueField x)
  let v : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x) Ω)) ≫
      Y.fromSpecResidueField x
  let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  exact ⟨⟨Ω, inferInstance, inferInstance, v, z,
    Scheme.fromSpecResidueField_apply x
      ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x) Ω))) z)⟩⟩

private lemma integral_matrix_corank_at_free (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (n t q : ℕ)
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (eC : (((ProEtale.upperStar AddCommGrpCat.{u + 1} g).mapMod _).obj
      ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj (cokernel a))) ≅
      Mod.finiteFree ((ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) q)
    (x : Y) :
    t - Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E g a i j x).val) = q := by
  classical
  have : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let R := condensedRingObj (integralCoeff ℓ E) X
  let A := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)
  obtain ⟨d⟩ := nonempty_integralMatrixCoefficientTransport ℓ E g
  have := d.additive
  have := d.finiteColimits
  let L := d.functor
  obtain ⟨w⟩ := exists_geometric_lift Y x
  let Ω := w.Ω
  let v := w.v
  let z := w.z
  have hv : v z = x := w.point_eq
  obtain ⟨F, hF, hFc, b, hb⟩ := exists_continuous_evaluation E Y Ω v z x hv
  have := hF
  have := hFc
  let H := L ⋙ F
  have : H.Additive := inferInstance
  have : PreservesFiniteColimits H := inferInstance
  let c := (F.mapIso d.regularIso).toLinearEquiv.trans b
  have hcoeff (p : Mod.regular R ⟶ Mod.regular R) :
      c (H.map p (c.symm 1)) = (integralRegularCoefficient ℓ E X p (g x)).val := by
    exact (linearEquiv_conjugate_map F d.regularIso b (L.map p)).trans
      ((hb _).trans (d.coefficient p x))
  let M : Matrix (Fin t) (Fin n) E :=
    fun i j ↦ (integralMatrixPullbackFunctions ℓ E g a i j x).val
  let cn := finiteFreeEvaluationCoords (Mod.regular R) H c n
  let ct := finiteFreeEvaluationCoords (Mod.regular R) H c t
  have hM : ct.toLinearMap ∘ₗ (H.map a).hom ∘ₗ cn.symm.toLinearMap = M.mulVecLin := by
    apply finiteFreeEvaluationCoords_matrix
    intro i j
    exact (hcoeff _).trans
      (congrArg Subtype.val (matrix_coefficient_pullback ℓ E g a i j x).symm)
  have hdim := finrank_cokernel_of_matrix cn ct (H.map a) M hM
  have hq : Module.finrank E (cokernel (H.map a) : ModuleCat.{u + 1} E) = q := by
    let k : cokernel (H.map a) ≅ F.obj (Mod.finiteFree A q) :=
      (PreservesCokernel.iso H a).symm ≪≫ F.mapIso (d.freeCokernel n t q a eC)
    calc
      _ = Module.finrank E (F.obj (Mod.finiteFree A q)) := k.toLinearEquiv.finrank_eq
      _ = Module.finrank E (Fin q → E) :=
        (finiteFreeEvaluationCoords (Mod.regular A) F b q).finrank_eq
      _ = q := by rw [Module.finrank_pi, Fintype.card_fin]
  exact hdim.symm.trans hq

/-- The evaluated integral matrix has constant field rank on a free rational-cokernel
cover member.

Source: Bhatt--Scholze, Section 6.8, continuous integral coefficient framework,
and Example 4.1.10, exact geometric-field evaluation.
(auxiliary; not a blueprint node)

Proof: choose the supplied rational-cokernel cover and choose its finite free basis
on each member, of rank q. Pull the cokernel presentation and this basis to an
algebraic closure of the residue field at any point. Scheme inverse image preserves
cokernels, as does final-object evaluation over the algebraically closed field.
The coefficient pullback comparison and the canonical continuous realization identify
the evaluated presentation with the pointwise E-matrix displayed here. Evaluation
sends the free target and cokernel to E-vector spaces of dimensions t and q.
Rank-nullity therefore gives matrix rank t-q, independent of the point.
The integral matrix and its E-valued image have the same entries under the scalar
inclusion O_E to E. A rank-zero source, rank-zero target or empty member causes no
exception; the rank formula still applies wherever there is a point. -/
theorem integralMatrix_pointwise_rank (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k (x y : V.X k),
      Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val) =
        Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val) :=
  by
    obtain ⟨V, hV⟩ := hC
    refine ⟨V, fun k x y ↦ ?_⟩
    obtain ⟨q, ⟨eC⟩⟩ := hV k
    have hx := integral_matrix_corank_at_free ℓ E (V.f k) n t q a eC x
    have hy := integral_matrix_corank_at_free ℓ E (V.f k) n t q a eC y
    have hxr := Matrix.rank_le_card_height
      (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val)
    have hyr := Matrix.rank_le_card_height
      (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val)
    simp only [Fintype.card_fin] at hxr hyr
    omega

end AlgebraicGeometry.ProEtale.CondensedRing
