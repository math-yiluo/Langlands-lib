import Langlands.Shimura.PEL.HarrisTaylorCMDivisionQuasiProjectiveDecomposition
import Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeStabilizers
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelRigidityProof
import Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentCoproduct
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Normal-quotient descent of quasi-projective representability from its premises -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- A locally noetherian scheme over `Spec F`, as an admissible test. -/
def noetherianCMTest (X : Over (Spec (.of F))) [IsLocallyNoetherian X.left] : DisBases :=
  ⟨X, componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} X⟩

section Representation

variable {D C preservation composition unitCoherence associativity comparison symmetry
  stability square universality dualityNaturality polarizationStability compatibility h htor}
variable {U' : SmallCMLevel D}
  (R : CMLevelQuasiProjectiveRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U')

instance CMLevelQuasiProjectiveRepresentation.isLocallyNoetherian :
    IsLocallyNoetherian R.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian R.scheme.hom

/-- The representing scheme at the fine level, as an admissible test. -/
def CMLevelQuasiProjectiveRepresentation.test : DisBases :=
  noetherianCMTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality R.scheme

/-- The fine class of a point of the representing scheme. -/
def CMLevelQuasiProjectiveRepresentation.cls (T : DisBases) (a : T.obj ⟶ R.scheme) :
    ((moduli).obj U').obj (Opposite.op T) :=
  R.represents.hom.app (Opposite.op T) (ULift.up a)

/-- The point of the representing scheme of a fine class. -/
def CMLevelQuasiProjectiveRepresentation.pt (T : DisBases)
    (c : ((moduli).obj U').obj (Opposite.op T)) : T.obj ⟶ R.scheme :=
  (R.represents.inv.app (Opposite.op T) c).down

namespace CMLevelQuasiProjectiveRepresentation

@[simp] theorem cls_pt (T : DisBases) (c : ((moduli).obj U').obj (Opposite.op T)) :
    R.cls T (R.pt T c) = c :=
  Iso.inv_hom_id_app_apply R.represents (Opposite.op T) c

@[simp] theorem pt_cls (T : DisBases) (a : T.obj ⟶ R.scheme) : R.pt T (R.cls T a) = a :=
  congrArg ULift.down (Iso.hom_inv_id_app_apply R.represents (Opposite.op T) ⟨a⟩)

theorem cls_injective (T : DisBases) : Function.Injective (R.cls T) := fun a b hab => by
  rw [← R.pt_cls T a, ← R.pt_cls T b, hab]

theorem cls_comp {T₁ T₂ : DisBases} (f : T₁ ⟶ T₂) (a : T₂.obj ⟶ R.scheme) :
    R.cls T₁ (f.hom ≫ a) = ((moduli).obj U').map f.op (R.cls T₂ a) :=
  NatTrans.naturality_apply R.represents.hom f.op ⟨a⟩

end CMLevelQuasiProjectiveRepresentation


section Action

variable (U : SmallCMLevel D) (hle : U'.obj.subgroup ≤ U.obj.subgroup)
  [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

set_option quotPrecheck false in
local notation "transl" g => (moduli).map (smallCMNormalInverseArrow D U U' hle g)
set_option quotPrecheck false in
local notation "forget" => (moduli).map (smallCMInclusion D hle)

namespace CMLevelQuasiProjectiveRepresentation

/-- The endomorphism of the representing scheme induced by inverse right
translation by `g`, recovered by Yoneda from the fine presheaf. -/
def act (g : U.obj.subgroup) : R.scheme ⟶ R.scheme :=
  R.pt R.test ((transl g).app (Opposite.op R.test) (R.cls R.test (𝟙 _)))

theorem cls_act (g : U.obj.subgroup) :
    R.cls R.test (R.act U hle g) =
      (transl g).app (Opposite.op R.test) (R.cls R.test (𝟙 _)) :=
  R.cls_pt _ _

theorem cls_comp_act (T : DisBases) (a : T.obj ⟶ R.scheme) (g : U.obj.subgroup) :
    R.cls T (a ≫ R.act U hle g) = (transl g).app (Opposite.op T) (R.cls T a) := by
  let aT : T ⟶ R.test := ObjectProperty.homMk a
  calc R.cls T (a ≫ R.act U hle g)
      = ((moduli).obj U').map aT.op (R.cls R.test (R.act U hle g)) :=
        R.cls_comp aT (R.act U hle g)
    _ = ((moduli).obj U').map aT.op
          ((transl g).app (Opposite.op R.test) (R.cls R.test (𝟙 _))) := by
        rw [R.cls_act U hle g]
    _ = (transl g).app (Opposite.op T)
          (((moduli).obj U').map aT.op (R.cls R.test (𝟙 _))) :=
        (NatTrans.naturality_apply _ _ _).symm
    _ = (transl g).app (Opposite.op T) (R.cls T (aT.hom ≫ 𝟙 _)) :=
        congrArg _ (R.cls_comp aT (𝟙 _)).symm
    _ = (transl g).app (Opposite.op T) (R.cls T a) :=
        congrArg (fun b => (transl g).app (Opposite.op T) (R.cls T b)) (Category.comp_id a)

theorem act_one : R.act U hle 1 = 𝟙 _ := by
  apply R.cls_injective R.test
  rw [R.cls_act U hle 1, smallCMNormalInverseArrow_one, CategoryTheory.Functor.map_id]
  rfl

theorem act_mul (g k : U.obj.subgroup) :
    R.act U hle (g * k) = R.act U hle k ≫ R.act U hle g := by
  apply R.cls_injective R.test
  refine Eq.trans ?_ (R.cls_comp_act U hle R.test (R.act U hle k) g).symm
  rw [R.cls_act U hle (g * k), R.cls_act U hle k, smallCMNormalInverseArrow_mul,
    CategoryTheory.Functor.map_comp]
  rfl

theorem act_of_mem (g : U.obj.subgroup)
    (hg : (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈ U'.obj.subgroup) :
    R.act U hle g = 𝟙 _ := by
  have ht : (transl g) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_id]
    apply smallLevelClassPresheafTower_map_eq_of_target_coset
    simpa using hg
  apply R.cls_injective R.test
  rw [R.cls_act U hle g, ht]
  rfl

theorem forget_cls_comp_act (T : DisBases) (a : T.obj ⟶ R.scheme) (g : U.obj.subgroup) :
    (forget).app (Opposite.op T) (R.cls T (a ≫ R.act U hle g)) =
      (forget).app (Opposite.op T) (R.cls T a) := by
  rw [cls_comp_act]
  have ht : (transl g) ≫ (forget) = forget := by
    rw [← CategoryTheory.Functor.map_comp]
    apply smallLevelClassPresheafTower_map_eq_of_target_coset
    change (((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ * 1)⁻¹ * 1) ∈ U.obj.subgroup
    simp
  exact congrArg (fun φ => φ.app (Opposite.op T) (R.cls T a)) ht

/-- The scheme automorphism of the representing scheme given by `g`. -/
def actIso (g : U.obj.subgroup) : R.scheme.left ≅ R.scheme.left where
  hom := (R.act U hle g).left
  inv := (R.act U hle g⁻¹).left
  hom_inv_id := by
    rw [← Over.comp_left, ← R.act_mul U hle g⁻¹ g, inv_mul_cancel, R.act_one U hle]
    rfl
  inv_hom_id := by
    rw [← Over.comp_left, ← R.act_mul U hle g g⁻¹, mul_inv_cancel, R.act_one U hle]
    rfl

/-- Inverse right translation as a group homomorphism to scheme automorphisms. -/
def actHom : U.obj.subgroup →* Aut R.scheme.left where
  toFun g := Aut.of (R.actIso U hle g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact congrArg CommaMorphism.left (R.act_one U hle)
  map_mul' g k := by
    apply Aut.ext
    apply Iso.ext
    exact congrArg CommaMorphism.left (R.act_mul U hle g k)

theorem le_ker_actHom : U'.obj.subgroup.subgroupOf U.obj.subgroup ≤ (R.actHom U hle).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply Aut.ext
  apply Iso.ext
  exact congrArg CommaMorphism.left (R.act_of_mem U hle g (Subgroup.mem_subgroupOf.mp hg))

/-- The residual group `U/U'` acting on the representing scheme. -/
def residualHom : SmallCMResidualGroup D U U' →* Aut R.scheme.left :=
  QuotientGroup.lift _ (R.actHom U hle) (R.le_ker_actHom U hle)

@[simp] theorem residualHom_mk (g : U.obj.subgroup) :
    (R.residualHom U hle (QuotientGroup.mk g)).asIso.hom = (R.act U hle g).left := rfl

theorem residualHom_comp (x y : SmallCMResidualGroup D U U') :
    (R.residualHom U hle x).asIso.hom ≫ (R.residualHom U hle y).asIso.hom =
      (R.residualHom U hle (y * x)).asIso.hom := by
  rw [map_mul, Aut.mul_asIso, Iso.trans_hom]

/-- A residual element fixing a point valued in a nonempty scheme is trivial:
this is the small-level rigidity of the coarse level. -/
theorem eq_one_of_comp_residualHom {T : Scheme.{0}} [Nonempty T] (a : T ⟶ R.scheme.left)
    (z : SmallCMResidualGroup D U U')
    (hz : a ≫ (R.residualHom U hle z).asIso.hom = a) : z = 1 := by
  induction z using QuotientGroup.induction_on with
  | H g =>
    rw [residualHom_mk] at hz
    let x := HarrisGeometricPoint.ofResidue T (Classical.arbitrary T)
    let b : Spec (CommRingCat.of x.Ω) ⟶ R.scheme.left := x.hom ≫ a
    have hb : b ≫ (R.act U hle g).left = b := by
      simp only [b, Category.assoc, hz]
    let p : Spec (CommRingCat.of x.Ω) ⟶ Spec (.of F) := b ≫ R.scheme.hom
    let Tb := cmGeometricTestBase D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality relativeDualSchemeExistence.{0}
      relativeDualSchemeGeometry.{0} p
    let bO : Tb.obj ⟶ R.scheme := Over.homMk b rfl
    have hbO : bO ≫ R.act U hle g = bO := by
      ext
      exact hb
    have hcls := R.cls_comp_act U hle Tb bO g
    rw [hbO] at hcls
    have key := (cmGeometricTestBase_normalTranslate_eq_iff D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
      relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} p U.obj U'.obj hle
      (cmSmallLevelRigidity D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h htor
        U.obj U.property) g 1 (R.cls Tb bO)).mp (by
      rw [CompactOpenLevel.normalInverseArrow_one, CategoryTheory.Functor.map_id]
      exact hcls.symm)
    simpa using key

/-- The residual group `U/U'` acting freely on the representing scheme, in the
composition convention of `FiniteFreeSchemeAction`. -/
def residualAction : FiniteFreeSchemeAction (SmallCMResidualGroup D U U') R.scheme.left where
  act q := (R.residualHom U hle q⁻¹).asIso
  one := by simp
  mul q r := by
    rw [R.residualHom_comp U hle, mul_inv_rev]
  free {T} _ a := by
    intro q r hqr
    have h1 := congrArg (· ≫ (R.residualHom U hle r).asIso.hom) hqr
    simp only [Category.assoc, R.residualHom_comp U hle, mul_inv_cancel, map_one,
      Aut.one_asIso, Iso.refl_hom, Category.comp_id] at h1
    exact (mul_inv_eq_one.mp (R.eq_one_of_comp_residualHom U hle a _ h1)).symm

@[simp] theorem residualAction_act_mk (g : U.obj.subgroup) :
    ((R.residualAction U hle).act (QuotientGroup.mk g)⁻¹).hom = (R.act U hle g).left := by
  change (R.residualHom U hle ((QuotientGroup.mk g)⁻¹)⁻¹).asIso.hom = _
  rw [inv_inv]
  rfl

theorem residualAction_over (q : SmallCMResidualGroup D U U') :
    ((R.residualAction U hle).act q).hom ≫ R.scheme.hom = R.scheme.hom := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q⁻¹
  rw [← inv_inv q, ← hg, residualAction_act_mk]
  exact Over.w (R.act U hle g)

instance relation_isLocallyNoetherian :
    IsLocallyNoetherian (R.residualAction U hle).relationScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (R.residualAction U hle).source

/-- The disjoint union of the graphs of the residual action, as an admissible test. -/
def relationTest : DisBases :=
  letI : IsLocallyNoetherian (Over.mk ((R.residualAction U hle).source ≫ R.scheme.hom)).left :=
    R.relation_isLocallyNoetherian U hle
  noetherianCMTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality
    (Over.mk ((R.residualAction U hle).source ≫ R.scheme.hom))

theorem target_comp_hom :
    (R.residualAction U hle).target ≫ R.scheme.hom =
      (R.residualAction U hle).source ≫ R.scheme.hom := by
  refine Sigma.hom_ext _ _ (fun q => ?_)
  change Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
      (R.residualAction U hle).target ≫ R.scheme.hom =
    Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
      (R.residualAction U hle).source ≫ R.scheme.hom
  rw [FiniteFreeSchemeAction.ι_target_assoc, FiniteFreeSchemeAction.ι_source_assoc]
  exact R.residualAction_over U hle q

/-- The first projection from the relation scheme, over `Spec F`. -/
def sourceO : (R.relationTest U hle).obj ⟶ R.scheme :=
  Over.homMk (R.residualAction U hle).source rfl

/-- The second projection from the relation scheme, over `Spec F`. -/
def targetO : (R.relationTest U hle).obj ⟶ R.scheme :=
  Over.homMk (R.residualAction U hle).target (R.target_comp_hom U hle)

/-- The summand of the relation scheme labelled by `q`, as a test morphism. -/
def summandO (q : SmallCMResidualGroup D U U') : R.test ⟶ R.relationTest U hle :=
  ObjectProperty.homMk (Over.homMk
    (Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q) (by
      change Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
        (R.residualAction U hle).source ≫ R.scheme.hom = R.scheme.hom
      simp))

/-- On the relation scheme, the two projections have the same coarse class. -/
theorem forget_cls_targetO
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :
    (forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.targetO U hle)) =
      (forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.sourceO U hle)) := by
  have hEt : ∀ q, Etale (R.summandO U hle q).hom.left := fun q => by
    change Etale (Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q)
    infer_instance
  have hSurj : ∀ x : (R.relationTest U hle).obj.left, ∃ (q : SmallCMResidualGroup D U U')
      (y : R.test.obj.left), (R.summandO U hle q).hom.left.base y = x := by
    intro x
    obtain ⟨⟨q, y⟩, hy⟩ :=
      (sigmaMk (fun _ : SmallCMResidualGroup D U U' => R.scheme.left)).surjective x
    refine ⟨q, y, ?_⟩
    rw [← hy, sigmaMk_mk]
    rfl
  have hsep := (hD U (R.relationTest U hle) (SmallCMResidualGroup D U U')
    (fun _ => R.test) (R.summandO U hle) hEt hSurj).isSeparatedFor
  apply hsep.ext
  rintro _ _ ⟨q⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q⁻¹
  have e₁ : (R.summandO U hle q).hom ≫ R.targetO U hle = 𝟙 _ ≫ R.act U hle g := by
    ext
    change Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
      (R.residualAction U hle).target = 𝟙 _ ≫ (R.act U hle g).left
    rw [FiniteFreeSchemeAction.ι_target, Category.id_comp, ← R.residualAction_act_mk U hle g,
      hg, inv_inv]
  have e₂ : (R.summandO U hle q).hom ≫ R.sourceO U hle = 𝟙 _ := by
    ext
    change Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
      (R.residualAction U hle).source = 𝟙 _
    rw [FiniteFreeSchemeAction.ι_source]
  calc ((moduli).obj U).map (R.summandO U hle q).op
        ((forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.targetO U hle)))
      = (forget).app (Opposite.op R.test)
          (R.cls _ ((R.summandO U hle q).hom ≫ R.targetO U hle)) := by
        rw [R.cls_comp]
        exact (NatTrans.naturality_apply _ _ _).symm
    _ = (forget).app (Opposite.op R.test) (R.cls _ (𝟙 _)) := by
        rw [e₁]
        exact R.forget_cls_comp_act U hle R.test (𝟙 _) g
    _ = (forget).app (Opposite.op R.test)
          (R.cls _ ((R.summandO U hle q).hom ≫ R.sourceO U hle)) := by
        rw [e₂]
    _ = ((moduli).obj U).map (R.summandO U hle q).op
          ((forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.sourceO U hle))) := by
        rw [R.cls_comp]
        exact NatTrans.naturality_apply _ _ _

section Quotient

variable {U hle} (Q : (R.residualAction U hle).EffectiveQuotient)

theorem act_left_comp_map (g : U.obj.subgroup) : (R.act U hle g).left ≫ Q.map = Q.map := by
  let A := R.residualAction U hle
  let q : SmallCMResidualGroup D U U' := (QuotientGroup.mk g)⁻¹
  calc (R.act U hle g).left ≫ Q.map = (A.act q).hom ≫ Q.map :=
        (congrArg (· ≫ Q.map) (R.residualAction_act_mk U hle g)).symm
    _ = (Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫ A.target) ≫
          Q.map := congrArg (· ≫ Q.map) (A.ι_target q).symm
    _ = Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
          (A.target ≫ Q.map) := Category.assoc _ _ _
    _ = Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫
          (A.source ≫ Q.map) := congrArg (_ ≫ ·) Q.condition
    _ = (Sigma.ι (fun _ : SmallCMResidualGroup D U U' => R.scheme.left) q ≫ A.source) ≫
          Q.map := (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ Q.map := congrArg (· ≫ Q.map) (A.ι_source q)
    _ = Q.map := Category.id_comp _

/-- Two points of the representing scheme with the same image in the quotient
have the same coarse class. -/
theorem forget_cls_eq_of_comp_eq
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (T : DisBases) (b₁ b₂ : T.obj ⟶ R.scheme) (hb : b₁.left ≫ Q.map = b₂.left ≫ Q.map) :
    (forget).app (Opposite.op T) (R.cls T b₁) = (forget).app (Opposite.op T) (R.cls T b₂) := by
  let w : T.obj.left ⟶ (R.residualAction U hle).relationScheme :=
    Q.isPullback.lift b₁.left b₂.left hb
  have hw₁ : w ≫ (R.residualAction U hle).target = b₁.left := Q.isPullback.lift_fst _ _ _
  have hw₂ : w ≫ (R.residualAction U hle).source = b₂.left := Q.isPullback.lift_snd _ _ _
  let wT : T ⟶ R.relationTest U hle := ObjectProperty.homMk (Over.homMk w (by
    change w ≫ (R.residualAction U hle).source ≫ R.scheme.hom = T.obj.hom
    rw [← Category.assoc, hw₂]
    exact Over.w b₂))
  have e₁ : b₁ = wT.hom ≫ R.targetO U hle := by
    ext
    exact hw₁.symm
  have e₂ : b₂ = wT.hom ≫ R.sourceO U hle := by
    ext
    exact hw₂.symm
  calc (forget).app (Opposite.op T) (R.cls T b₁)
      = (forget).app (Opposite.op T) (R.cls T (wT.hom ≫ R.targetO U hle)) := by
        rw [← e₁]
    _ = ((moduli).obj U).map wT.op
          ((forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.targetO U hle))) := by
        rw [R.cls_comp]
        exact NatTrans.naturality_apply _ _ _
    _ = ((moduli).obj U).map wT.op
          ((forget).app (Opposite.op (R.relationTest U hle)) (R.cls _ (R.sourceO U hle))) := by
        rw [R.forget_cls_targetO U hle hD]
    _ = (forget).app (Opposite.op T) (R.cls T (wT.hom ≫ R.sourceO U hle)) := by
        rw [R.cls_comp]
        exact (NatTrans.naturality_apply _ _ _).symm
    _ = (forget).app (Opposite.op T) (R.cls T b₂) := by
        rw [← e₂]

/-- The open connected component of an admissible test, as an admissible test. -/
def componentTest (T : DisBases) (c : _root_.ConnectedComponents T.obj.left) : DisBases :=
  letI : IsLocallyNoetherian (Over.mk (componentι T.obj.left c ≫ T.obj.hom)).left :=
    componentSchemeLocallyNoetherian T.obj.left c
  noetherianCMTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality (Over.mk (componentι T.obj.left c ≫ T.obj.hom))

/-- The inclusion of an open connected component, as a test morphism. -/
def componentTestι (T : DisBases) (c : _root_.ConnectedComponents T.obj.left) :
    componentTest (D := D) (C := C) (preservation := preservation) (composition := composition)
      (unitCoherence := unitCoherence) (associativity := associativity)
      (comparison := comparison) (symmetry := symmetry) (stability := stability)
      (square := square) (universality := universality) T c ⟶ T :=
  ObjectProperty.homMk (Over.homMk (componentι T.obj.left c) rfl)

/-- Two points of the representing scheme with the same coarse class have the
same image in the quotient. -/
theorem comp_eq_of_forget_cls_eq
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (T : DisBases) (b₁ b₂ : T.obj ⟶ R.scheme)
    (hb : (forget).app (Opposite.op T) (R.cls T b₁) = (forget).app (Opposite.op T) (R.cls T b₂)) :
    b₁.left ≫ Q.map = b₂.left ≫ Q.map := by
  apply component_hom_ext T.obj.left
  intro c
  let eT := componentTestι (D := D) (C := C) (preservation := preservation)
    (composition := composition) (unitCoherence := unitCoherence)
    (associativity := associativity) (comparison := comparison) (symmetry := symmetry)
    (stability := stability) (square := square) (universality := universality) T c
  have hconn : ConnectedSpace (componentTest (D := D) (C := C) (preservation := preservation)
      (composition := composition) (unitCoherence := unitCoherence)
      (associativity := associativity) (comparison := comparison) (symmetry := symmetry)
      (stability := stability) (square := square) (universality := universality)
      T c).obj.left :=
    componentSchemeConnected T.obj.left c
  have hb' : (forget).app _ (R.cls _ (eT.hom ≫ b₁)) = (forget).app _ (R.cls _ (eT.hom ≫ b₂)) := by
    rw [R.cls_comp, R.cls_comp, NatTrans.naturality_apply, NatTrans.naturality_apply, hb]
  obtain ⟨g, hg⟩ := hO U' U hle _ hconn _ _ hb'
  have hg' := (R.cls_comp_act U hle _ (eT.hom ≫ b₁) g).trans hg
  have hl := congrArg CommaMorphism.left (R.cls_injective _ hg')
  simp only [Over.comp_left] at hl
  change componentι T.obj.left c ≫ b₁.left ≫ (R.act U hle g).left =
    componentι T.obj.left c ≫ b₂.left at hl
  calc componentι T.obj.left c ≫ b₁.left ≫ Q.map
      = componentι T.obj.left c ≫ b₁.left ≫ (R.act U hle g).left ≫ Q.map := by
        rw [R.act_left_comp_map Q g]
    _ = (componentι T.obj.left c ≫ b₁.left ≫ (R.act U hle g).left) ≫ Q.map := by
        simp only [Category.assoc]
    _ = componentι T.obj.left c ≫ b₂.left ≫ Q.map := by
        rw [hl, Category.assoc]

/-- The sheaf condition of the étale descent premise for a single étale
surjective test morphism. -/
theorem isSheafFor_singleton_of_etale
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (V : SmallCMLevel D) {S₁ S : DisBases} (p : S₁ ⟶ S) [Etale p.hom.left]
    [Surjective p.hom.left] :
    Presieve.IsSheafFor ((moduli).obj V) (Presieve.singleton p) := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact hD V S PUnit (fun _ => S₁) (fun _ => p) (fun _ => inferInstance)
    (fun x => ⟨⟨⟩, Surjective.surj x⟩)

theorem map_injective_of_etale
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (V : SmallCMLevel D) {S₁ S : DisBases} (p : S₁ ⟶ S) [Etale p.hom.left]
    [Surjective p.hom.left] : Function.Injective (((moduli).obj V).map p.op) :=
  Presieve.isSeparatedFor_singleton.mp
    (isSheafFor_singleton_of_etale hD V p).isSeparatedFor

variable (t : Q.scheme ⟶ Spec (.of F)) (ht : Q.map ≫ t = R.scheme.hom)

/-- The pullback of the quotient map along a point of the quotient, as a test. -/
def pullbackTest (S : DisBases) (f : S.obj ⟶ Over.mk t) : DisBases :=
  letI : IsLocallyNoetherian (Over.mk (pullback.fst f.left Q.map ≫ S.obj.hom)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f.left Q.map)
  noetherianCMTest D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality (Over.mk (pullback.fst f.left Q.map ≫ S.obj.hom))

/-- The projection of the pullback test to the given test. -/
def pullbackTestπ (S : DisBases) (f : S.obj ⟶ Over.mk t) : R.pullbackTest Q t S f ⟶ S :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.left Q.map) rfl)

instance (S : DisBases) (f : S.obj ⟶ Over.mk t) : Etale (R.pullbackTestπ Q t S f).hom.left :=
  inferInstanceAs (Etale (pullback.fst f.left Q.map))

instance (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    Surjective (R.pullbackTestπ Q t S f).hom.left :=
  inferInstanceAs (Surjective (pullback.fst f.left Q.map))

/-- The projection of the pullback test to the representing scheme. -/
def pullbackTestPt (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    (R.pullbackTest Q t S f).obj ⟶ R.scheme :=
  Over.homMk (pullback.snd f.left Q.map) (by
    change pullback.snd f.left Q.map ≫ R.scheme.hom = pullback.fst f.left Q.map ≫ S.obj.hom
    rw [← ht, ← Category.assoc, ← pullback.condition, Category.assoc]
    congr 1
    exact Over.w f)

theorem pullbackTestPt_comp_map (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    (R.pullbackTestPt Q t ht S f).left ≫ Q.map =
      (R.pullbackTestπ Q t S f).hom.left ≫ f.left :=
  pullback.condition.symm

theorem compatible_pullbackTest
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) {Z : DisBases}
    (g₁ g₂ : Z ⟶ R.pullbackTest Q t S f)
    (hg : g₁ ≫ R.pullbackTestπ Q t S f = g₂ ≫ R.pullbackTestπ Q t S f) :
    ((moduli).obj U).map g₁.op ((forget).app _ (R.cls _ (R.pullbackTestPt Q t ht S f))) =
      ((moduli).obj U).map g₂.op ((forget).app _ (R.cls _ (R.pullbackTestPt Q t ht S f))) := by
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← R.cls_comp, ← R.cls_comp]
  apply R.forget_cls_eq_of_comp_eq Q hD
  have hl := congrArg (fun k => k.hom.left) hg
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] at hl
  simp only [Over.comp_left, Category.assoc, R.pullbackTestPt_comp_map Q t ht]
  rw [← Category.assoc, hl, Category.assoc]

theorem existsUnique_classOfMap
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    ∃! c : ((moduli).obj U).obj (Opposite.op S),
      ((moduli).obj U).map (R.pullbackTestπ Q t S f).op c =
        (forget).app _ (R.cls _ (R.pullbackTestPt Q t ht S f)) :=
  (Presieve.isSheafFor_singleton.mp (isSheafFor_singleton_of_etale hD U _)) _
    (fun g₁ g₂ hg => R.compatible_pullbackTest Q t ht hD S f g₁ g₂ hg)

/-- The coarse class of a point of the quotient, by étale descent from the
pullback of the quotient map. -/
def classOfMap
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) : ((moduli).obj U).obj (Opposite.op S) :=
  (R.existsUnique_classOfMap Q t ht hD S f).exists.choose

theorem classOfMap_spec
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    ((moduli).obj U).map (R.pullbackTestπ Q t S f).op (R.classOfMap Q t ht hD S f) =
      (forget).app _ (R.cls _ (R.pullbackTestPt Q t ht S f)) :=
  (R.existsUnique_classOfMap Q t ht hD S f).exists.choose_spec

theorem moduli_map_comp (V : SmallCMLevel D) {X Y Z : DisBases} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ((moduli).obj V).obj (Opposite.op Z)) :
    ((moduli).obj V).map (f ≫ g).op x = ((moduli).obj V).map f.op (((moduli).obj V).map g.op x) :=
  CategoryTheory.Functor.map_comp_apply ((moduli).obj V) g.op f.op x

/-- Characterization of `classOfMap`: its pullback along any test morphism is the
coarse class of any lift through the quotient map. -/
theorem map_classOfMap
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) {S₂ : DisBases} (q : S₂ ⟶ S)
    (a₂ : S₂.obj ⟶ R.scheme) (ha : a₂.left ≫ Q.map = q.hom.left ≫ f.left) :
    ((moduli).obj U).map q.op (R.classOfMap Q t ht hD S f) = (forget).app _ (R.cls S₂ a₂) := by
  let π₁ := (R.pullbackTestπ Q t S f).hom.left
  let : IsLocallyNoetherian (Over.mk (pullback.snd π₁ q.hom.left ≫ S₂.obj.hom)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π₁ q.hom.left)
  let WT : DisBases := noetherianCMTest D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality
    (Over.mk (pullback.snd π₁ q.hom.left ≫ S₂.obj.hom))
  let w₂ : WT ⟶ S₂ := ObjectProperty.homMk (Over.homMk (pullback.snd π₁ q.hom.left) rfl)
  let w₁ : WT ⟶ R.pullbackTest Q t S f :=
    ObjectProperty.homMk (Over.homMk (pullback.fst π₁ q.hom.left) (by
      change pullback.fst π₁ q.hom.left ≫ (π₁ ≫ S.obj.hom) =
        pullback.snd π₁ q.hom.left ≫ S₂.obj.hom
      rw [← Category.assoc, pullback.condition, Category.assoc]
      congr 1
      exact Over.w q.hom))
  have : Etale w₂.hom.left := inferInstanceAs (Etale (pullback.snd π₁ q.hom.left))
  have : Surjective w₂.hom.left := inferInstanceAs (Surjective (pullback.snd π₁ q.hom.left))
  have hw : w₁ ≫ R.pullbackTestπ Q t S f = w₂ ≫ q := by
    apply ObjectProperty.hom_ext
    ext
    exact pullback.condition
  apply map_injective_of_etale hD U w₂
  have hK : (w₁.hom ≫ R.pullbackTestPt Q t ht S f).left ≫ Q.map =
      (w₂.hom ≫ a₂).left ≫ Q.map := by
    change pullback.fst π₁ q.hom.left ≫ (pullback.snd f.left Q.map ≫ Q.map) =
      pullback.snd π₁ q.hom.left ≫ (a₂.left ≫ Q.map)
    calc pullback.fst π₁ q.hom.left ≫ (pullback.snd f.left Q.map ≫ Q.map)
        = pullback.fst π₁ q.hom.left ≫ (pullback.fst f.left Q.map ≫ f.left) :=
          congrArg (_ ≫ ·) pullback.condition.symm
      _ = (pullback.fst π₁ q.hom.left ≫ π₁) ≫ f.left := (Category.assoc _ _ _).symm
      _ = (pullback.snd π₁ q.hom.left ≫ q.hom.left) ≫ f.left :=
          congrArg (· ≫ f.left) pullback.condition
      _ = pullback.snd π₁ q.hom.left ≫ (q.hom.left ≫ f.left) := Category.assoc _ _ _
      _ = pullback.snd π₁ q.hom.left ≫ (a₂.left ≫ Q.map) := congrArg (_ ≫ ·) ha.symm
  calc ((moduli).obj U).map w₂.op (((moduli).obj U).map q.op (R.classOfMap Q t ht hD S f))
      = ((moduli).obj U).map (w₂ ≫ q).op (R.classOfMap Q t ht hD S f) :=
        (moduli_map_comp U w₂ q _).symm
    _ = ((moduli).obj U).map (w₁ ≫ R.pullbackTestπ Q t S f).op
          (R.classOfMap Q t ht hD S f) := by rw [hw]
    _ = ((moduli).obj U).map w₁.op (((moduli).obj U).map (R.pullbackTestπ Q t S f).op
          (R.classOfMap Q t ht hD S f)) := moduli_map_comp U _ _ _
    _ = ((moduli).obj U).map w₁.op
          ((forget).app _ (R.cls _ (R.pullbackTestPt Q t ht S f))) := by
        rw [R.classOfMap_spec Q t ht hD S f]
    _ = (forget).app _ (R.cls WT (w₁.hom ≫ R.pullbackTestPt Q t ht S f)) := by
        rw [R.cls_comp]
        exact (NatTrans.naturality_apply _ _ _).symm
    _ = (forget).app _ (R.cls WT (w₂.hom ≫ a₂)) := R.forget_cls_eq_of_comp_eq Q hD _ _ _ hK
    _ = ((moduli).obj U).map w₂.op ((forget).app _ (R.cls S₂ a₂)) := by
        rw [R.cls_comp]
        exact NatTrans.naturality_apply _ _ _

theorem classOfMap_comp
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    {S S' : DisBases} (k : S' ⟶ S) (f : S.obj ⟶ Over.mk t) :
    R.classOfMap Q t ht hD S' (k.hom ≫ f) =
      ((moduli).obj U).map k.op (R.classOfMap Q t ht hD S f) := by
  apply map_injective_of_etale hD U (R.pullbackTestπ Q t S' (k.hom ≫ f))
  rw [R.classOfMap_spec Q t ht hD S' (k.hom ≫ f), ← moduli_map_comp]
  refine (R.map_classOfMap Q t ht hD S f _ _ ?_).symm
  rw [R.pullbackTestPt_comp_map Q t ht]
  simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

end Quotient

section Lift

variable {U hle} (Q : (R.residualAction U hle).EffectiveQuotient)
  (t : Q.scheme ⟶ Spec (.of F)) (ht : Q.map ≫ t = R.scheme.hom)
  (hL : CMSublevelEtaleLiftStatement D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor)

/-- An étale surjective test morphism with a fine class lifting the pullback of
a given coarse class. -/
structure CoarseLift (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) where
  test : DisBases
  π : test ⟶ S
  cls : ((moduli).obj U').obj (Opposite.op test)
  etale : Etale π.hom.left
  surjective : Surjective π.hom.left
  forget_cls : (forget).app _ cls = ((moduli).obj U).map π.op c

attribute [instance] CoarseLift.etale CoarseLift.surjective

include hL in
/-- A chosen lift, supplied by the étale-local lifting premise. -/
def coarseLift (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) :
    CoarseLift (hle := hle) S c :=
  Classical.choice (by
    obtain ⟨S₁, p, c₁, h₁, h₂, h₃⟩ := hL U' U hle S c
    exact ⟨⟨S₁, p, c₁, h₁, h₂, h₃⟩⟩)

theorem coarseLift_desc_condition
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ (coarseLift (hle := hle) hL S c).test.obj.left)
    (hg : g₁ ≫ (coarseLift (hle := hle) hL S c).π.hom.left =
      g₂ ≫ (coarseLift (hle := hle) hL S c).π.hom.left) :
    g₁ ≫ ((R.pt _ (coarseLift (hle := hle) hL S c).cls).left ≫ Q.map) =
      g₂ ≫ ((R.pt _ (coarseLift (hle := hle) hL S c).cls).left ≫ Q.map) := by
  let ℓ := coarseLift (hle := hle) hL S c
  let p := ℓ.π.hom.left
  let a₁ := R.pt _ ℓ.cls
  let : IsLocallyNoetherian (Over.mk (pullback.fst p p ≫ ℓ.test.obj.hom)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst p p)
  let KT : DisBases := noetherianCMTest D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (Over.mk (pullback.fst p p ≫ ℓ.test.obj.hom))
  let fstT : KT ⟶ ℓ.test := ObjectProperty.homMk (Over.homMk (pullback.fst p p) rfl)
  let sndT : KT ⟶ ℓ.test := ObjectProperty.homMk (Over.homMk (pullback.snd p p) (by
    change pullback.snd p p ≫ ℓ.test.obj.hom = pullback.fst p p ≫ ℓ.test.obj.hom
    calc pullback.snd p p ≫ ℓ.test.obj.hom = pullback.snd p p ≫ (p ≫ S.obj.hom) :=
          congrArg (_ ≫ ·) (Over.w ℓ.π.hom).symm
      _ = (pullback.snd p p ≫ p) ≫ S.obj.hom := (Category.assoc _ _ _).symm
      _ = (pullback.fst p p ≫ p) ≫ S.obj.hom := congrArg (· ≫ S.obj.hom) pullback.condition.symm
      _ = pullback.fst p p ≫ (p ≫ S.obj.hom) := Category.assoc _ _ _
      _ = pullback.fst p p ≫ ℓ.test.obj.hom := congrArg (_ ≫ ·) (Over.w ℓ.π.hom)))
  have hcomm : fstT ≫ ℓ.π = sndT ≫ ℓ.π := by
    apply ObjectProperty.hom_ext
    ext
    exact pullback.condition
  have hforget : (forget).app _ (R.cls KT (fstT.hom ≫ a₁)) =
      (forget).app _ (R.cls KT (sndT.hom ≫ a₁)) := by
    calc (forget).app _ (R.cls KT (fstT.hom ≫ a₁))
        = ((moduli).obj U).map fstT.op ((forget).app _ (R.cls ℓ.test a₁)) := by
          rw [R.cls_comp]
          exact NatTrans.naturality_apply _ _ _
      _ = ((moduli).obj U).map fstT.op (((moduli).obj U).map ℓ.π.op c) := by
          rw [R.cls_pt, ℓ.forget_cls]
      _ = ((moduli).obj U).map (fstT ≫ ℓ.π).op c := (moduli_map_comp U _ _ _).symm
      _ = ((moduli).obj U).map (sndT ≫ ℓ.π).op c := by rw [hcomm]
      _ = ((moduli).obj U).map sndT.op (((moduli).obj U).map ℓ.π.op c) :=
          moduli_map_comp U _ _ _
      _ = ((moduli).obj U).map sndT.op ((forget).app _ (R.cls ℓ.test a₁)) := by
          rw [R.cls_pt, ℓ.forget_cls]
      _ = (forget).app _ (R.cls KT (sndT.hom ≫ a₁)) := by
          rw [R.cls_comp]
          exact (NatTrans.naturality_apply _ _ _).symm
  have key := R.comp_eq_of_forget_cls_eq Q hO KT _ _ hforget
  have key' : pullback.fst p p ≫ (a₁.left ≫ Q.map) = pullback.snd p p ≫ (a₁.left ≫ Q.map) :=
    (Category.assoc _ _ _).symm.trans (key.trans (Category.assoc _ _ _))
  calc g₁ ≫ (a₁.left ≫ Q.map)
      = (pullback.lift g₁ g₂ hg ≫ pullback.fst p p) ≫ (a₁.left ≫ Q.map) := by
        rw [pullback.lift_fst]
    _ = pullback.lift g₁ g₂ hg ≫ (pullback.fst p p ≫ (a₁.left ≫ Q.map)) :=
        Category.assoc _ _ _
    _ = pullback.lift g₁ g₂ hg ≫ (pullback.snd p p ≫ (a₁.left ≫ Q.map)) := by rw [key']
    _ = (pullback.lift g₁ g₂ hg ≫ pullback.snd p p) ≫ (a₁.left ≫ Q.map) :=
        (Category.assoc _ _ _).symm
    _ = g₂ ≫ (a₁.left ≫ Q.map) := by rw [pullback.lift_snd]

/-- The point of the quotient attached to a coarse class: descend the image of
a fine lift along the étale surjective lifting map. -/
def mapOfClass
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) : S.obj ⟶ Over.mk t :=
  Over.homMk (EffectiveEpi.desc (coarseLift (hle := hle) hL S c).π.hom.left
      ((R.pt _ (coarseLift (hle := hle) hL S c).cls).left ≫ Q.map)
      (fun g₁ g₂ hg => R.coarseLift_desc_condition Q hL hO S c g₁ g₂ hg)) (by
    change EffectiveEpi.desc _ _ _ ≫ t = S.obj.hom
    apply (cancel_epi (coarseLift (hle := hle) hL S c).π.hom.left).mp
    rw [← Category.assoc, EffectiveEpi.fac, Category.assoc, ht]
    exact (Over.w (R.pt _ (coarseLift (hle := hle) hL S c).cls)).trans
      (Over.w (coarseLift (hle := hle) hL S c).π.hom).symm)

theorem π_comp_mapOfClass
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) :
    (coarseLift (hle := hle) hL S c).π.hom.left ≫ (R.mapOfClass Q t ht hL hO S c).left =
      (R.pt _ (coarseLift (hle := hle) hL S c).cls).left ≫ Q.map :=
  EffectiveEpi.fac _ _ (fun g₁ g₂ hg => R.coarseLift_desc_condition Q hL hO S c g₁ g₂ hg)

/-- Characterization of `mapOfClass` by any fine lift of a pullback of the class. -/
theorem mapOfClass_spec
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) {S₂ : DisBases} (q : S₂ ⟶ S)
    (c₂ : ((moduli).obj U').obj (Opposite.op S₂))
    (hc : (forget).app _ c₂ = ((moduli).obj U).map q.op c) :
    q.hom.left ≫ (R.mapOfClass Q t ht hL hO S c).left = (R.pt S₂ c₂).left ≫ Q.map := by
  let ℓ := coarseLift (hle := hle) hL S c
  let p := ℓ.π.hom.left
  let a₁ := R.pt _ ℓ.cls
  let a₂ := R.pt S₂ c₂
  let : IsLocallyNoetherian (Over.mk (pullback.snd p q.hom.left ≫ S₂.obj.hom)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p q.hom.left)
  let WT : DisBases := noetherianCMTest D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (Over.mk (pullback.snd p q.hom.left ≫ S₂.obj.hom))
  let w₂ : WT ⟶ S₂ := ObjectProperty.homMk (Over.homMk (pullback.snd p q.hom.left) rfl)
  let w₁ : WT ⟶ ℓ.test := ObjectProperty.homMk (Over.homMk (pullback.fst p q.hom.left) (by
    change pullback.fst p q.hom.left ≫ ℓ.test.obj.hom = pullback.snd p q.hom.left ≫ S₂.obj.hom
    calc pullback.fst p q.hom.left ≫ ℓ.test.obj.hom
        = pullback.fst p q.hom.left ≫ (p ≫ S.obj.hom) :=
          congrArg (_ ≫ ·) (Over.w ℓ.π.hom).symm
      _ = (pullback.fst p q.hom.left ≫ p) ≫ S.obj.hom := (Category.assoc _ _ _).symm
      _ = (pullback.snd p q.hom.left ≫ q.hom.left) ≫ S.obj.hom :=
          congrArg (· ≫ S.obj.hom) pullback.condition
      _ = pullback.snd p q.hom.left ≫ (q.hom.left ≫ S.obj.hom) := Category.assoc _ _ _
      _ = pullback.snd p q.hom.left ≫ S₂.obj.hom := congrArg (_ ≫ ·) (Over.w q.hom)))
  have hcomm : w₁ ≫ ℓ.π = w₂ ≫ q := by
    apply ObjectProperty.hom_ext
    ext
    exact pullback.condition
  have hforget : (forget).app _ (R.cls WT (w₁.hom ≫ a₁)) =
      (forget).app _ (R.cls WT (w₂.hom ≫ a₂)) := by
    calc (forget).app _ (R.cls WT (w₁.hom ≫ a₁))
        = ((moduli).obj U).map w₁.op ((forget).app _ (R.cls ℓ.test a₁)) := by
          rw [R.cls_comp]
          exact NatTrans.naturality_apply _ _ _
      _ = ((moduli).obj U).map w₁.op (((moduli).obj U).map ℓ.π.op c) := by
          rw [R.cls_pt, ℓ.forget_cls]
      _ = ((moduli).obj U).map (w₁ ≫ ℓ.π).op c := (moduli_map_comp U _ _ _).symm
      _ = ((moduli).obj U).map (w₂ ≫ q).op c := by rw [hcomm]
      _ = ((moduli).obj U).map w₂.op (((moduli).obj U).map q.op c) :=
          moduli_map_comp U _ _ _
      _ = ((moduli).obj U).map w₂.op ((forget).app _ (R.cls S₂ a₂)) := by
          rw [R.cls_pt, hc]
      _ = (forget).app _ (R.cls WT (w₂.hom ≫ a₂)) := by
          rw [R.cls_comp]
          exact (NatTrans.naturality_apply _ _ _).symm
  have key := R.comp_eq_of_forget_cls_eq Q hO WT _ _ hforget
  apply (cancel_epi (pullback.snd p q.hom.left)).mp
  calc pullback.snd p q.hom.left ≫ q.hom.left ≫ (R.mapOfClass Q t ht hL hO S c).left
      = (pullback.snd p q.hom.left ≫ q.hom.left) ≫ (R.mapOfClass Q t ht hL hO S c).left :=
        (Category.assoc _ _ _).symm
    _ = (pullback.fst p q.hom.left ≫ p) ≫ (R.mapOfClass Q t ht hL hO S c).left :=
        congrArg (· ≫ _) pullback.condition.symm
    _ = pullback.fst p q.hom.left ≫ (p ≫ (R.mapOfClass Q t ht hL hO S c).left) :=
        Category.assoc _ _ _
    _ = pullback.fst p q.hom.left ≫ (a₁.left ≫ Q.map) :=
        congrArg (_ ≫ ·) (R.π_comp_mapOfClass Q t ht hL hO S c)
    _ = (pullback.fst p q.hom.left ≫ a₁.left) ≫ Q.map := (Category.assoc _ _ _).symm
    _ = (pullback.snd p q.hom.left ≫ a₂.left) ≫ Q.map := key
    _ = pullback.snd p q.hom.left ≫ a₂.left ≫ Q.map := Category.assoc _ _ _

theorem mapOfClass_classOfMap
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (f : S.obj ⟶ Over.mk t) :
    R.mapOfClass Q t ht hL hO S (R.classOfMap Q t ht hD S f) = f := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (R.pullbackTestπ Q t S f).hom.left).mp
  rw [R.mapOfClass_spec Q t ht hL hO S _ (R.pullbackTestπ Q t S f) _
    (R.classOfMap_spec Q t ht hD S f).symm, R.pt_cls]
  exact R.pullbackTestPt_comp_map Q t ht S f

theorem classOfMap_mapOfClass
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (S : DisBases) (c : ((moduli).obj U).obj (Opposite.op S)) :
    R.classOfMap Q t ht hD S (R.mapOfClass Q t ht hL hO S c) = c := by
  apply map_injective_of_etale hD U (coarseLift (hle := hle) hL S c).π
  rw [R.map_classOfMap Q t ht hD S _ (coarseLift (hle := hle) hL S c).π _
    (R.π_comp_mapOfClass Q t ht hL hO S c).symm, R.cls_pt,
    (coarseLift (hle := hle) hL S c).forget_cls]

/-- The quotient represents the coarse class presheaf on admissible tests. -/
def quotientRepresents
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :
    admissibleTestPoints D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (Over.mk t) ≅ (moduli).obj U :=
  NatIso.ofComponents
    (fun S => Equiv.toIso
      { toFun := fun f => R.classOfMap Q t ht hD S.unop (ULift.down f)
        invFun := fun c => ULift.up (R.mapOfClass Q t ht hL hO S.unop c)
        left_inv := fun f => congrArg ULift.up (R.mapOfClass_classOfMap Q t ht hL hD hO _ _)
        right_inv := fun c => R.classOfMap_mapOfClass Q t ht hL hD hO _ c })
    (fun {S S'} k => by
      ext f
      exact R.classOfMap_comp Q t ht hD k.unop (ULift.down f))

end Lift


end CMLevelQuasiProjectiveRepresentation

end Action

end Representation

/-- Normal-quotient descent of quasi-projective representability follows from
quotients of quasi-projective schemes by free finite group actions, étale
descent and étale-local lifting of the normalized classes, and the description
of fibres of the forgetting transition on connected tests. Freeness of the
residual action comes from the Library's small-level rigidity theorem. -/
theorem cmQuasiProjectiveNormalQuotientStatement_of_premises
    (hG : FiniteFreeQuasiProjectiveQuotientStatement)
    (hD : CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hL : CMSublevelEtaleLiftStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hO : CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :
    CMQuasiProjectiveNormalQuotientStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  intro U' U hle hnormal hrep
  obtain ⟨R⟩ := hrep
  have := smallCMResidualGroup_finite D U U'
  obtain ⟨Q, t, M, j', hj', hj't, ht⟩ := hG F R.scheme.left R.scheme.hom R.dim R.embedding
    R.isImmersion R.embedding_comp (SmallCMResidualGroup D U U') (R.residualAction U hle)
    (R.residualAction_over U hle)
  exact ⟨{ scheme := Over.mk t
           dim := M
           embedding := j'
           isImmersion := hj'
           embedding_comp := hj't
           represents := R.quotientRepresents Q t ht hL hD hO }⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
