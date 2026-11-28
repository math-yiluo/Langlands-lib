import Langlands.Shimura.PEL.HarrisTaylorCMArtinianPolarizedLiftingStatement
import Langlands.Shimura.PEL.HarrisTaylorCMDvrGenericTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Langlands.AbelianScheme.RationalActionBasisLift
import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.PolarizationInfinitesimalReflection
import Langlands.AlgebraicGeometry.Picard.RosatiBaseChangeReflection

/-! # Assembling a polarized rational lift from actual geometric lifts -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.PolarizedFiniteLevel

section ChangeDual

variable (P : Prerequisites.{0}) {S T : Scheme.{0}} (b : T ⟶ S) {B : AbelianScheme S}
  (U : DualWitness B) (V W : DualWitness ((baseChange b).obj B))

private theorem pullbackMap_change_dual (lam : B ⟶ U.dual P) :
    U.pullbackMap P b W lam =
      U.pullbackMap P b V lam ≫ W.map P V (𝟙 ((baseChange b).obj B)) := by
  have h := dualAbelianBaseChangeNaturality P.preservation P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility
    S T b B B U.hasDual U.geometry U.inverseBundle U.evaluation U.hasDual U.geometry
    U.inverseBundle U.evaluation W.hasDual W.geometry W.inverseBundle W.evaluation
    V.hasDual V.geometry V.inverseBundle V.evaluation (𝟙 B)
  rw [dualAbelianSchemeMapFromEvaluation_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id] at h
  change (baseChange b).map lam ≫ _ = ((baseChange b).map lam ≫ _) ≫ _
  rw [Category.assoc]
  exact congrArg ((baseChange b).map lam ≫ ·) h

end ChangeDual

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
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

local notation "Pos" base => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := base)
local notation "P" => Prerequisites.mk preservation square universality stability composition
  unitCoherence associativity comparison symmetry dualAbelianBaseChange polarizationBaseChange
local notation "isometric" => PositivePolarizedActionIsometricReduction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

variable {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]

/-- It suffices to lift the actual polarization and integral multiples of the
rational action of basis elements on a common lift of the abelian scheme. -/
theorem positivePolarizedAction_lifts_of_basis_lifts
    (b : T ⟶ S) [Surjective b] (Y : Pos T) (B : AbelianScheme S)
    {I : Type} (basis : Module.Basis I ℚ A)
    (e : (baseChange b).obj B ≅ (letI := auxiliaryStarRing D C; Y.actionObj.abelianScheme))
    (U : DualWitness B) (V : DualWitness ((baseChange b).obj B))
    (lam : B ⟶ U.dual P) (hpol : U.IsPolarization P lam) :
    letI := auxiliaryStarRing D C
    let Z := transportDvrGenericPolarizedAction P Y ((baseChange b).obj B) V e
    U.pullbackMap P b V lam = Z.polarization →
    (∀ i, ∃ m : ℤ, m ≠ 0 ∧ ∃ f : B ⟶ B,
      homToHom0 ((baseChange b).map f) = m • (Z.actionObj.action (basis i)).asHom) →
    ∃ X : Pos S, ∃ k : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj,
      isometric b X Y k := by
  classical
  let := auxiliaryStarRing D C
  let Z := transportDvrGenericPolarizedAction P Y ((baseChange b).obj B) V e
  let eZ := transportDvrGenericActionIso P Y ((baseChange b).obj B) V e
  change U.pullbackMap P b V lam = Z.polarization →
    (∀ i, ∃ m : ℤ, m ≠ 0 ∧ ∃ f : B ⟶ B,
      homToHom0 ((baseChange b).map f) = m • (Z.actionObj.action (basis i)).asHom) → _
  intro hlam hf
  choose m hm f hmap using hf
  obtain ⟨i, hi⟩ := exists_rationalAction_of_basis_lifts b B basis Z.actionObj.action m hm f hmap
  let addU := relativeDualSchemeMapAdditivity preservation stability S B B U.hasDual U.hasDual
  let addV := relativeDualSchemeMapAdditivity preservation stability T _ _ V.hasDual V.hasDual
  have hcompat : IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability U.hasDual addU U.inverseBundle U.evaluation U.geometry
      i.toRingHom (homToHom0 lam) := by
    apply IsInvolutionCompatible.of_surjective_baseChange P b U V addU addV
    change IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability V.hasDual addV V.inverseBundle V.evaluation V.geometry
      ((rationalBaseChangeEnd b B).comp i).toRingHom
      (rationalDualBaseChangeHom preservation stability composition unitCoherence associativity
        comparison symmetry universality dualAbelianBaseChange b B U.hasDual U.geometry
        U.inverseBundle U.evaluation V.hasDual V.geometry V.inverseBundle V.evaluation
        (homToHom0 lam))
    rw [rationalDualBaseChangeHom_homToHom0, hi]
    have heq : dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality dualAbelianBaseChange b B U.hasDual
        U.geometry U.inverseBundle U.evaluation V.hasDual V.geometry V.inverseBundle
        V.evaluation lam = Z.polarization := hlam
    rw [heq]
    exact Z.involutionCompatible
  let X : Pos S :=
    { actionObj := RationalAlgebraAction.of B i
      hasDual := U.hasDual
      geometry := U.geometry
      inversePoincare := U.inverseBundle
      evaluation := U.evaluation
      dualEndAdditivity := addU
      polarization := lam
      isPolarization := hpol
      faithful := by
        intro a a' ha
        apply Z.faithful
        exact (congrFun (congrArg DFunLike.coe hi) a).symm.trans
          ((congrArg (rationalBaseChangeEnd b B) ha).trans
            (congrFun (congrArg DFunLike.coe hi) a'))
      involutionCompatible := hcompat }
  let k : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj :=
    RationalAlgebraAction.isoMk ((rationalization T).mapIso e) (fun a => by
      have h0 := RationalAlgebraAction.intertwines eZ.hom a
      change comp0 _ _ _ (((rationalBaseChangeEnd b B).comp i) a).asHom (homToHom0 e.hom) =
        comp0 _ _ _ (homToHom0 e.hom) (Y.actionObj.action a).asHom
      rw [hi]
      exact h0)
  refine ⟨X, k, ?_⟩
  intro W
  let W' : DualWitness ((baseChange b).obj B) :=
    ⟨W.hasDual, W.geometry, W.inversePoincare, W.evaluation⟩
  let WY := Y.dualWitness P
  have hW : U.pullbackMap P b W' lam = DualWitness.transportMap P e W' WY Y.polarization := by
    calc
      U.pullbackMap P b W' lam =
          U.pullbackMap P b V lam ≫ W'.map P V (𝟙 _) :=
        pullbackMap_change_dual P b U V W' lam
      _ = DualWitness.transportMap P e V WY Y.polarization ≫ W'.map P V (𝟙 _) := by
        exact congrArg (· ≫ W'.map P V (𝟙 _)) hlam
      _ = DualWitness.transportMap P e W' WY Y.polarization := by
        simp only [DualWitness.transportMap, Category.assoc]
        rw [← W'.map_comp P V WY, Category.id_comp]
  change IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
    comparison symmetry stability W'.hasDual WY.hasDual W'.geometry WY.geometry W'.inverseBundle
    W'.evaluation WY.inverseBundle WY.evaluation
    (relativeDualSchemeMapAdditivity preservation stability T _ _ W'.hasDual WY.hasDual)
    1 (homToHom0 e.hom) (homToHom0 (U.pullbackMap P b W' lam)) (homToHom0 Y.polarization)
  unfold IsRationalDualPullbackMultiple
  rw [one_smul, ← homToHom0_integralDualPullback]
  exact congrArg homToHom0 hW.symm

/-- The required geometric input can be expressed as ordinary lifting of a
finite family of integral maps and of the original integral polarization. -/
theorem positivePolarizedAction_lifts_of_integral_map_lifts
    (b : T ⟶ S) [Surjective b] (Y : Pos T)
    {I : Type} [Finite I] (basis : Module.Basis I ℚ A) :
    letI := auxiliaryStarRing D C
    (∀ (m : ℤ), m ≠ 0 → ∀ (g : I → (Y.actionObj.abelianScheme ⟶ Y.actionObj.abelianScheme)),
      (∀ i, homToHom0 (g i) = m • (Y.actionObj.action (basis i)).asHom) →
      ∃ (B : AbelianScheme S) (e : (baseChange b).obj B ≅ Y.actionObj.abelianScheme)
        (U : DualWitness B) (V : DualWitness ((baseChange b).obj B))
        (lam : B ⟶ U.dual P),
        U.IsPolarization P lam ∧
          U.pullbackMap P b V lam = DualWitness.transportMap P e V (Y.dualWitness P)
            Y.polarization ∧
          ∃ f : I → (B ⟶ B), ∀ i, (baseChange b).map (f i) ≫ e.hom = e.hom ≫ g i) →
    ∃ X : Pos S, ∃ k : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj,
      isometric b X Y k := by
  let := auxiliaryStarRing D C
  intro h
  obtain ⟨m, hm, g, hg⟩ := Rationalization.exists_common_integral_multiple
    (fun i => (Y.actionObj.action (basis i)).asHom)
  obtain ⟨B, e, U, V, lam, hpol, hlam, f, hf⟩ := h m hm g hg
  let Z := transportDvrGenericPolarizedAction P Y ((baseChange b).obj B) V e
  let eZ := transportDvrGenericActionIso P Y ((baseChange b).obj B) V e
  apply positivePolarizedAction_lifts_of_basis_lifts D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b Y B basis e U V lam hpol
  · exact hlam
  · intro i
    refine ⟨m, hm, f i, ?_⟩
    let e₀ := (rationalization T).mapIso e
    have hconj : comp0 _ _ _ (Z.actionObj.action (basis i)).asHom e₀.hom =
        comp0 _ _ _ e₀.hom (Y.actionObj.action (basis i)).asHom :=
      RationalAlgebraAction.intertwines eZ.hom (basis i)
    let B₀ := (baseChange b).obj B
    let Y₀ := Y.actionObj.abelianScheme
    let precompose := comp0 B₀ Y₀ Y₀ (homToHom0 e.hom)
    let postcompose := (comp0 B₀ B₀ Y₀).flip (homToHom0 e.hom)
    apply (cancel_mono e₀.hom).mp
    change comp0 _ _ _ (homToHom0 ((baseChange b).map (f i))) (homToHom0 e.hom) =
      comp0 _ _ _ (m • (Z.actionObj.action (basis i)).asHom) (homToHom0 e.hom)
    calc
      _ = homToHom0 ((baseChange b).map (f i) ≫ e.hom) := comp0_homToHom0 _ _
      _ = homToHom0 (e.hom ≫ g i) := congrArg homToHom0 (hf i)
      _ = comp0 _ _ _ e₀.hom (homToHom0 (g i)) := (comp0_homToHom0 _ _).symm
      _ = m • comp0 _ _ _ e₀.hom (Y.actionObj.action (basis i)).asHom := by
        exact (congrArg precompose (hg i)).trans (map_zsmul precompose m _)
      _ = _ := (congrArg (m • ·) hconj.symm).trans (map_zsmul postcompose m _).symm

/-- Across an elementary extension, the polarization premise can be stated
as a lift of the original homomorphism to the actual dual. -/
theorem positivePolarizedAction_lifts_of_integral_map_lifts_elementary
    {R' R : Type} [CommRing R'] [CommRing R] [IsLocalRing R'] [IsLocalRing R]
    (φ : R' →+* R) (hφ : Function.Surjective φ)
    (hker : IsLocalRing.maximalIdeal R' * RingHom.ker φ = ⊥)
    (Y : Pos (Spec (CommRingCat.of R))) {I : Type} [Finite I] (basis : Module.Basis I ℚ A) :
    letI := auxiliaryStarRing D C
    let b := Spec.map (CommRingCat.ofHom φ)
    (∀ (m : ℤ), m ≠ 0 → ∀ (g : I → (Y.actionObj.abelianScheme ⟶ Y.actionObj.abelianScheme)),
      (∀ i, homToHom0 (g i) = m • (Y.actionObj.action (basis i)).asHom) →
      ∃ (B : AbelianScheme (Spec (CommRingCat.of R')))
        (e : (baseChange b).obj B ≅ Y.actionObj.abelianScheme)
        (U : DualWitness B) (V : DualWitness ((baseChange b).obj B))
        (lam : B ⟶ U.dual P),
        U.pullbackMap P b V lam = DualWitness.transportMap P e V (Y.dualWitness P)
          Y.polarization ∧
        ∃ f : I → (B ⟶ B), ∀ i, (baseChange b).map (f i) ≫ e.hom = e.hom ≫ g i) →
    ∃ X : Pos (Spec (CommRingCat.of R')),
      ∃ k : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj,
        isometric b X Y k := by
  let := auxiliaryStarRing D C
  let b := Spec.map (CommRingCat.ofHom φ)
  have hsq : RingHom.ker φ * RingHom.ker φ = ⊥ := by
    apply le_bot_iff.mp
    exact (Ideal.mul_mono_left
      (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ))).trans hker.le
  let : Surjective b := specMap_surjective_of_squareZero_ker φ hφ hsq
  dsimp only
  intro h
  apply positivePolarizedAction_lifts_of_integral_map_lifts D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b Y basis
  intro m hm g hg
  obtain ⟨B, e, U, V, lam, hlam, hf⟩ := h m hm g hg
  have hpol : V.IsPolarization P (U.pullbackMap P b V lam) := by
    rw [hlam]
    exact DualWitness.isPolarization_transportMap P e V (Y.dualWitness P)
      Y.polarization Y.isPolarization
  exact ⟨B, e, U, V, lam, U.isPolarization_of_squareZero_reduction P φ hφ hsq V lam hpol,
    hlam, hf⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
