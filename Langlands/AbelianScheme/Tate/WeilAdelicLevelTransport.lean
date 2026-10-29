import Langlands.AbelianScheme.Tate.WeilFrameMonodromy
import Langlands.Shimura.PEL.FormIsoTransport

/-! # Path transport and level maps for actual Weil-compatible adelic frames -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (geometricCompatibility : RationalWeilGeometricTransportStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ

local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ

local notation "rightActionAt" => weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ

local notation "leftActionAt" => weilAdelicFrameMonodromyAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap h i V ψ

local notation "commAt" => weilAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA
  MA evaluationA polarizationMap h i V ψ

local notation "Level" => WeilAdelicLevel preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA
  MA evaluationA polarizationMap h i V ψ

/-- Actual Tate and twist path transport restricts to Weil-compatible frames. -/
def weilAdelicFrameTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Frame s ≃ Frame t := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk t) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk t).left, ⊤) (fun _ => True) h
  exact FormIso.transport (finiteAdeleAlgebraTransport htor A (fun _ => True) hu h i p)
    (TateTwist.Geometry.sectionFiniteAdeleTransport (fun _ => True)
      (hμfin := hμfin) (hμet := hμet) h p)
    (fun x y => by
      simpa only [adelicWeilAlongHomBilinearMap_apply,
        TateTwist.Geometry.sectionFiniteAdeleTransport_apply,
        finiteAdeleAlgebraTransport_apply] using
        ((geometricCompatibility preservation composition unitCoherence associativity
          comparison symmetry stability compatibility S A hA geometryA MA evaluationA
          Ω Ω' s t hs ht htor (fun _ => True) hu hμfin hμet p).2
          polarizationMap x y).symm)

local notation "frameTransport" => weilAdelicFrameTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu

@[simp] theorem weilAdelicFrameTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frame s)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    (frameTransport p eta).1 x =
      rationalTransport htor A (fun _ => True) hu p (eta.1 x) := rfl

@[simp] theorem weilAdelicFrameTransport_refl (eta : Frame s) :
    frameTransport (Iso.refl (fiberFunctor s hs)) eta = eta := by
  apply Subtype.ext
  ext x
  exact rationalTransport_refl htor A (fun _ => True) hu (eta.1 x)

theorem weilAdelicFrameTransport_trans
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr)
    (eta : Frame s) :
    frameTransport (p ≪≫ q) eta = frameTransport q (frameTransport p eta) := by
  apply Subtype.ext
  ext x
  exact rationalTransport_trans htor A (fun _ => True) hu p q (eta.1 x)

theorem weilAdelicFrameTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (frameTransport p).symm = frameTransport p.symm := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  rfl

/-- Source precomposition commutes with geometric path transport. -/
theorem weilAdelicFrameTransport_right
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frame s) (g : G) :
    letI := rightActionAt s
    letI := rightActionAt t
    frameTransport p (right eta g) = right (frameTransport p eta) g := by
  apply Subtype.ext
  ext x
  rfl

/-- Path transport intertwines the actual geometric actions by path conjugation. -/
theorem weilAdelicFrameTransport_monodromy
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : FundamentalGroup s hs)
    (eta : Frame s) :
    letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
    letI := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
    frameTransport p (g • eta) = pathConjugation p g • frameTransport p eta := by
  apply Subtype.ext
  ext x
  exact rationalTransport_monodromy htor A (fun _ => True) hu p g (eta.1 x)

/-- Geometric path transport on the actual fixed Weil-compatible level orbits. -/
def weilAdelicLevelTransport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level s hs htor hu U ≃ Level t ht htor hu U := by
  letI := rightActionAt s
  letI := rightActionAt t
  letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.equiv U (pathConjugation p) (frameTransport p)
    (weilAdelicFrameTransport_right preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ htor hu p)
    (weilAdelicFrameTransport_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ htor hu p)

local notation "levelTransport" => weilAdelicLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu

/-- Dependence on the path vanishes on fixed orbit classes. -/
theorem weilAdelicLevelTransport_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    levelTransport U p = levelTransport U q := by
  let := rightActionAt s
  let := rightActionAt t
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  symm
  apply InvariantOrbit.equiv_eq_of_left U (pathConjugation p) (pathConjugation q)
    (frameTransport p) (frameTransport q) _ _ _ _ (p.symm ≪≫ q)
  intro eta
  apply Subtype.ext
  ext x
  exact rationalTransport_change_path htor A (fun _ => True) hu p q (eta.1 x)

@[simp] theorem weilAdelicLevelTransport_refl (U : Subgroup G) :
    levelTransport U (Iso.refl (fiberFunctor s hs)) =
      Equiv.refl (Level s hs htor hu U) := by
  let := rightActionAt s
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilAdelicFrameTransport_refl preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
        evaluationA polarizationMap h i V ψ htor hu (hs := hs) eta)

theorem weilAdelicLevelTransport_trans (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    levelTransport U (p ≪≫ q) = (levelTransport U p).trans (levelTransport U q) := by
  let := rightActionAt s
  let := rightActionAt t
  let := rightActionAt r
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt r hr htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt r hr htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilAdelicFrameTransport_trans preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
        evaluationA polarizationMap h i V ψ htor hu p q eta)

theorem weilAdelicLevelTransport_symm (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (levelTransport U p).symm = levelTransport U p.symm := by
  let := rightActionAt s
  let := rightActionAt t
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta)
        (weilAdelicFrameTransport_symm preservation composition unitCoherence associativity
          comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
          evaluationA polarizationMap h i V ψ htor hu p))

variable {U U' U'' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)}

/-- Right Hecke translation, with the source-to-target subgroup condition. -/
def weilAdelicLevelTranslate (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    Level s hs htor hu U → Level s hs htor hu U' := by
  letI := rightActionAt s
  letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate g hg

local notation "levelTranslate" => weilAdelicLevelTranslate preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu

/-- Forgetting a finer subgroup level. -/
def weilAdelicLevelForget (hU : U ≤ U') :
    Level s hs htor hu U → Level s hs htor hu U' :=
  levelTranslate 1 (by intro u hu; simpa using hU hu)

local notation "levelForget" => weilAdelicLevelForget preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu

@[simp] theorem weilAdelicLevelTranslate_one (x : Level s hs htor hu U) :
    levelTranslate 1 (by intro u hu; simpa using hu) x = x := by
  let := rightActionAt s
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate_one x

/-- Successive right translations by g and k translate by g*k. -/
theorem weilAdelicLevelTranslate_comp (g k : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (hk : ∀ u ∈ U', k⁻¹ * u * k ∈ U'')
    (x : Level s hs htor hu U) :
    levelTranslate k hk (levelTranslate g hg x) =
      levelTranslate (g * k) (by intro u hu; simpa [mul_assoc] using hk _ (hg u hu)) x := by
  let := rightActionAt s
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate_comp g k hg hk x

@[simp] theorem weilAdelicLevelForget_refl (x : Level s hs htor hu U) :
    levelForget (le_refl U) x = x :=
  weilAdelicLevelTranslate_one preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ htor hu x

theorem weilAdelicLevelForget_comp (hU : U ≤ U') (hU' : U' ≤ U'')
    (x : Level s hs htor hu U) :
    levelForget hU' (levelForget hU x) = levelForget (hU.trans hU') x := by
  let := rightActionAt s
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  simpa only [weilAdelicLevelForget, weilAdelicLevelTranslate, one_mul] using
    (InvariantOrbit.translate_comp (1 : G) 1
      (by intro u hu; simpa using hU hu) (by intro u hu; simpa using hU' hu) x)

/-- Geometric path transport commutes with right Hecke translation. -/
theorem weilAdelicLevelTransport_translate
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (x : Level s hs htor hu U) :
    levelTransport U' p (levelTranslate g hg x) =
      levelTranslate g hg (levelTransport U p x) := by
  let := rightActionAt s
  let := rightActionAt t
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.map_translate (pathConjugation p) (frameTransport p)
    (weilAdelicFrameTransport_right preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ htor hu p)
    (weilAdelicFrameTransport_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ htor hu p) g hg x

theorem weilAdelicLevelTransport_forget
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (hU : U ≤ U')
    (x : Level s hs htor hu U) :
    levelTransport U' p (levelForget hU x) = levelForget hU (levelTransport U p x) :=
  weilAdelicLevelTransport_translate preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ htor hu p 1 _ x

end Langlands.AbelianScheme.Tate
