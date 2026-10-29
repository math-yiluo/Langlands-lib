import Langlands.AbelianScheme.Tate.WeilPrimeToFrameMonodromy
import Langlands.Shimura.PEL.FormIsoTransport

/-! # Path transport and level maps for actual Weil-compatible prime-to-modulus frames -/

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
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "Frame" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ

local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ

local notation "rightActionAt" => weilPrimeToAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ

local notation "leftActionAt" => weilPrimeToAdelicFrameMonodromyAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap hAway i V ψ

local notation "commAt" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA
  MA evaluationA polarizationMap hAway i V ψ

local notation "Level" => WeilPrimeToAdelicLevel preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA
  MA evaluationA polarizationMap hAway i V ψ

/-- Actual Tate and twist path transport restricts to Weil-compatible frames. -/
def weilPrimeToAdelicFrameTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Frame s hAway ≃ Frame t hAway := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk t) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk t).left, ⊤) hAway
  exact FormIso.transport (primeToFiniteAdeleAlgebraTransport htor A m hu hAway i p)
    (TateTwist.Geometry.sectionPrimeToFiniteAdeleTransport hAway
      (hμfin := hμfin) (hμet := hμet) p)
    (fun x y => by
      simpa only [awayAdelicWeilAlongHomBilinearMap_apply,
        TateTwist.Geometry.sectionPrimeToFiniteAdeleTransport_apply,
        primeToFiniteAdeleAlgebraTransport_apply] using
        ((geometricCompatibility preservation composition unitCoherence associativity
          comparison symmetry stability compatibility S A hA geometryA MA evaluationA
          Ω Ω' s t hs ht htor (fun n => Nat.Coprime n m) hu hμfin hμet p).2
          polarizationMap x y).symm)

local notation "frameTransport" => weilPrimeToAdelicFrameTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu

@[simp] theorem weilPrimeToAdelicFrameTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frame s hAway)
    (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    (frameTransport p eta).1 x =
      rationalTransport htor A (fun n => Nat.Coprime n m) hu p (eta.1 x) := rfl

@[simp] theorem weilPrimeToAdelicFrameTransport_refl (eta : Frame s hAway) :
    frameTransport (Iso.refl (fiberFunctor s hs)) eta = eta := by
  apply Subtype.ext
  ext x
  exact rationalTransport_refl htor A (fun n => Nat.Coprime n m) hu (eta.1 x)

theorem weilPrimeToAdelicFrameTransport_trans
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr)
    (eta : Frame s hAway) :
    frameTransport (p ≪≫ q) eta = frameTransport q (frameTransport p eta) := by
  apply Subtype.ext
  ext x
  exact rationalTransport_trans htor A (fun n => Nat.Coprime n m) hu p q (eta.1 x)

theorem weilPrimeToAdelicFrameTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (frameTransport p).symm = frameTransport p.symm := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  rfl

/-- Source precomposition commutes with geometric path transport. -/
theorem weilPrimeToAdelicFrameTransport_right
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frame s hAway) (g : G) :
    letI := rightActionAt s hAway
    letI := rightActionAt t hAway
    frameTransport p (right eta g) = right (frameTransport p eta) g := by
  apply Subtype.ext
  ext x
  rfl

/-- Path transport intertwines the actual geometric actions by path conjugation. -/
theorem weilPrimeToAdelicFrameTransport_monodromy
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : FundamentalGroup s hs)
    (eta : Frame s hAway) :
    letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
    letI := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
    frameTransport p (g • eta) = pathConjugation p g • frameTransport p eta := by
  apply Subtype.ext
  ext x
  exact rationalTransport_monodromy htor A (fun n => Nat.Coprime n m) hu p g (eta.1 x)

/-- Geometric path transport on the actual fixed Weil-compatible level orbits. -/
def weilPrimeToAdelicLevelTransport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level s hs htor hu U ≃ Level t ht htor hu U := by
  letI := rightActionAt s hAway
  letI := rightActionAt t hAway
  letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.equiv U (pathConjugation p) (frameTransport p)
    (weilPrimeToAdelicFrameTransport_right preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap hAway i V ψ htor hu p)
    (weilPrimeToAdelicFrameTransport_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap hAway i V ψ htor hu p)

local notation "levelTransport" => weilPrimeToAdelicLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu

/-- Dependence on the path vanishes on fixed orbit classes. -/
theorem weilPrimeToAdelicLevelTransport_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    levelTransport U p = levelTransport U q := by
  let := rightActionAt s hAway
  let := rightActionAt t hAway
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
  exact rationalTransport_change_path htor A (fun n => Nat.Coprime n m) hu p q (eta.1 x)

@[simp] theorem weilPrimeToAdelicLevelTransport_refl (U : Subgroup G) :
    levelTransport U (Iso.refl (fiberFunctor s hs)) =
      Equiv.refl (Level s hs htor hu U) := by
  let := rightActionAt s hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilPrimeToAdelicFrameTransport_refl preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
        evaluationA polarizationMap hAway i V ψ htor hu (hs := hs) eta)

theorem weilPrimeToAdelicLevelTransport_trans (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    levelTransport U (p ≪≫ q) = (levelTransport U p).trans (levelTransport U q) := by
  let := rightActionAt s hAway
  let := rightActionAt t hAway
  let := rightActionAt r hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt r hr htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt r hr htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilPrimeToAdelicFrameTransport_trans preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
        evaluationA polarizationMap hAway i V ψ htor hu p q eta)

theorem weilPrimeToAdelicLevelTransport_symm (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (levelTransport U p).symm = levelTransport U p.symm := by
  let := rightActionAt s hAway
  let := rightActionAt t hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta)
        (weilPrimeToAdelicFrameTransport_symm preservation composition unitCoherence associativity
          comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
          evaluationA polarizationMap hAway i V ψ htor hu p))

variable {U U' U'' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)}

/-- Right Hecke translation, with the source-to-target subgroup condition. -/
def weilPrimeToAdelicLevelTranslate (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    Level s hs htor hu U → Level s hs htor hu U' := by
  letI := rightActionAt s hAway
  letI := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate g hg

local notation "levelTranslate" => weilPrimeToAdelicLevelTranslate preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu

/-- Forgetting a finer subgroup level. -/
def weilPrimeToAdelicLevelForget (hU : U ≤ U') :
    Level s hs htor hu U → Level s hs htor hu U' :=
  levelTranslate 1 (by intro u hu; simpa using hU hu)

local notation "levelForget" => weilPrimeToAdelicLevelForget preservation composition
  unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu

@[simp] theorem weilPrimeToAdelicLevelTranslate_one (x : Level s hs htor hu U) :
    levelTranslate 1 (by intro u hu; simpa using hu) x = x := by
  let := rightActionAt s hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate_one x

/-- Successive right translations by g and k translate by g*k. -/
theorem weilPrimeToAdelicLevelTranslate_comp (g k : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (hk : ∀ u ∈ U', k⁻¹ * u * k ∈ U'')
    (x : Level s hs htor hu U) :
    levelTranslate k hk (levelTranslate g hg x) =
      levelTranslate (g * k) (by intro u hu; simpa [mul_assoc] using hk _ (hg u hu)) x := by
  let := rightActionAt s hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.translate_comp g k hg hk x

@[simp] theorem weilPrimeToAdelicLevelForget_refl (x : Level s hs htor hu U) :
    levelForget (le_refl U) x = x :=
  weilPrimeToAdelicLevelTranslate_one preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap hAway i V ψ htor hu x

theorem weilPrimeToAdelicLevelForget_comp (hU : U ≤ U') (hU' : U' ≤ U'')
    (x : Level s hs htor hu U) :
    levelForget hU' (levelForget hU x) = levelForget (hU.trans hU') x := by
  let := rightActionAt s hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  simpa only [weilPrimeToAdelicLevelForget, weilPrimeToAdelicLevelTranslate, one_mul] using
    (InvariantOrbit.translate_comp (1 : G) 1
      (by intro u hu; simpa using hU hu) (by intro u hu; simpa using hU' hu) x)

/-- Geometric path transport commutes with right Hecke translation. -/
theorem weilPrimeToAdelicLevelTransport_translate
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (x : Level s hs htor hu U) :
    levelTransport U' p (levelTranslate g hg x) =
      levelTranslate g hg (levelTransport U p x) := by
  let := rightActionAt s hAway
  let := rightActionAt t hAway
  let := leftActionAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := leftActionAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commAt t ht htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.map_translate (pathConjugation p) (frameTransport p)
    (weilPrimeToAdelicFrameTransport_right preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap hAway i V ψ htor hu p)
    (weilPrimeToAdelicFrameTransport_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
      evaluationA polarizationMap hAway i V ψ htor hu p) g hg x

theorem weilPrimeToAdelicLevelTransport_forget
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (hU : U ≤ U')
    (x : Level s hs htor hu U) :
    levelTransport U' p (levelForget hU x) = levelForget hU (levelTransport U p x) :=
  weilPrimeToAdelicLevelTransport_translate preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap hAway i V ψ htor hu p 1 _ x

end Langlands.AbelianScheme.Tate
