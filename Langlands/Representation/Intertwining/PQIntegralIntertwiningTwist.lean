import Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements
import Langlands.Representation.Aubert.General.CharacterTwistEquivalences
import Langlands.Representation.Aubert.General.InductionCarrierTransport

/-! # Character multiplication and integral-normalized intertwining -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {F : Type u} [Field F] [TopologicalSpace F] [T2Space F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance characterAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

local instance characterLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable (eta : SmoothCharacter ℂ (rationalPoints G))
  (nu : SmoothCharacter ℂ (rationalPoints M))
  (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M))

set_option quotPrecheck false in
local notation "orbit" => σ.twist nu.toMonoidHom nu.isOpen_ker
local notation "induced" => leviInductionFunctor p l r hp hr hl hmul

set_option maxHeartbeats 600000 in
/-- Multiplication of an induced function by the ambient character gives the
induction of the restricted character twist, with the original coefficient carrier. -/
def leviInductionCharacterMultiplication
    (heta : pointImage (r ≫ p) ≤ eta.toMonoidHom.ker)
    (hnu : ∀ m, nu.toMonoidHom m = eta.toMonoidHom (rationalPoints.map (l ≫ p) m)) :
    { E : (Langlands.twist eta.toMonoidHom ((induced).obj σ).representation).Equiv
        ((induced).obj orbit).representation //
      ∀ (f : (induced).obj σ) (x : rationalPoints G),
        Induction.eval _ _ (E f) x = (eta.toMonoidHom x : ℂ) • Induction.eval _ _ f x } := by
  let d := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hN := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let e := leviPointsEquiv p l hp hl
  let A := SmoothRep.pullback e.symm σ
  let ψ := subgroupSmoothCharacter eta (pointImage (l ≫ p))
  let B := A.twist ψ.toMonoidHom ψ.isOpen_ker
  let C := SmoothRep.pullback e.symm orbit
  let E : B.representation.Equiv C.representation :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun m => by
      apply LinearMap.ext
      intro x
      change (eta.toMonoidHom (m : rationalPoints G) : ℂ) • σ.representation (e.symm m) x =
        (nu.toMonoidHom (e.symm m) : ℂ) • σ.representation (e.symm m) x
      rw [hnu, ← leviPointsEquiv_apply_coe p l hp hl]
      change _ = (eta.toMonoidHom ((e (e.symm m) : pointImage (l ≫ p)) : rationalPoints G) : ℂ) • _
      rw [e.apply_symm_apply])
  refine ⟨(normalizedInductionCharacterTwistEquiv d hN eta heta A).trans
    (normalizedInductionEquivOfEquiv d hN E), ?_⟩
  intro f x
  rfl

section Transport

variable {Q U : GroupScheme (Spec (CommRingCat.of F))}
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {V : Subgroup (rationalPoints G)} [MeasurableSpace V] (measure : Measure V)

local notation "target" => leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ
local notation "normal" =>
  IsIntegralIntertwiner p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ V measure
set_option quotPrecheck false in
local notation "char" => eta.toMonoidHom

set_option maxHeartbeats 600000 in
/-- Conjugation by character multiplication preserves the integral formula at
one whenever the character is trivial on the fixed integration subgroup. -/
theorem isIntegralIntertwiner_twist
    (J : ((induced).obj σ).representation.IntertwiningMap ((target).obj σ).representation)
    (hJ : normal σ J) (hV : V ≤ (char).ker)
    (E : (Langlands.twist char ((induced).obj σ).representation).Equiv
      ((induced).obj orbit).representation)
    (E' : (Langlands.twist char ((target).obj σ).representation).Equiv
      ((target).obj orbit).representation)
    (hE : ∀ (f : (induced).obj σ) (x : rationalPoints G),
      Induction.eval _ _ (E f) x = (char x : ℂ) • Induction.eval _ _ f x)
    (hE' : ∀ (f : (target).obj σ) (x : rationalPoints G),
      Induction.eval _ _ (E' f) x = (char x : ℂ) • Induction.eval _ _ f x) :
    normal orbit (E'.toIntertwiningMap.comp
      ((Langlands.twistIntertwining char J).comp E.symm.toIntertwiningMap)) := by
  let Z := closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
      (identityParabolicDoubleCoset p q)) \
    DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) (identityParabolicDoubleCoset p q)
  have hB (τ : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) (f : (induced).obj τ) :
      f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
        (identityParabolicDoubleCoset p q)).obj τ ↔
      ∀ x ∈ Z, Induction.eval _ _ f x = 0 :=
    Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p) (pointImage q) Z
      (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p q))
      ((leviInducingFunctor p l r hp hr hl hmul).obj τ) f
  intro f hf ℓ
  let f₀ : (induced).obj σ := E.symm f
  have hf₀ (x : rationalPoints G) : Induction.eval _ _ f x = (char x : ℂ) • Induction.eval _ _ f₀ x := by
    simpa only [f₀, E.apply_symm_apply] using hE f₀ x
  have hvanish := (hB orbit f).mp hf
  have hvanish₀ := (hB σ f₀).mpr (fun x hx => by
    have h := hvanish x hx
    rw [hf₀ x] at h
    exact (smul_eq_zero.mp h).resolve_left (Units.ne_zero _))
  have hvalues : (fun x : V => ℓ (Induction.eval _ _ f x.val)) =
      fun x : V => ℓ (Induction.eval _ _ f₀ x.val) := by
    funext x
    have hx : char x.val = 1 := hV x.property
    have h := hf₀ x.val
    rw [hx, Units.val_one, one_smul] at h
    exact congrArg (fun y : σ => ℓ y) h
  obtain ⟨hi, he⟩ := hJ f₀ hvanish₀ ℓ
  refine ⟨?_, ?_⟩
  · change Integrable (fun x : V => ℓ (Induction.eval _ _ f x.val)) measure
    rw [hvalues]
    exact hi
  · change ℓ (Induction.eval _ _ (E' (J f₀)) 1) = ∫ x : V, ℓ (Induction.eval _ _ f x.val) ∂measure
    have hone := hE' (J f₀) 1
    rw [map_one, Units.val_one, one_smul] at hone
    exact (congrArg (fun y : σ => ℓ y) hone).trans
      (he.trans (congrArg (fun g : V → ℂ => ∫ x, g x ∂measure) hvalues).symm)

end Transport

end Langlands.Aubert.General.RepresentedParabolic
