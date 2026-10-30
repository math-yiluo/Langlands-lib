import Langlands.AbelianScheme.Tate.WeilGeometricTransportStatement

/-! # Geometric path compatibility of the actual rational Weil pairing: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- The structure morphism of a binary product in `Over S` factors through the pullback. -/
theorem prod_hom_eq_pullback (Y Z : Over S) :
    (Y ⨯ Z).hom = (Over.prodLeftIsoPullback Y Z).hom ≫ pullback.fst Y.hom Z.hom ≫ Y.hom := by
  rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]

/-- A binary product of finite objects over `S` is finite over `S`. -/
theorem prod_isFinite (Y Z : Over S) [IsFinite Y.hom] [IsFinite Z.hom] :
    IsFinite (Y ⨯ Z).hom := by
  rw [prod_hom_eq_pullback]
  infer_instance

/-- A binary product of étale objects over `S` is étale over `S`. -/
theorem prod_etale (Y Z : Over S) [Etale Y.hom] [Etale Z.hom] :
    Etale (Y ⨯ Z).hom := by
  rw [prod_hom_eq_pullback]
  infer_instance

attribute [local instance] prod_isFinite prod_etale

/-- Path evaluation preserves the binary-product pairing of two lifts. -/
theorem pathAct_prodLift (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (Y Z : Over S) [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom]
    (x : Over.mk s ⟶ Y) (y : Over.mk s ⟶ Z) :
    pathAct p (Y ⨯ Z) (prod.lift x y) = prod.lift (pathAct p Y x) (pathAct p Z y) := by
  apply prod.hom_ext
  · rw [← pathAct_naturality, prod.lift_fst, prod.lift_fst]
  · rw [← pathAct_naturality, prod.lift_snd, prod.lift_snd]

/-- Path evaluation commutes with any morphism out of a product of finite étale objects. -/
theorem pathAct_prodLift_comp (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    {Y Z W : Over S} [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom]
    [IsFinite W.hom] [Etale W.hom] (q : Y ⨯ Z ⟶ W)
    (x : Over.mk s ⟶ Y) (y : Over.mk s ⟶ Z) :
    pathAct p W (prod.lift x y ≫ q) = prod.lift (pathAct p Y x) (pathAct p Z y) ≫ q := by
  rw [pathAct_naturality, pathAct_prodLift]

end Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.GroupScheme.mu

/-- On a field-valued point, the canonical section-ring comparison carries the points-level
root to the affine root. -/
theorem levelMap_pointsLevelEquiv {S : Scheme.{u}} (n : ℕ) {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (z : Additive (Over.mk s ⟶ (mu S n).X)) :
    TateTwist.levelMap (Scheme.ΓSpecIso (.of Ω)).hom.hom n (pointsLevelEquiv n (Over.mk s) z) =
      levelEquiv n s z := rfl

end Langlands.GroupScheme.mu

namespace Langlands.GroupScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

attribute [local instance] prod_isFinite prod_etale

/-- Root values of any morphism on a product of actual torsion kernels are transported by the
same geometric path that transports the two torsion arguments. -/
theorem levelTransport_kernelPairing (G H : Grp (Over S)) [IsCommMonObj G.X]
    [IsCommMonObj H.X] (n : ℕ)
    [IsFinite (GroupScheme.kernel (multiplication G n)).X.hom]
    [Etale (GroupScheme.kernel (multiplication G n)).X.hom]
    [IsFinite (GroupScheme.kernel (multiplication H n)).X.hom]
    [Etale (GroupScheme.kernel (multiplication H n)).X.hom]
    [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
    (q : (GroupScheme.kernel (multiplication G n)).X ⨯
      (GroupScheme.kernel (multiplication H n)).X ⟶ (mu S n).X)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level G (Over.mk s) n) (y : Level H (Over.mk s) n) :
    TateTwist.Geometry.levelTransport n p
        (TateTwist.levelMap (Scheme.ΓSpecIso (.of Ω)).hom.hom n
          (mu.pointsLevelEquiv n (Over.mk s)
            (Additive.ofMul (prod.lift (kernelLift G (Over.mk s) n x)
              (kernelLift H (Over.mk s) n y) ≫ q)))) =
      TateTwist.levelMap (Scheme.ΓSpecIso (.of Ω')).hom.hom n
        (mu.pointsLevelEquiv n (Over.mk t)
          (Additive.ofMul (prod.lift (kernelLift G (Over.mk t) n (finiteLevelTransport G n p x))
            (kernelLift H (Over.mk t) n (finiteLevelTransport H n p y)) ≫ q))) := by
  obtain ⟨x, rfl⟩ := (kernelLevelEquiv G (Over.mk s) n).surjective x
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv H (Over.mk s) n).surjective y
  rw [finiteLevelTransport_kernel, finiteLevelTransport_kernel]
  simp only [kernelLift, AddEquiv.symm_apply_apply, toMul_ofMul]
  rw [mu.levelMap_pointsLevelEquiv, mu.levelMap_pointsLevelEquiv,
    TateTwist.Geometry.levelTransport_kernel, toMul_ofMul, pathAct_prodLift_comp]

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "integralPair" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility
local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility
local notation "rationalAlong" => rationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility

/-- Finite-level path compatibility of the actual finite Weil pairing, after the canonical
section-ring comparisons at both points. -/
theorem levelTransport_finiteWeilLevelBilinearMap (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Tate.Level A (Over.mk s) n) (y : Tate.Level (DA) (Over.mk s) n) :
    TateTwist.Geometry.levelTransport n p
        (TateTwist.levelMap (Scheme.ΓSpecIso (.of Ω)).hom.hom n
          (levelPair n (Over.mk s) x y)) =
      TateTwist.levelMap (Scheme.ΓSpecIso (.of Ω')).hom.hom n
        (levelPair n (Over.mk t) (Tate.levelTransport htor A n hn hu p x)
          (Tate.levelTransport htor (DA) n hn hu p y)) := by
  have := Tate.torsionKernel_isFinite htor A n hn hu
  have := Tate.torsionKernel_etale htor A n hn hu
  have := Tate.torsionKernel_isFinite htor (DA) n hn hu
  have := Tate.torsionKernel_etale htor (DA) n hn hu
  rw [finiteWeilLevelBilinearMap_apply, finiteWeilLevelBilinearMap_apply]
  exact GroupScheme.Tate.levelTransport_kernelPairing A.toGrp (DA).toGrp n
    (finiteWeilPairing preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n) p x y

/-- Integral path compatibility of the actual integral Weil pairing. -/
theorem integralTransport_integralWeilBilinearMap (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
    [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Tate.Integral A (Over.mk s) P) (y : Tate.Integral (DA) (Over.mk s) P) :
    TateTwist.Geometry.integralTransport P (hμfin := hμfin) (hμet := hμet) p
        (TateTwist.Divisibility.map P (Scheme.ΓSpecIso (.of Ω)).hom.hom
          (integralPair (Over.mk s) P x y)) =
      TateTwist.Divisibility.map P (Scheme.ΓSpecIso (.of Ω')).hom.hom
        (integralPair (Over.mk t) P (Tate.integralTransport htor A P hu p x)
          (Tate.integralTransport htor (DA) P hu p y)) := by
  apply Subtype.ext
  funext n
  exact levelTransport_finiteWeilLevelBilinearMap preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA htor n.val
    n.property.1 (hu n) p (x.val n) (y.val n)

/-- Rational path compatibility of the actual rational Weil pairing on `A` and its dual. -/
theorem sectionRationalTransport_rationalWeilBilinearMap (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
    [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Tate.Rational A (Over.mk s) P) (y : Tate.Rational (DA) (Over.mk s) P) :
    TateTwist.Geometry.sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p
        (rationalPairing (Over.mk s) P x y) =
      rationalPairing (Over.mk t) P (Tate.rationalTransport htor A P hu p x)
        (Tate.rationalTransport htor (DA) P hu p y) := by
  rw [TateTwist.Geometry.sectionRationalTransport_apply, LinearEquiv.symm_apply_eq]
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      rw [rationalWeilBilinearMap_tmul, Tate.rationalTransport_tmul, Tate.rationalTransport_tmul,
        rationalWeilBilinearMap_tmul, TateTwist.Geometry.sectionRationalEquiv_apply,
        TateTwist.Geometry.sectionRationalEquiv_apply, TateTwist.Divisibility.rationalMap_tmul,
        TateTwist.Divisibility.rationalMap_tmul, TateTwist.Geometry.rationalTransport_tmul,
        integralTransport_integralWeilBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
          htor P hu p x y]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- Rational path compatibility of every actual dual-valued homomorphism pullback. -/
theorem sectionRationalTransport_rationalWeilAlongHomBilinearMap (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
    [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (lam : A ⟶ DA)
    (x y : Tate.Rational A (Over.mk s) P) :
    TateTwist.Geometry.sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p
        (rationalAlong (Over.mk s) lam P x y) =
      rationalAlong (Over.mk t) lam P (Tate.rationalTransport htor A P hu p x)
        (Tate.rationalTransport htor A P hu p y) := by
  rw [rationalWeilAlongHomBilinearMap_apply, rationalWeilAlongHomBilinearMap_apply,
    sectionRationalTransport_rationalWeilBilinearMap preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      htor P hu p]
  congr 1
  exact Tate.rationalTransport_map htor P hu lam p y

/-- The actual rational Weil pairing and every actual dual-hom pullback commute with geometric
path transport on both arguments and on the roots-of-unity twist. -/
theorem rationalWeilGeometricTransport : RationalWeilGeometricTransportStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    compatibility S _ A hA geometryA MA evaluationA Ω Ω' _ _ s t hs ht htor P hu hμfin hμet p
  exact ⟨fun x y => sectionRationalTransport_rationalWeilBilinearMap preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility htor P hu (hμfin := hμfin) (hμet := hμet) p x y,
    fun lam x y => sectionRationalTransport_rationalWeilAlongHomBilinearMap preservation
      composition unitCoherence associativity comparison symmetry stability hA geometryA MA
      evaluationA compatibility htor P hu (hμfin := hμfin) (hμet := hμet) p lam x y⟩

end Langlands.AbelianScheme
