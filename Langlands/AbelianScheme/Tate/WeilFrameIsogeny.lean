import Langlands.AbelianScheme.Tate.WeilHom0Pullback
import Langlands.AbelianScheme.Tate.WeilFrame
import Langlands.AbelianScheme.Tate.AdelicFrameIsogeny
import Langlands.AbelianScheme.Tate.PrimeToAdelicFrameIsogeny
import Langlands.Shimura.PEL.FormIsoTransport

/-! # Rational-isogeny transport of actual Weil-compatible frames -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Shimura.PEL

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
  (lamA : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (lamB : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
    evaluationB stability composition unitCoherence associativity comparison symmetry)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (functoriality : RationalWeilFunctorialityStatement.{u})

local notation "multiple" => IsRationalDualPullbackMultiple preservation composition
  unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
  MA evaluationA MB evaluationB additivity

include functoriality

/-- The geometric Hom0 multiplier gives the scaling law for the existing
integral-map Weil pullbacks on rational Tate sections. -/
lemma rationalWeilAlongHomBilinearMap_rationalHom_similitude (T : Over S) (P : ℕ → Prop)
    (q : ℚ) (f : Hom0 A B)
    (hf : multiple q f (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (x y : Tate.Rational A T P) :
    rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hB geometryB MB evaluationB compatibility T lamB P
      (Tate.rationalHomMap T P f x) (Tate.rationalHomMap T P f y) =
    q • rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lamA P x y := by
  simpa only [rationalWeilAlongHom0BilinearMap_ofHom] using
    rationalWeilAlongHom0BilinearMap_similitude preservation composition unitCoherence
      associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
      MB evaluationB additivity compatibility functoriality T P q f
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB) hf x y

namespace Tate

variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V) {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  lamA h iA V ψ s
local notation "FrameB" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hB geometryB MB evaluationB compatibility
  lamB h iB V ψ s

/-- Postcomposition by a rational isogeny restricts to actual Weil-compatible
full adelic frames. Multiplication on the actual twist realizes its multiplier. -/
def weilAdelicFrameIsogeny (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    FrameA ≃ FrameB := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  letI := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := GroupScheme.Tate.finiteAdeleModule B.toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) (fun _ => True) h
  exact FormIso.transport (finiteAdeleAlgebraIso (Over.mk s) (fun _ => True) h iA iB e he)
    (LinearEquiv.smulOfUnit
      (Units.map (algebraMap ℚ (Global.FiniteAdeles ℚ)) q))
    (fun x y => by
      change adelicWeilAlongHomBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hB geometryB MB evaluationB
          compatibility (Over.mk s) lamB (fun _ => True) h
          (rationalHomMap (Over.mk s) (fun _ => True) e.hom x)
          (rationalHomMap (Over.mk s) (fun _ => True) e.hom y) =
        TateTwist.Divisibility.finiteAdeleAction Γ((Over.mk s).left, ⊤) (fun _ => True) h
          (algebraMap ℚ (Global.FiniteAdeles ℚ) (q : ℚ))
          (adelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lamA (fun _ => True) h x y)
      simp only [adelicWeilAlongHomBilinearMap_apply,
        TateTwist.Divisibility.finiteAdeleAction_diagonal]
      exact rationalWeilAlongHomBilinearMap_rationalHom_similitude preservation composition
        unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
        MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality
        (Over.mk s) (fun _ => True) (q : ℚ) e.hom hf x y)

local notation "fullIsogeny" => weilAdelicFrameIsogeny preservation composition
  unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
  MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ s

@[simp] theorem weilAdelicFrameIsogeny_apply (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (eta : FrameA) (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    (fullIsogeny q e he hf eta).1 x =
      rationalHomMap (Over.mk s) (fun _ => True) e.hom (eta.1 x) := rfl

/-- The restricted map agrees with the already constructed ambient Tate-frame map. -/
theorem weilAdelicFrameIsogeny_underlying (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) (eta : FrameA) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    (fullIsogeny q e he hf eta).1 =
      adelicFrameIsogeny h iA iB ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s e he eta.1 := rfl

/-- Source precomposition commutes with the restricted isogeny map. -/
theorem weilAdelicFrameIsogeny_right (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (eta : FrameA) (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ) :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility lamA h iA V ψ s
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hB geometryB MB evaluationB
      compatibility lamB h iB V ψ s
    fullIsogeny q e he hf (right eta g) = right (fullIsogeny q e he hf eta) g := by
  apply Subtype.ext
  ext x
  rfl

variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local notation "AwayFrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  lamA h iA V ψ s hAway
local notation "AwayFrameB" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hB geometryB MB evaluationB compatibility
  lamB h iB V ψ s hAway

/-- The same geometric multiplier gives transport for actual away adelic frames
and the actual away Tate twist, with the coupled scalar comparison. -/
def weilPrimeToAdelicFrameIsogeny (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    AwayFrameA ≃ AwayFrameB := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  letI := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := GroupScheme.Tate.primeToFiniteAdeleModule B.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  exact FormIso.transport (primeToFiniteAdeleAlgebraIso (Over.mk s) hAway iA iB e he)
    (LinearEquiv.smulOfUnit
      (Units.map (algebraMap ℚ (Global.PrimeToFiniteAdeles m)) q))
    (fun x y => by
      change awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hB geometryB MB evaluationB
          compatibility (Over.mk s) lamB hAway
          (rationalHomMap (Over.mk s) (fun n => Nat.Coprime n m) e.hom x)
          (rationalHomMap (Over.mk s) (fun n => Nat.Coprime n m) e.hom y) =
        TateTwist.Divisibility.primeToFiniteAdeleAction Γ((Over.mk s).left, ⊤) hAway
          (algebraMap ℚ (Global.PrimeToFiniteAdeles m) (q : ℚ))
          (awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lamA hAway x y)
      simp only [awayAdelicWeilAlongHomBilinearMap_apply,
        TateTwist.Divisibility.primeToFiniteAdeleAction_diagonal]
      exact rationalWeilAlongHomBilinearMap_rationalHom_similitude preservation composition
        unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
        MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality
        (Over.mk s) (fun n => Nat.Coprime n m) (q : ℚ) e.hom hf x y)

local notation "awayIsogeny" => weilPrimeToAdelicFrameIsogeny preservation composition
  unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
  MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ s hAway

@[simp] theorem weilPrimeToAdelicFrameIsogeny_apply (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (eta : AwayFrameA) (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    (awayIsogeny q e he hf eta).1 x =
      rationalHomMap (Over.mk s) (fun n => Nat.Coprime n m) e.hom (eta.1 x) := rfl

/-- Away transport is exactly restriction of the ambient isogeny transport. -/
theorem weilPrimeToAdelicFrameIsogeny_underlying (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) (eta : AwayFrameA) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    (awayIsogeny q e he hf eta).1 =
      primeToAdelicFrameIsogeny m hAway iA iB ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V)
        s e he eta.1 := rfl

theorem weilPrimeToAdelicFrameIsogeny_right (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (eta : AwayFrameA) (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ) :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility lamA h iA V ψ s hAway
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hB geometryB MB evaluationB
      compatibility lamB h iB V ψ s hAway
    awayIsogeny q e he hf (right eta g) = right (awayIsogeny q e he hf eta) g := by
  apply Subtype.ext
  ext x
  rfl

end Tate
end Langlands.AbelianScheme
