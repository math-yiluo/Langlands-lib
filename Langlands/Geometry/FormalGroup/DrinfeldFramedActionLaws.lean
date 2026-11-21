import Langlands.Geometry.FormalGroup.DrinfeldFramedAction
import Langlands.Geometry.FormalGroup.DrinfeldActionFrame

/-! # The group laws on height-zero framed representatives -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open ValuativeRel CentralSimple ModuleLaw
open BasicAtlas.RationalHom (comp comp_assoc comp_id id_comp)

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {π : 𝒪[K]} {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable (X : DrinfeldFramedAtlas Φ A)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))
variable (c : Φ.val.MatrixCoordinates)

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem eq_of_components {Y Z : DrinfeldFramedAtlas Φ A}
    (hresidue : Y.residueMap = Z.residueMap) (htarget : Y.target = Z.target)
    (hforward : HEq Y.rho.hom.val Z.rho.hom.val) : Y = Z := by
  rcases Y with ⟨a, Y, ρ, hρ⟩
  rcases Z with ⟨b, Z, σ, hσ⟩
  dsimp only at hresidue htarget hforward
  subst b
  subst Z
  have : ρ = σ := BasicAtlas.OrderAction.QuasiIsogeny.ext_hom
    (BasicAtlas.OrderAction.RationalHom.ext (eq_of_heq hforward))
  subst σ
  rfl

variable (g h : GL (Fin (reducedDegree K D)) K × Dˣ)

/-- Restrict the combined fixed-frame comparison to the original reduced target cover. -/
def actionFrameOnCover {a : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj}
    (e : X.actionResidueMap g = a) :
    BasicAtlas.OrderAction.QuasiIsogeny K
      (SpecialAtlas.quotientFrame Φ.val a X.target.val).order X.source.order rfl :=
  BasicAtlas.ofGlobalOrderQuasiIsogeny (DrinfeldResidue.actionFrameQuasiIsogeny Φ p hcard hFrob c g e)
    X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers

set_option maxHeartbeats 1000000 in
/-- The forward tensor of the transformed framing is the original framing with the
combined fixed-frame comparison before it and the reduced-target twist after it. -/
theorem act_rho_hom {a : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj}
    (e : X.actionResidueMap g = a) :
    HEq (X.act g p hcard hFrob hRank c).rho.hom.val
      (comp (X.actionTargetQuasiIsogeny g).hom.val
        (comp X.rho.hom.val (X.actionFrameOnCover p hcard hFrob c g e).hom.val)) := by
  subst a
  change HEq (X.actionFraming g p hcard hFrob c).hom.val _
  have hframe : X.actionFrameOnCover p hcard hFrob c g rfl =
      (X.actionSourceFrobenius g p hcard hFrob).trans (X.matrixSourceQuasiIsogeny c g.1⁻¹) :=
    BasicAtlas.ofGlobalOrderQuasiIsogeny_trans _ _ _ _
  refine (X.actionFraming_hom g p hcard hFrob c).trans
    ((heq_of_eq (X.actionFramingOnCover_hom g p hcard hFrob c).symm).trans ?_)
  apply heq_of_eq
  rw [hframe]
  rfl

set_option maxHeartbeats 1000000 in
/-- The unit fixes the actual residue map, special target and framing. -/
@[simp]
theorem act_one : X.act 1 p hcard hFrob hRank c = X := by
  have e : X.actionResidueMap 1 = X.residueMap := by
    rw [actionResidueMap, DrinfeldAction.exponent_one, DrinfeldResidue.shift_zero]
  refine eq_of_components e (SpecialAtlas.HeightSquaredAtlas.twistDivisionUnit_one X.target) ?_
  refine (X.act_rho_hom p hcard hFrob hRank c 1 e).trans (heq_of_eq ?_)
  have hframe : X.actionFrameOnCover p hcard hFrob c 1 e =
      BasicAtlas.OrderAction.QuasiIsogeny.refl X.source.order := by
    unfold actionFrameOnCover
    rw [DrinfeldResidue.actionFrameQuasiIsogeny_one, BasicAtlas.ofGlobalOrderQuasiIsogeny_refl]
    rfl
  have htarget : (X.actionTargetQuasiIsogeny 1).hom.val =
      BasicAtlas.RationalHom.id X.target.val.reduction.atlas := by
    change atlasRationalAction K D X.target.val.reduction.order (((1 : Dˣ)⁻¹ : Dˣ) : D) = 1
    rw [inv_one, Units.val_one, map_one]
  rw [hframe, htarget]
  exact (id_comp _).trans (comp_id _)

omit [Algebra 𝒪[K] R] [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem atlasTwist_mul_forward {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
    {σ : Type} [Finite σ] {B : BasicAtlas 𝒪[K] S σ}
    (E : BasicAtlas.OrderAction (IntegerRing K D) B) (a b : Dˣ) :
    comp (atlasTwistQuasiIsogeny K D (atlasTwist K D E b) a).hom.val
      (atlasTwistQuasiIsogeny K D E b).hom.val = (atlasTwistQuasiIsogeny K D E (a * b)).hom.val := by
  have forward_cast {T U : BasicAtlas.OrderAction (IntegerRing K D) B} (e : T = U)
      (q : BasicAtlas.OrderAction.QuasiIsogeny K E T rfl) :
      (cast (congrArg (fun V => BasicAtlas.OrderAction.QuasiIsogeny K E V rfl) e) q).hom.val =
        q.hom.val := by
    subst U
    rfl
  exact (forward_cast (atlasTwist_twist K D E b a) _).symm.trans
    (congrArg (fun q => q.hom.val) (atlasTwistQuasiIsogeny_mul K D E b a))

section ForwardComposition

variable {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
variable {a b z : κ →ₐ[𝒪[K]] S}
variable (T : SpecialAtlas K D ι S)

private abbrev frameAtlas (ψ : κ →ₐ[𝒪[K]] S) :=
  (SpecialAtlas.ofGlobalCover (Φ.val.mapSameUniverse ψ) T.atlas.opens T.atlas.covers).atlas

/-- Form the forward tensor using a single specified reduced atlas. -/
private def framingForward
    (ρ : BasicAtlas.RationalHom K (frameAtlas (Φ := Φ) T b) T.atlas rfl)
    (q : ModuleLaw.OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b)) (d : Dˣ) :
    BasicAtlas.RationalHom K (frameAtlas (Φ := Φ) T a) T.atlas rfl :=
  comp (T.twistDivisionUnitQuasiIsogeny d).hom.val
    (comp ρ (BasicAtlas.ofGlobalOrderQuasiIsogeny q T.atlas.opens T.atlas.covers).hom.val)

omit [Algebra 𝒪[K] R] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem framingForward_congr {T U : SpecialAtlas K D ι S} (e : T = U)
    {ρ : BasicAtlas.RationalHom K (frameAtlas (Φ := Φ) T b) T.atlas rfl}
    {ρ' : BasicAtlas.RationalHom K (frameAtlas (Φ := Φ) U b) U.atlas rfl} (hρ : HEq ρ ρ')
    (q : ModuleLaw.OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b)) (d : Dˣ) :
    HEq (framingForward T ρ q d) (framingForward U ρ' q d) := by
  subst U
  cases eq_of_heq hρ
  rfl

omit [Algebra 𝒪[K] R] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem framingForward_mul
    (ρ : BasicAtlas.RationalHom K (frameAtlas (Φ := Φ) T z) T.atlas rfl)
    (q : ModuleLaw.OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b))
    (r : ModuleLaw.OrderAction.QuasiIsogeny K (Φ.val.order.map b) (Φ.val.order.map z)) (d e : Dˣ) :
    framingForward (T.twistDivisionUnit e) (framingForward T ρ r e) q d =
      framingForward T ρ (q.trans r) (d * e) := by
  let twistD := (atlasTwistQuasiIsogeny K D (atlasTwist K D T.order e) d).hom.val
  let twistE := (atlasTwistQuasiIsogeny K D T.order e).hom.val
  let frameQ := (BasicAtlas.ofGlobalOrderQuasiIsogeny q T.atlas.opens T.atlas.covers).hom.val
  let frameR := (BasicAtlas.ofGlobalOrderQuasiIsogeny r T.atlas.opens T.atlas.covers).hom.val
  change comp twistD (comp (comp twistE (comp ρ frameR)) frameQ) = _
  calc
    _ = comp (comp twistD twistE) (comp ρ (comp frameR frameQ)) := by
      simp only [comp_assoc]
    _ = _ := by
      rw [show comp twistD twistE = (T.twistDivisionUnitQuasiIsogeny (d * e)).hom.val from
        atlasTwist_mul_forward T.order d e]
      simp only [framingForward, BasicAtlas.ofGlobalOrderQuasiIsogeny_trans]
      rfl

end ForwardComposition

set_option maxHeartbeats 1000000 in
/-- Applying two transformations in succession gives the transformed triple for their ordered product. -/
theorem act_mul : X.act (g * h) p hcard hFrob hRank c =
    (X.act h p hcard hFrob hRank c).act g p hcard hFrob hRank c := by
  symm
  let Y := X.act h p hcard hFrob hRank c
  have eg : Y.actionResidueMap g = X.actionResidueMap (g * h) := by
    change DrinfeldResidue.shift (DrinfeldAction.exponent K D g)
        (DrinfeldResidue.shift (DrinfeldAction.exponent K D h) X.residueMap) = _
    rw [actionResidueMap, DrinfeldAction.exponent_mul, DrinfeldResidue.shift_shift, add_comm]
  have eh : X.actionResidueMap h = Y.residueMap := rfl
  refine eq_of_components eg (SpecialAtlas.HeightSquaredAtlas.twistDivisionUnit_mul X.target g.2 h.2).symm ?_
  let frameG := DrinfeldResidue.actionFrameQuasiIsogeny Φ p hcard hFrob c g eg
  let frameH := DrinfeldResidue.actionFrameQuasiIsogeny Φ p hcard hFrob c h eh
  let frameProduct := DrinfeldResidue.actionFrameQuasiIsogeny Φ p hcard hFrob c (g * h)
    (a := X.actionResidueMap (g * h)) (b := X.residueMap) rfl
  have hframe : frameG.trans frameH = frameProduct :=
    DrinfeldResidue.actionFrameQuasiIsogeny_mul Φ p hcard hFrob c g h eg eh rfl
  let T := X.target.val.reduction
  let U := Y.target.val.reduction
  have hreduce : U = T.twistDivisionUnit h.2 := X.actionTarget_reduction h
  have hrho : HEq Y.rho.hom.val (framingForward (Φ := Φ) T X.rho.hom.val frameH h.2) :=
    X.act_rho_hom p hcard hFrob hRank c h eh
  have htransport := framingForward_congr (Φ := Φ) hreduce hrho frameG g.2
  have hproduct := framingForward_mul (Φ := Φ) T X.rho.hom.val frameG frameH g.2 h.2
  have hreplace := congrArg (fun q => framingForward (Φ := Φ) T X.rho.hom.val q (g.2 * h.2)) hframe
  exact (Y.act_rho_hom p hcard hFrob hRank c g eg).trans
    (htransport.trans ((heq_of_eq (hproduct.trans hreplace)).trans
      (X.act_rho_hom p hcard hFrob hRank c (g * h) rfl).symm))

/-- The matrix and division groups act on the actual height-zero framed triples. -/
@[instance_reducible]
def groupAction : MulAction (GL (Fin (reducedDegree K D)) K × Dˣ) (DrinfeldFramedAtlas Φ A) where
  smul g X := X.act g p hcard hFrob hRank c
  one_smul X := X.act_one p hcard hFrob hRank c
  mul_smul g h X := X.act_mul p hcard hFrob hRank c g h

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
