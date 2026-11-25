import Langlands.Geometry.FormalGroup.DrinfeldActionNaturality
import Langlands.Geometry.FormalGroup.DrinfeldFramedUnitTwist
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Integral and central elements acting trivially on Drinfeld's functor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] {D : Type w} [Ring D] [Algebra O D]
variable {R S : Type v} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

/-- Actual integral order endomorphisms commute with coefficient extension. -/
theorem endomorphism_baseChangeAlong (E : OrderAction D X) (a : D) (f : R →ₐ[O] S) :
    (E.endomorphism a).baseChangeAlong f = (E.baseChangeAlong f).endomorphism a := by
  apply Hom.ext
  intro C b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  exact (BasicAtlas.Hom.baseChangeAlong_coordinates (E.endomorphism a) f C b hb).trans
    (E.baseChangeAlongOrderChart_coordinates f C b hb a).symm

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]
variable {Y Z : BasicAtlas O R σ} {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

private theorem trans_ofIso_forward (f : QuasiIsogeny F E E' h) (i : Iso E' E'' k) :
    HEq (f.trans (.ofIso i)).hom.val
      (BasicAtlas.RationalHom.comp (BasicAtlas.RationalHom.ofHom i.hom.val) f.hom.val) := by
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom

variable {O T F : Type*} [CommRing O] [CommRing T] [Algebra O T]
  [Field F] [Algebra O F]
variable {σ : Type} [Finite σ] {X Y : BasicAtlas O T σ} {h : X.opens = Y.opens}

private theorem cancelScalarComposites (q : RationalHom F X Y h) (a : Fˣ) :
    comp ((a : F) • id Y) (comp q (((a⁻¹ : Fˣ) : F) • id X)) = q := by
  rw [comp_smul, comp_id, smul_comp, comp_smul, id_comp, smul_smul, Units.mul_inv, one_smul]

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralSimple CentralDivision ModuleLaw
open BasicAtlas.RationalHom (comp comp_id id_comp)

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

/-- The printed order units and anti-diagonal central pairs generate a normal
subgroup of the acting product. -/
def DrinfeldAction.trivialSubgroup (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D] :
    Subgroup (GL (Fin (reducedDegree K D)) K × Dˣ) :=
  Subgroup.normalClosure
    (Set.range (fun a : (IntegerRing K D)ˣ => (1, integerUnit K D a)) ∪
      Set.range (fun a : Kˣ => (Matrix.GeneralLinearGroup.scalar (Fin (reducedDegree K D)) a,
        Units.map (algebraMap K D).toMonoidHom a⁻¹)))

instance : (DrinfeldAction.trivialSubgroup K D).Normal :=
  Subgroup.normalClosure_normal

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]

namespace SpecialAtlas

/-- A central division unit leaves the actual special atlas unchanged. -/
theorem twistDivisionUnit_scalar (Y : SpecialAtlas K D ι R) (a : Kˣ) :
    Y.twistDivisionUnit (Units.map (algebraMap K D).toMonoidHom a) = Y := by
  have he : (Y.twistDivisionUnit (Units.map (algebraMap K D).toMonoidHom a)).order = Y.order := by
    change Y.order.twist (conjugation K D (Units.map (algebraMap K D).toMonoidHom a)) = Y.order
    rw [conjugation_scalar]
    cases Y.order
    rfl
  have ext_order {U V : SpecialAtlas K D ι R} (h : U.atlas = V.atlas)
      (e : HEq U.order V.order) : U = V := by
    cases U
    cases V
    cases h
    cases eq_of_heq e
    rfl
  exact ext_order rfl (heq_of_eq he)

end SpecialAtlas

namespace DrinfeldFramedAtlas

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

private theorem eq_of_forward_components {X Y : DrinfeldFramedAtlas Φ A}
    (he : X.residueMap = Y.residueMap) (ht : X.target = Y.target)
    (hq : HEq X.rho.hom.val Y.rho.hom.val) : X = Y := by
  apply eq_of_residue_target_rho he ht
  rcases X with ⟨a, X, ρ, hX⟩
  rcases Y with ⟨b, Y, σ, hY⟩
  change a = b at he
  change X = Y at ht
  subst b
  subst Y
  exact heq_of_eq (BasicAtlas.OrderAction.QuasiIsogeny.ext_hom
    (BasicAtlas.OrderAction.RationalHom.ext (eq_of_heq hq)))

set_option maxHeartbeats 750000 in
private theorem integerUnit_reduced_forward (Y : SpecialAtlas K D ι A.obj)
    (a : (IntegerRing K D)ˣ) :
    ((Y.twistIntegerUnitIso a).reduction).hom.val = (Y.reduction.twistIntegerUnitIso a).hom.val := by
  let t := Y.twistIntegerUnitIso a
  have hh := congrArg Subtype.val (BasicAtlas.OrderAction.Iso.reduction_hom t)
  have hv := BasicAtlas.OrderAction.Hom.reduction_val t.hom
  exact hh.trans (hv.trans (BasicAtlas.OrderAction.endomorphism_baseChangeAlong Y.order
    (a⁻¹ : (IntegerRing K D)ˣ) (Nilp.quotientO 𝒪[K] A)))

variable [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (p : ℕ) [ExpChar κ p] {n : ℕ} (hcard : Nat.card 𝓀[K] = p ^ n)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (n * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (n * j))
variable (c : Φ.val.MatrixCoordinates)

private theorem signedFrobenius_of_zero {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
    (b : κ →ₐ[𝒪[K]] S) {m : ℤ} (hm : m = 0) (e : DrinfeldResidue.shift m b = b) :
    DrinfeldResidue.signedFrameFrobenius Φ p hcard hFrob m e =
      ModuleLaw.OrderAction.QuasiIsogeny.refl (Φ.val.order.map b) := by
  subst m
  exact DrinfeldResidue.signedFrameFrobenius_zero Φ p hcard hFrob b

private theorem actionFrameOnCover_of_zero (X : DrinfeldFramedAtlas Φ A)
    (g : GL (Fin (reducedDegree K D)) K × Dˣ) (hg : DrinfeldAction.exponent K D g = 0)
    (e : X.actionResidueMap g = X.residueMap) :
    X.actionFrameOnCover p hcard hFrob c g e = X.matrixSourceQuasiIsogeny c g.1⁻¹ := by
  unfold actionFrameOnCover matrixSourceQuasiIsogeny DrinfeldResidue.actionFrameQuasiIsogeny
  rw [signedFrobenius_of_zero p hcard hFrob X.residueMap hg e,
    ModuleLaw.OrderAction.QuasiIsogeny.refl_trans]

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
set_option maxHeartbeats 800000 in
private theorem integerUnitTarget_forward (X : DrinfeldFramedAtlas Φ A)
    (a : (IntegerRing K D)ˣ) :
    (X.actionTargetQuasiIsogeny (1, integerUnit K D a)).hom.val =
      BasicAtlas.RationalHom.ofHom ((X.target.val.twistIntegerUnitIso a).reduction.hom.val) := by
  have h := congrArg (fun q => q.hom.val)
    (atlasTwistQuasiIsogeny_integerUnit K D X.target.val.reduction a)
  exact h.trans (congrArg (BasicAtlas.RationalHom.ofHom (F := K))
    (integerUnit_reduced_forward X.target.val a).symm)

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
set_option maxHeartbeats 1500000 in
private theorem twistIntegerUnit_forward (X : DrinfeldFramedAtlas Φ A)
    (a : (IntegerRing K D)ˣ) :
    HEq (X.twistIntegerUnit a).rho.hom.val
      (comp (BasicAtlas.RationalHom.ofHom ((X.target.val.twistIntegerUnitIso a).reduction.hom.val))
        X.rho.hom.val) := by
  have h := congrArg (fun q => q.hom.val) (X.twistIntegerUnit_rho a)
  exact (heq_of_eq h).trans (BasicAtlas.OrderAction.trans_ofIso_forward X.rho
    ((X.target.val.twistIntegerUnitIso a).reduction))

set_option maxHeartbeats 1300000 in
/-- The integral pair in Drinfeld's action is the original unit twist with its
integral comparison map. -/
theorem act_integerUnit (X : DrinfeldFramedAtlas Φ A) (a : (IntegerRing K D)ˣ) :
    X.act (1, integerUnit K D a) p hcard hFrob hRank c = X.twistIntegerUnit a := by
  let g : GL (Fin (reducedDegree K D)) K × Dˣ := (1, integerUnit K D a)
  have hg : DrinfeldAction.exponent K D g = 0 := DrinfeldAction.exponent_integerUnit K D a
  have e : X.actionResidueMap g = X.residueMap := by
    rw [actionResidueMap, hg, DrinfeldResidue.shift_zero]
  refine eq_of_forward_components (X := X.act g p hcard hFrob hRank c)
    (Y := X.twistIntegerUnit a) e
    (Subtype.ext (X.target.val.twistDivisionUnit_integerUnit a)) ?_
  have hf : X.actionFrameOnCover p hcard hFrob c g e =
      BasicAtlas.OrderAction.QuasiIsogeny.refl X.source.order := by
    rw [actionFrameOnCover_of_zero p hcard hFrob c X g hg e]
    change X.matrixSourceQuasiIsogeny c ((1 : GL (Fin (reducedDegree K D)) K)⁻¹) = _
    rw [inv_one, matrixSourceQuasiIsogeny_one]
  let t := BasicAtlas.RationalHom.ofHom (F := K)
    ((X.target.val.twistIntegerUnitIso a).reduction.hom.val)
  have hr : comp (X.actionTargetQuasiIsogeny g).hom.val
      (comp X.rho.hom.val (X.actionFrameOnCover p hcard hFrob c g e).hom.val) =
      comp t X.rho.hom.val :=
    (congrArg₂ (fun d s => comp d (comp X.rho.hom.val s)) (integerUnitTarget_forward X a)
      (congrArg (fun q => q.hom.val) hf)).trans (congrArg (comp t) (comp_id X.rho.hom.val))
  exact (X.act_rho_hom p hcard hFrob hRank c g e).trans
    ((heq_of_eq hr).trans (twistIntegerUnit_forward X a).symm)

set_option maxHeartbeats 1200000 in
/-- Opposite central scalars cancel in the complete framing tensor and fix the
actual framed representative. -/
theorem act_oppositeScalars (X : DrinfeldFramedAtlas Φ A) (a : Kˣ) :
    X.act (Matrix.GeneralLinearGroup.scalar (Fin (reducedDegree K D)) a,
      Units.map (algebraMap K D).toMonoidHom a⁻¹) p hcard hFrob hRank c = X := by
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin (reducedDegree K D)) (R := K)
  let g := (scalar a, Units.map (algebraMap K D).toMonoidHom a⁻¹)
  have hg : DrinfeldAction.exponent K D g = 0 := DrinfeldAction.exponent_central K D a
  have e : X.actionResidueMap g = X.residueMap := by
    rw [actionResidueMap, hg, DrinfeldResidue.shift_zero]
  refine eq_of_forward_components e (Subtype.ext (X.target.val.twistDivisionUnit_scalar a⁻¹)) ?_
  refine (X.act_rho_hom p hcard hFrob hRank c g e).trans (heq_of_eq ?_)
  have hs : (X.actionFrameOnCover p hcard hFrob c g e).hom.val =
      ((a⁻¹ : Kˣ) : K) • BasicAtlas.RationalHom.id X.source.atlas := by
    rw [actionFrameOnCover_of_zero p hcard hFrob c X g hg e]
    let b := X.residueMap
    change BasicAtlas.ofGlobalRationalHom _ _
      (ModuleLaw.RationalHom.map b (c.quasiIsogeny (scalar a)⁻¹).hom.val) = _
    rw [← map_inv scalar, SpecialModule.MatrixCoordinates.quasiIsogeny_scalar_hom]
    change BasicAtlas.ofGlobalRationalHom _ _ (ModuleLaw.RationalHom.map b
      (((a⁻¹ : Kˣ) : K) • ModuleLaw.RationalHom.id Φ.val.formalModule)) = _
    simp only [_root_.map_smul, ModuleLaw.RationalHom.map_id,
      BasicAtlas.ofGlobalRationalHom_id]
    rfl
  have ht : (X.actionTargetQuasiIsogeny g).hom.val =
      (a : K) • BasicAtlas.RationalHom.id X.target.val.reduction.atlas := by
    change atlasRationalAction K D X.target.val.reduction.order (algebraMap K D (a : K)) = _
    exact (atlasRationalAction K D X.target.val.reduction.order).commutes (a : K)
  exact (congrArg₂ (fun d s => comp d (comp X.rho.hom.val s)) ht hs).trans
    (BasicAtlas.RationalHom.cancelScalarComposites X.rho.hom.val a)

/-- The original natural action factors through the quotient by Drinfeld's
stated trivial elements. -/
def actionQuotientHom : (GL (Fin (reducedDegree K D)) K × Dˣ) ⧸
      DrinfeldAction.trivialSubgroup K D →* Aut (comparisonClassFunctor (R := R) Φ) := by
  refine QuotientGroup.lift _ (actionHom (R := R) p hcard c) ?_
  apply Subgroup.normalClosure_le_normal
  intro g hg
  change actionHom (R := R) p hcard c g = 1
  apply Aut.ext
  apply CategoryTheory.Iso.ext
  apply NatTrans.ext
  funext A
  apply ConcreteCategory.hom_ext
  intro q
  rw [actionHom_app]
  refine Quotient.inductionOn q ?_
  intro X
  rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (congrArg comparisonClassOf (act_integerUnit p hcard _ _ c X a)).trans
      (comparisonClassOf_twistIntegerUnit X a)
  · exact congrArg comparisonClassOf (act_oppositeScalars p hcard _ _ c X a)

/-- Evaluating the quotient action on an acting pair gives the original natural automorphism. -/
@[simp]
theorem actionQuotientHom_mk (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    actionQuotientHom (R := R) p hcard c (QuotientGroup.mk' (DrinfeldAction.trivialSubgroup K D) g) =
      actionHom (R := R) p hcard c g := rfl

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
