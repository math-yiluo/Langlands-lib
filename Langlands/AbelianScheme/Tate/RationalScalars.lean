import Langlands.AbelianScheme.Tate.Rational
import Langlands.AbelianScheme.Tate.Scalars
import Langlands.Global.RationalProfiniteIntegerComparison
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rational scalar actions on actual Tate modules -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.TateScalarExtension

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- Extend the actual integral action to rationalized scalars and vectors. -/
def action : (ℚ ⊗[ℤ] R) →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] M) :=
  (LinearMap.tensorProductEnd ℤ ℚ M).comp
    (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Algebra.lsmul ℤ ℤ M))

@[simp] theorem action_tmul (q r : ℚ) (a : R) (x : M) :
    action R M (q ⊗ₜ[ℤ] a) (r ⊗ₜ[ℤ] x) = (q * r) ⊗ₜ[ℤ] (a • x) := by
  simp [action, LinearMap.tensorProductEnd, LinearMap.tensorProduct,
    TensorProduct.smul_tmul']

variable {R M} {N : Type*} [AddCommGroup N] [Module R N]

/-- Rationalization of an integral linear map preserves the extended action. -/
theorem map_action (f : M →ₗ[R] N) (a : ℚ ⊗[ℤ] R) (x : ℚ ⊗[ℤ] M) :
    f.toAddMonoidHom.toIntLinearMap.baseChange ℚ (action R M a x) =
      action R N a (f.toAddMonoidHom.toIntLinearMap.baseChange ℚ x) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x => simp [action_tmul]
    | add x y hx hy => simp_all
  | add a b ha hb => simp_all

end Langlands.TateScalarExtension

namespace Langlands.Global.RationalProfiniteIntegerAdeleComparison

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Integral witness chosen from the explicitly assumed published comparison. -/
def integralEquiv : ProfiniteIntegerRing ≃+* integralFiniteAdeles ℚ := h.choose

/-- Rational witness coupled to the same integral witness. -/
def rationalEquiv : (ℚ ⊗[ℤ] ProfiniteIntegerRing) ≃ₐ[ℚ] FiniteAdeles ℚ :=
  h.choose_spec.2.2.2.choose

@[simp] theorem rationalEquiv_tmul (q : ℚ) (a : ProfiniteIntegerRing) :
    rationalEquiv h (q ⊗ₜ[ℤ] a) = algebraMap ℚ (FiniteAdeles ℚ) q *
      (integralEquiv h a : FiniteAdeles ℚ) :=
  h.choose_spec.2.2.2.choose_spec q a

end Langlands.Global.RationalProfiniteIntegerAdeleComparison

namespace Langlands.GroupScheme.Tate

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The full rational residue scalar algebra acts on every selected Tate limit. -/
def rationalScalarAction (P : ℕ → Prop) :
    (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) →ₐ[ℚ] Module.End ℚ (Rational G T P) :=
  TateScalarExtension.action _ _

/-- Prime-to-p rational residue scalars act on the actual away Tate module. -/
def rationalAwayScalarAction (p : ℕ) :
    (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) →ₐ[ℚ]
      Module.End ℚ (RationalAway G T p) :=
  TateScalarExtension.action _ _

/-- Finite-adelic action, conditional on the published scalar comparison. -/
def finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    Global.FiniteAdeles ℚ →ₐ[ℚ] Module.End ℚ (Rational G T P) :=
  (rationalScalarAction G T P).comp
    (Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm.toAlgHom

/-- The corresponding module structure; the comparison hypothesis is explicit. -/
@[instance_reducible] def finiteAdeleModule (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    Module (Global.FiniteAdeles ℚ) (Rational G T P) :=
  Module.compHom _ (finiteAdeleAction G T P h).toRingHom

@[simp] theorem finiteAdeleAction_diagonal (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (q : ℚ) (x : Rational G T P) :
    finiteAdeleAction G T P h (algebraMap ℚ (Global.FiniteAdeles ℚ) q) x = q • x := by
  rw [AlgHom.commutes]
  rfl

/-- The module scalar operation is evaluation of the constructed algebra action. -/
theorem finiteAdeleModule_smul (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (a : Global.FiniteAdeles ℚ) (x : Rational G T P) :
    let := finiteAdeleModule G T P h
    a • x = finiteAdeleAction G T P h a x := rfl

/-- The finite-adelic module structure extends the existing rational one. -/
theorem finiteAdeleModule_scalarTower (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := finiteAdeleModule G T P h
    IsScalarTower ℚ (Global.FiniteAdeles ℚ) (Rational G T P) := by
  let := finiteAdeleModule G T P h
  exact IsScalarTower.of_algebraMap_smul (finiteAdeleAction_diagonal G T P h)

/-- The normalized integral witness recovers the original residue action. -/
theorem finiteAdeleAction_integral_tmul (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (a : Global.ProfiniteIntegerRing) (r : ℚ) (x : Integral G T P) :
    finiteAdeleAction G T P h
      (Global.RationalProfiniteIntegerAdeleComparison.integralEquiv h a)
      (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] (a • x) := by
  have he := Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul h 1 a
  simp only [map_one, one_mul] at he
  change TateScalarExtension.action _ _
    ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm _) _ = _
  rw [← he, AlgEquiv.symm_apply_apply, TateScalarExtension.action_tmul, one_mul]

/-- Rationalized restriction of the actual residue scalar ring. -/
def rationalScalarRestrictAway (p : ℕ) :
    (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) →ₐ[ℚ]
      (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (Global.PrimeToProfiniteIntegerRing.restrict p).toIntAlgHom

@[simp] theorem rationalScalarRestrictAway_tmul (p : ℕ) (q : ℚ)
    (a : Global.ProfiniteIntegerRing) :
    rationalScalarRestrictAway p (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] Global.PrimeToProfiniteIntegerRing.restrict p a := rfl

/-- Restriction preserves the extended action with its corresponding scalar map. -/
theorem rationalRestrictAway_scalarAction (p : ℕ)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull G T) :
    rationalRestrictAway G T p (rationalScalarAction G T _ a x) =
      rationalAwayScalarAction G T p (rationalScalarRestrictAway p a)
        (rationalRestrictAway G T p x) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp [rationalScalarAction, rationalAwayScalarAction,
        TateScalarExtension.action_tmul, restrictAway_smul]
    | add x y hx hy => simp_all
  | add a b ha hb => simp_all

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- The prime-to-p rational Tate map preserves rationalized away residue scalars. -/
theorem rationalMap_awayScalarAction (p : ℕ) (f : G ⟶ H)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) (x : RationalAway G T p) :
    rationalMap T _ f (rationalAwayScalarAction G T p a x) =
      rationalAwayScalarAction H T p a (rationalMap T _ f x) :=
  TateScalarExtension.map_action (awayLinearMap T p f) _ _

/-- Actual homomorphism-induced maps preserve the finite-adelic action. -/
theorem rationalMap_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : G ⟶ H)
    (a : Global.FiniteAdeles ℚ) (x : Rational G T P) :
    rationalMap T P f (finiteAdeleAction G T P h a x) =
      finiteAdeleAction H T P h a (rationalMap T P f x) :=
  TateScalarExtension.map_action (fullLinearMap T P f) _ _

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (P : ℕ → Prop)
variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Finite-adelic scalar action on the rational Tate module of an actual abelian scheme. -/
abbrev finiteAdeleAction : Global.FiniteAdeles ℚ →ₐ[ℚ] Module.End ℚ (Rational A T P) :=
  GroupScheme.Tate.finiteAdeleAction A.toGrp T P h

/-- Its module structure, with an explicit comparison assumption. -/
@[instance_reducible] def finiteAdeleModule :
    Module (Global.FiniteAdeles ℚ) (Rational A T P) :=
  GroupScheme.Tate.finiteAdeleModule A.toGrp T P h

variable {A} {B : AbelianScheme S}

/-- Scalar compatibility extends to the existing rational homomorphism maps. -/
theorem rationalHomMap_finiteAdeleAction (f : Rationalization.Hom A B)
    (a : Global.FiniteAdeles ℚ) (x : Rational A T P) :
    rationalHomMap T P f (finiteAdeleAction A T P h a x) =
      finiteAdeleAction B T P h a (rationalHomMap T P f x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalHomMap_tmul, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => q • y)
      (GroupScheme.Tate.rationalMap_finiteAdeleAction T P h (AbelianScheme.groupHom f) a x)
  | add f g hf hg => simp_all

/-- The actual rational homomorphism map, bundled as finite-adelic linear. -/
def finiteAdeleHomMap (f : Rationalization.Hom A B) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    Rational A T P →ₗ[Global.FiniteAdeles ℚ] Rational B T P := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  exact { (rationalHomMap T P f).toAddHom with
    map_smul' := rationalHomMap_finiteAdeleAction T P h f }

@[simp] theorem finiteAdeleHomMap_apply (f : Rationalization.Hom A B)
    (x : Rational A T P) :
    finiteAdeleHomMap T P h f x = rationalHomMap T P f x := rfl

@[simp] theorem finiteAdeleHomMap_identity :
    let := finiteAdeleModule A T P h
    finiteAdeleHomMap T P h (Rationalization.identity A) = LinearMap.id := by
  let := finiteAdeleModule A T P h
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T P) x

theorem finiteAdeleHomMap_comp {C : AbelianScheme S}
    (f : Rationalization.Hom A B) (g : Rationalization.Hom B C) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    let := finiteAdeleModule C T P h
    finiteAdeleHomMap T P h (Rationalization.comp A B C f g) =
      (finiteAdeleHomMap T P h g).comp (finiteAdeleHomMap T P h f) := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  let := finiteAdeleModule C T P h
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T P f g) x

theorem finiteAdeleHomMap_add (f g : Rationalization.Hom A B) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    finiteAdeleHomMap T P h (f + g) =
      finiteAdeleHomMap T P h f + finiteAdeleHomMap T P h g := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun ((rationalHomMap T P).map_add f g) x

variable (A)

/-- The rational endomorphism action commutes with finite-adelic scalars. -/
theorem rationalEndAction_commute (f : Rationalization.End A) (a : Global.FiniteAdeles ℚ) :
    Commute (rationalEndAction A T P f) (finiteAdeleAction A T P h a) := by
  apply LinearMap.ext
  intro x
  exact rationalHomMap_finiteAdeleAction T P h f a x

/-- The required B tensor_Q A_f action comes from actual rational endomorphisms. -/
def finiteAdeleAlgebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    (D ⊗[ℚ] Global.FiniteAdeles ℚ) →ₐ[ℚ] Module.End ℚ (Rational A T P) :=
  Algebra.TensorProduct.lift (algebraAction A T P i) (finiteAdeleAction A T P h)
    (fun d a => rationalEndAction_commute A T P h (i d) a)

@[simp] theorem finiteAdeleAlgebraAction_tmul {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (d : D) (a : Global.FiniteAdeles ℚ)
    (x : Rational A T P) :
    finiteAdeleAlgebraAction A T P h i (d ⊗ₜ[ℚ] a) x =
      rationalEndAction A T P (i d) (finiteAdeleAction A T P h a x) := rfl

/-- Module structure for the constructed B tensor_Q A_f action. -/
@[instance_reducible] def finiteAdeleAlgebraModule {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) (Rational A T P) :=
  Module.compHom _ (finiteAdeleAlgebraAction A T P h i).toRingHom

end Langlands.AbelianScheme.Tate
