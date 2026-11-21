import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof
import Langlands.AlgebraicGeometry.FiniteEtale.CoverPowerLift

/-! # Comparing rational Tate monodromy with a supplied model -/

noncomputable section

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.FiniteEtale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Langlands.AbelianScheme.Tate

open GroupScheme.Tate (Index)

variable {S T W : Scheme.{u}} {Ω : Type u} [Field Ω]
  (b : W ⟶ S) (j : W ⟶ T)
  (B : AbelianScheme S) (G : AbelianScheme T)
  (e : (AbelianScheme.baseChange b).obj B ≅ (AbelianScheme.baseChange j).obj G)
  (w : Spec (.of Ω) ⟶ W) (s : Spec (.of Ω) ⟶ S) (hsb : w ≫ b = s)
  (P : ℕ → Prop)

/-- Compare rational Tate modules using the actual isomorphism over the common base. -/
def rationalModelComparison :
    Rational G (Over.mk (w ≫ j)) P ≃ₗ[ℚ] Rational B (Over.mk s) P := by
  subst s
  exact ((rationalBaseChange j G (Over.mk w) P).symm.trans
    (rationalIso (Over.mk w) P (Rationalization.inclusion.mapIso e.symm))).trans
    (rationalBaseChange b B (Over.mk w) P)

variable (hw : ∀ Y : Cover W, Finite (Fiber w Y))
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (ht : ∀ Y : Cover T, Finite (Fiber (w ≫ j) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (huS : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (huT : ∀ n : Index P, IsUnit (n.val : Γ(T, ⊤)))
  (huW : ∀ n : Index P, IsUnit (n.val : Γ(W, ⊤)))

include huW in
/-- The comparison intertwines the two actions pulled back from the base schemes. -/
theorem rationalModelComparison_monodromy (g : FundamentalGroup w hw)
    (x : Rational G (Over.mk (w ≫ j)) P) :
    rationalModelComparison b j B G e w s hsb P
      (rationalMonodromyRepresentation (w ≫ j) ht htor G P huT
        (fundamentalGroupMap j w (w ≫ j) rfl hw ht g) x) =
    rationalMonodromyRepresentation s hs htor B P huS
      (fundamentalGroupMap b w s hsb hw hs g)
      (rationalModelComparison b j B G e w s hsb P x) := by
  subst s
  let q := rationalBaseChange j G (Over.mk w) P
  have hq : q.symm
      (rationalMonodromyRepresentation (w ≫ j) ht htor G P huT
        (fundamentalGroupMap j w (w ≫ j) rfl hw ht g) x) =
      rationalMonodromyRepresentation w hw htor ((AbelianScheme.baseChange j).obj G) P huW
        g (q.symm x) := by
    apply q.injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((rationalBaseChange_monodromy j w hw ht htor G P huT huW g (q.symm x)).trans
      (congrArg (rationalMonodromyRepresentation (w ≫ j) ht htor G P huT
        (fundamentalGroupMap j w (w ≫ j) rfl hw ht g)) (q.apply_symm_apply x))).symm
  simp only [rationalModelComparison, LinearEquiv.trans_apply]
  change rationalBaseChange b B (Over.mk w) P
      (rationalIso (Over.mk w) P (Rationalization.inclusion.mapIso e.symm) (q.symm _)) = _
  rw [hq]
  change rationalBaseChange b B (Over.mk w) P
      (rationalIso (Over.mk w) P (Rationalization.inclusion.mapIso e.symm)
        (rationalMonodromy w hw htor _ P huW g (q.symm x))) =
    rationalMonodromy (w ≫ b) hs htor B P huS (fundamentalGroupMap b w (w ≫ b) rfl hw hs g)
      (rationalBaseChange b B (Over.mk w) P
        (rationalIso (Over.mk w) P (Rationalization.inclusion.mapIso e.symm) (q.symm x)))
  rw [← rationalMonodromy_iso w hw htor P huW,
    rationalBaseChange_monodromy b w hw hs htor B P huS huW]

include G e huT huW in
/-- If an element restricts trivially over the model, it acts trivially over the original base. -/
theorem rationalMonodromy_eq_one_of_model (g : FundamentalGroup w hw)
    (hg : fundamentalGroupMap j w (w ≫ j) rfl hw ht g = 1) :
    rationalMonodromyRepresentation s hs htor B P huS
      (fundamentalGroupMap b w s hsb hw hs g) = 1 := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (rationalModelComparison b j B G e w s hsb P).surjective y
  have h := rationalModelComparison_monodromy b j B G e w s hsb P hw hs ht htor huS huT huW g x
  rw [hg, map_one] at h
  exact h.symm

/-- If the covering fundamental group restricts trivially over the model,
every monodromy operator over the original base has finite order. -/
theorem isOfFinOrder_rationalMonodromy_of_finiteEtale_model {S T : Scheme.{u}}
    (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (Y : Cover S) (x : Fiber s Y) (j : Y.obj.left ⟶ T)
    (B : AbelianScheme S) (G : AbelianScheme T)
    (e : (AbelianScheme.baseChange Y.obj.hom).obj B ≅ (AbelianScheme.baseChange j).obj G)
    (hw : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
    (ht : ∀ Z : Cover T, Finite (Fiber (x.left ≫ j) Z))
    (htor : TorsionFiniteEtaleStatement.{u}) (P : ℕ → Prop)
    (huS : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    (huT : ∀ n : Index P, IsUnit (n.val : Γ(T, ⊤)))
    (huW : ∀ n : Index P, IsUnit (n.val : Γ(Y.obj.left, ⊤)))
    (htriv : ∀ g : FundamentalGroup x.left hw,
      fundamentalGroupMap j x.left (x.left ≫ j) rfl hw ht g = 1)
    (g : FundamentalGroup s hs) :
    IsOfFinOrder (rationalMonodromyRepresentation s hs htor B P huS g) :=
  isOfFinOrder_of_trivial_on_cover s hs Y x hw
    (rationalMonodromyRepresentation s hs htor B P huS)
    (fun k => rationalMonodromy_eq_one_of_model Y.obj.hom j B G e x.left s (Over.w x)
      P hw hs ht htor huS huT huW k (htriv k)) g

end Langlands.AbelianScheme.Tate
