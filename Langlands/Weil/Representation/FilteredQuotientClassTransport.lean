import Langlands.Weil.Representation.IrreducibleQuotientEquiv

/-!
# Transport of continuous irreducible classes through isomorphic quotients

A topological isomorphism of group quotients transports the classes
trivial on the two normal subgroups. It preserves triviality on subgroups
with matching images and intertwines characters from the common quotient.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.FiniteRepresentation

universe uG uH uV

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

theorem restrictClass_isTrivialOn_iff (p : G →* H) (S : Subgroup G)
    (c : IsomorphismClasses.{0, uH, uV} ℂ H) :
    (restrictClass p c).IsTrivialOn S ↔ c.IsTrivialOn (S.map p) := by
  induction c using Quotient.inductionOn with
  | h A =>
    change S ≤ (A.representation.comp p).ker ↔ S.map p ≤ A.representation.ker
    constructor
    · rintro h _ ⟨g, hg, rfl⟩
      exact h hg
    · intro h g hg
      exact h ⟨g, hg, rfl⟩

variable [TopologicalSpace G] [TopologicalSpace H]
variable {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]

local notation "π" => QuotientGroup.mk' N
local notation "π'" => QuotientGroup.mk' M

/-- The rank-indexed continuous irreducible classes trivial on a given subgroup. -/
abbrev ContinuousIrreducibleClasses.TrivialOn (J : Subgroup G) (n : ℕ) :=
  {d : ContinuousIrreducibleClasses.{uG, uV} G n // (forgetPropertyClass _ d.val).IsTrivialOn J}

/-- Transport a bounded class by descending to the first quotient, pulling
back along the inverse isomorphism, and inflating from the second quotient. -/
def continuousIrreducibleQuotientTransport (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) (n : ℕ) :
    ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n ≃
      ContinuousIrreducibleClasses.TrivialOn.{uH, uV} M n :=
  (continuousIrreducibleQuotientEquiv N n).symm.trans
    ((continuousIrreducibleRestrictEquiv φ.symm n).trans (continuousIrreducibleQuotientEquiv M n))

/-- Matching quotient subgroup images give matching kernel containments. -/
theorem continuousIrreducibleQuotientTransport_isTrivialOn_iff
    (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) {n : ℕ} (c : ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n)
    (S : Subgroup G) (T : Subgroup H)
    (hST : (S.map π).map φ.toMulEquiv.toMonoidHom = T.map π') :
    (forgetPropertyClass _ (continuousIrreducibleQuotientTransport φ n c).val.val).IsTrivialOn T ↔
      (forgetPropertyClass _ c.val.val).IsTrivialOn S := by
  let E := continuousIrreducibleQuotientEquiv N n
  obtain ⟨q, rfl⟩ := E.surjective c
  have hmap : (T.map π').map φ.symm.toMulEquiv.toMonoidHom = S.map π := by
    rw [← hST, Subgroup.map_map]
    have hcomp : φ.symm.toMulEquiv.toMonoidHom.comp φ.toMulEquiv.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext φ.symm_apply_apply
    rw [hcomp, Subgroup.map_id]
  change (forgetPropertyClass _ (continuousIrreducibleQuotientEquiv M n
    (continuousIrreducibleRestrictEquiv φ.symm n (E.symm (E q)))).val.val).IsTrivialOn T ↔
      (forgetPropertyClass _ (E q).val.val).IsTrivialOn S
  rw [Equiv.symm_apply_apply, forget_continuousIrreducibleQuotientEquiv,
    forget_continuousIrreducibleRestrictEquiv, forget_continuousIrreducibleQuotientEquiv,
    restrictClass_isTrivialOn_iff,
    restrictClass_isTrivialOn_iff]
  change (forgetPropertyClass _ q.val).IsTrivialOn
      ((T.map π').map φ.symm.toMulEquiv.toMonoidHom) ↔
    (restrictClass π (forgetPropertyClass _ q.val)).IsTrivialOn S
  rw [hmap]
  exact (restrictClass_isTrivialOn_iff π S (forgetPropertyClass _ q.val)).symm

private theorem restrictEquiv_twist {A : Type uG} {B : Type uH}
    [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃ₜ* B) (χ : B →ₜ* ℂˣ) {n : ℕ} (c : ContinuousIrreducibleClasses.{uH, uV} B n) :
    continuousIrreducibleRestrictEquiv f n (continuousIrreducibleTwistEquiv χ n c) =
      continuousIrreducibleTwistEquiv (χ.comp (f : A →ₜ* B)) n
        (continuousIrreducibleRestrictEquiv f n c) := by
  apply Subtype.ext
  apply forgetPropertyClass_injective _
  rw [forget_continuousIrreducibleRestrictEquiv, forget_continuousIrreducibleTwistEquiv,
    forget_continuousIrreducibleTwistEquiv, forget_continuousIrreducibleRestrictEquiv]
  generalize forgetPropertyClass _ c.val = c'
  exact Quotient.inductionOn c' fun _ => rfl

/-- A character of the quotient acts by twisting on the classes trivial
on the normal subgroup. -/
def ContinuousIrreducibleClasses.TrivialOn.twistEquiv
    (χ : (G ⧸ N) →ₜ* ℂˣ) (n : ℕ) :
    ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n ≃
      ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n :=
  (continuousIrreducibleQuotientEquiv N n).symm.trans
    ((continuousIrreducibleTwistEquiv χ n).trans (continuousIrreducibleQuotientEquiv N n))

/-- The twist on a quotient-trivial class is the usual twist by the
pullback character. -/
theorem ContinuousIrreducibleClasses.TrivialOn.twistEquiv_val
    (χ : (G ⧸ N) →ₜ* ℂˣ) {n : ℕ} (c : ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n) :
    (twistEquiv χ n c).val =
      continuousIrreducibleTwistEquiv (χ.comp ⟨π, QuotientGroup.continuous_mk⟩) n c.val := by
  obtain ⟨q, rfl⟩ := (continuousIrreducibleQuotientEquiv N n).surjective c
  change (continuousIrreducibleQuotientEquiv N n
    (continuousIrreducibleTwistEquiv χ n
      ((continuousIrreducibleQuotientEquiv N n).symm
        (continuousIrreducibleQuotientEquiv N n q)))).val = _
  rw [Equiv.symm_apply_apply]
  exact continuousIrreducibleQuotientEquiv_twist N χ q

/-- Transport intertwines twisting by a continuous character of the target
quotient, pulled back to the two groups. -/
theorem continuousIrreducibleQuotientTransport_twist
    (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) {n : ℕ} (c : ContinuousIrreducibleClasses.TrivialOn.{uG, uV} N n)
    (χ : (H ⧸ M) →ₜ* ℂˣ) :
    continuousIrreducibleQuotientTransport φ n
      (ContinuousIrreducibleClasses.TrivialOn.twistEquiv (χ.comp (φ : _ →ₜ* _)) n c) =
      ContinuousIrreducibleClasses.TrivialOn.twistEquiv χ n
        (continuousIrreducibleQuotientTransport φ n c) := by
  let E := continuousIrreducibleQuotientEquiv N n
  let F := continuousIrreducibleQuotientEquiv M n
  let R := continuousIrreducibleRestrictEquiv φ.symm n
  let χG := χ.comp (φ : (G ⧸ N) →ₜ* (H ⧸ M))
  have hχ : χG.comp (φ.symm : (H ⧸ M) →ₜ* (G ⧸ N)) = χ := by
    apply ContinuousMonoidHom.ext
    intro x
    change χ (φ (φ.symm x)) = χ x
    rw [φ.apply_symm_apply]
  change F (R (E.symm (E (continuousIrreducibleTwistEquiv χG n (E.symm c))))) =
    F (continuousIrreducibleTwistEquiv χ n (F.symm (F (R (E.symm c)))))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have htw := restrictEquiv_twist φ.symm χG (E.symm c)
  rw [hχ] at htw
  exact congrArg F htw

end Langlands.FiniteRepresentation
