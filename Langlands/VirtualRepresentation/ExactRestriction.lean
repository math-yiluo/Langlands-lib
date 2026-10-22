import Langlands.VirtualRepresentation.Exact
import Langlands.Weil.Representation.Restriction
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.InductionContinuity
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Restriction on exact virtual representations

Restriction retains the vector spaces and linear maps, so it preserves the
actual short exact relations. Continuous group maps preserve the usual
endomorphism-topology continuity predicate.
-/

noncomputable section

universe uK uG uH uJ uV uA uB uC

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH} {J : Type uJ}
  [Field K] [Monoid G] [Monoid H] [Monoid J]

/-- Restrict an actual intertwiner, retaining its underlying linear map. -/
def restrictMap (φ : H →* G)
    {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    (f : A.representation.IntertwiningMap B.representation) :
    (restrict φ A).representation.IntertwiningMap (restrict φ B).representation :=
  ⟨f.toLinearMap, fun h => f.isIntertwining' (φ h)⟩

/-- All three short exactness conditions are unchanged by restriction. -/
theorem isShortExact_restrict_iff (φ : H →* G)
    {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    {C : FiniteRepresentation.{uK, uG, uC} K G}
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation) :
    IsShortExact (restrictMap φ f) (restrictMap φ g) ↔ IsShortExact f g := Iff.rfl

@[simp]
theorem rank_restrict (φ : H →* G) (A : FiniteRepresentation K G) :
    (restrict φ A).rank = A.rank := rfl

/-- The identity restriction preserves the actual representation. -/
def restrictIdEquiv (A : FiniteRepresentation K G) :
    Equiv (restrict (MonoidHom.id G) A) A :=
  Representation.Equiv.refl _

/-- Successive restrictions agree with restriction along the composite. -/
def restrictCompEquiv (φ : H →* G) (ψ : J →* H) (A : FiniteRepresentation K G) :
    Equiv (restrict ψ (restrict φ A)) (restrict (φ.comp ψ) A) :=
  Representation.Equiv.refl _

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH} {J : Type uJ}
  [Field K] [Monoid G] [Monoid H] [Monoid J]
variable (φ : H →* G)
variable (P : FiniteRepresentation.{uK, uG, uV} K G → Prop)
variable (Q : FiniteRepresentation.{uK, uH, uV} K H → Prop)

/-- Restriction on genuine classes, with the explicit object-closure condition. -/
def restrictClassWith
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A)) :
    IsomorphismClassesWith P → IsomorphismClassesWith Q :=
  Quotient.map
    (fun A => ⟨FiniteRepresentation.restrict φ A.val, hPQ A.val A.property⟩)
    (fun _ _ ⟨e⟩ => ⟨FiniteRepresentation.restrictEquiv φ e⟩)

/-- Actual restriction carries each exact relation to an exact relation. -/
theorem restrictClassWith_isExactAdditive
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A)) :
    IsExactAdditive P (fun c => ofClass Q (restrictClassWith φ P Q hPQ c)) := by
  intro A B C f g h
  exact ofRepresentation_shortExact Q
    ((isShortExact_restrict_iff φ (A := A.val) (B := B.val) (C := C.val) f g).mpr h)

/-- The descended integer-linear restriction on the exact quotient. -/
def restrict (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A)) :
    ExactGrothendieckGroup P →ₗ[ℤ] ExactGrothendieckGroup Q :=
  lift P (fun c => ofClass Q (restrictClassWith φ P Q hPQ c))
    (restrictClassWith_isExactAdditive φ P Q hPQ)

@[simp]
theorem restrict_ofClass
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A))
    (c : IsomorphismClassesWith P) :
    restrict φ P Q hPQ (ofClass P c) = ofClass Q (restrictClassWith φ P Q hPQ c) :=
  lift_ofClass P _ _ c

@[simp]
theorem restrict_ofRepresentation
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A))
    (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    restrict φ P Q hPQ (ofRepresentation P A) =
      ofRepresentation Q ⟨FiniteRepresentation.restrict φ A.val, hPQ A.val A.property⟩ :=
  restrict_ofClass φ P Q hPQ _

/-- Restriction preserves the genuine virtual dimension. -/
theorem degree_comp_restrict
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A)) :
    (degree Q).comp (restrict φ P Q hPQ) = degree P := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change degree Q (restrict φ P Q hPQ (ofRepresentation P A)) =
      degree P (ofRepresentation P A)
    simp only [restrict_ofRepresentation, degree_ofRepresentation, rank_restrict]

theorem degree_restrict
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A))
    (x : ExactGrothendieckGroup P) :
    degree Q (restrict φ P Q hPQ x) = degree P x :=
  LinearMap.congr_fun (degree_comp_restrict φ P Q hPQ) x

/-- The same map restricts to the genuine virtual dimension-zero subgroups. -/
def restrictDegreeZero
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A)) :
    degreeZero P →ₗ[ℤ] degreeZero Q :=
  (restrict φ P Q hPQ).restrict fun x hx => by
    change degree Q (restrict φ P Q hPQ x) = 0
    rw [degree_restrict, (mem_degreeZero P x).mp hx]

/-- Identity restriction induces the identity for any supplied closure proof. -/
theorem restrict_id
    (hP : ∀ A, P A → P (FiniteRepresentation.restrict (MonoidHom.id G) A)) :
    restrict (MonoidHom.id G) P P hP = LinearMap.id := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change restrict (MonoidHom.id G) P P hP (ofRepresentation P A) = ofRepresentation P A
    rw [restrict_ofRepresentation]
    exact ofRepresentation_eq_of_equiv P (FiniteRepresentation.restrictIdEquiv A.val)

/-- The contravariant composition law holds on the actual exact quotients. -/
theorem restrict_comp (ψ : J →* H)
    (R : FiniteRepresentation.{uK, uJ, uV} K J → Prop)
    (hφ : ∀ A, P A → Q (FiniteRepresentation.restrict φ A))
    (hψ : ∀ A, Q A → R (FiniteRepresentation.restrict ψ A))
    (hφψ : ∀ A, P A → R (FiniteRepresentation.restrict (φ.comp ψ) A)) :
    (restrict ψ Q R hψ).comp (restrict φ P Q hφ) =
      restrict (φ.comp ψ) P R hφψ := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change restrict ψ Q R hψ (restrict φ P Q hφ (ofRepresentation P A)) =
      restrict (φ.comp ψ) P R hφψ (ofRepresentation P A)
    rw [restrict_ofRepresentation, restrict_ofRepresentation, restrict_ofRepresentation]
    exact ofRepresentation_eq_of_equiv R (FiniteRepresentation.restrictCompEquiv φ ψ A.val)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} {J : Type uJ} [Group G] [Group H] [Group J]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]

/-- Restriction of continuous exact virtual representations along an actual
continuous group homomorphism; the closure condition is proved. -/
def continuousRestrict (φ : H →ₜ* G) :
    ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous) →ₗ[ℤ]
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
        A.IsContinuous) :=
  restrict φ.toMonoidHom _ _
    (fun _ hA => FiniteRepresentation.isContinuous_restrict φ.toMonoidHom φ.continuous hA)

/-- Continuous restriction preserves virtual degree. -/
theorem degree_continuousRestrict (φ : H →ₜ* G)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    degree (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.IsContinuous)
      (continuousRestrict φ x) =
        degree (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) x :=
  degree_restrict φ.toMonoidHom _ _ _ x

/-- A topological group isomorphism induces an actual equivalence of continuous
exact virtual groups. The inverse uses the inverse group isomorphism. -/
def continuousRestrictEquivalence (e : H ≃ₜ* G) :
    ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous) ≃ₗ[ℤ]
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
        A.IsContinuous) where
  toLinearMap := continuousRestrict (e : H →ₜ* G)
  invFun := continuousRestrict (e.symm : G →ₜ* H)
  left_inv x := by
    have h :
        (continuousRestrict.{uH, uG, uV} (e.symm : G →ₜ* H)).comp
          (continuousRestrict.{uG, uH, uV} (e : H →ₜ* G)) = LinearMap.id := by
      apply hom_ext _
      intro c
      induction c using Quotient.inductionOn with
      | h A =>
        change restrict (e.symm : G →ₜ* H).toMonoidHom _ _ _
          (restrict (e : H →ₜ* G).toMonoidHom _ _ _ (ofRepresentation _ A)) = ofRepresentation _ A
        rw [restrict_ofRepresentation, restrict_ofRepresentation]
        apply ofRepresentation_eq_of_equiv _
        refine { toLinearEquiv := LinearEquiv.refl ℂ A.val, isIntertwining' := ?_ }
        intro g
        ext v
        change A.val.representation (e (e.symm g)) v = A.val.representation g v
        rw [e.apply_symm_apply]
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h :
        (continuousRestrict.{uG, uH, uV} (e : H →ₜ* G)).comp
          (continuousRestrict.{uH, uG, uV} (e.symm : G →ₜ* H)) = LinearMap.id := by
      apply hom_ext _
      intro c
      induction c using Quotient.inductionOn with
      | h A =>
        change restrict (e : H →ₜ* G).toMonoidHom _ _ _
          (restrict (e.symm : G →ₜ* H).toMonoidHom _ _ _ (ofRepresentation _ A)) = ofRepresentation _ A
        rw [restrict_ofRepresentation, restrict_ofRepresentation]
        apply ofRepresentation_eq_of_equiv _
        refine { toLinearEquiv := LinearEquiv.refl ℂ A.val, isIntertwining' := ?_ }
        intro g
        ext v
        change A.val.representation (e.symm (e g)) v = A.val.representation g v
        rw [e.symm_apply_apply]
    exact LinearMap.congr_fun h x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
