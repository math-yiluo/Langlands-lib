import Langlands.LocalFactor.SpectralConductorClassFunction
import Langlands.LocalFactor.ConductorExponentStatement
import Langlands.LocalFactor.BrauerKernel.Trace
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# A conductor functional on the exact virtual group of the base field

For one actual finite Galois subfield `M`, the class-function form of the
inertia Artin sum of `M/F` is applied to trace characters through a fixed
section of Weil inertia over the inertia group of `M/F`. This gives an additive
functional on all continuous virtual classes of the base. On a genuine
representation presented at a subfield of `M`, it is the refined presentation
conductor.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Module Ramification Ramification.Padic
open scoped BigOperators

section Inertia

universe uE uK uV

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{uE} p} (T : E.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K E.Carrier]
  [IsScalarTower (Padic p) K E.Carrier]

open Classical in
/-- The number of lower ramification groups `G_i`, `i < b`, containing `σ`. -/
def galoisLowerCount (b : ℕ) (σ : E.Carrier ≃ₐ[K] E.Carrier) : ℕ :=
  ((Finset.range b).filter (fun i => σ ∈ lowerRamificationGroup T K i)).card

theorem integerRing_noetherian' : IsNoetherianRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

theorem automorphismGroup_finite' : Finite (E.Carrier ≃ₐ[K] E.Carrier) := by
  have : FiniteDimensional K E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K E.Carrier
  infer_instance

theorem inertiaIntegerAction_faithful' :
    letI := inertiaIntegerAction T K
    FaithfulSMul (inertia T K) T.Integers := by
  let := inertiaIntegerAction T K
  let := T.valuativeRel
  have : IsFractionRing T.Integers E.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation E.Carrier).valuationSubring E.Carrier)
  refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
  have heq : (σ : E.Carrier ≃ₐ[K] E.Carrier).toRingHom = (τ : E.Carrier ≃ₐ[K] E.Carrier).toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : E.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The class-function form of the inertia Artin sum. -/
theorem inertiaArtinConductor_eq_classSum [Fintype (inertia T K)] [DecidableEq (inertia T K)]
    (ρ : Representation ℂ (inertia T K) V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerRamificationGroup T K i = ⊥) :
    ((inertiaArtinConductor T K ρ : ℚ) : ℂ) =
      (Nat.card (inertia T K) : ℂ)⁻¹ * ∑ g : inertia T K,
        (galoisLowerCount T K b g : ℂ) *
          ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) := by
  let := inertiaIntegerAction T K
  have := inertiaIntegerAction_faithful' T K
  have := integerRing_noetherian' T
  have hb' : ∀ i ≥ b, lowerGroup T.Integers (inertia T K) i = ⊥ := by
    intro i hi
    change inertiaLowerGroup T K i = ⊥
    rw [inertiaLowerGroup, hb i hi, Subgroup.bot_subgroupOf]
  have h0 : lowerGroup T.Integers (inertia T K) 0 = ⊤ := inertiaLowerGroup_zero T K
  change ((Ramification.artinConductor T.Integers (inertia T K) ρ : ℚ) : ℂ) = _
  rw [artinConductor_eq_classSum T.Integers ρ b hb', h0, Subgroup.card_top]
  rfl

/-- The same formula, with the field structures found by unification. -/
theorem inertiaArtinConductor_eq_classSum' {E : PadicField.{uE} p} (T : E.TopologicalData)
    (K : Type uK) {_ : Field K} {_ : Algebra (Padic p) K} {_ : Algebra K E.Carrier}
    {_ : IsScalarTower (Padic p) K E.Carrier} (hfin : Fintype (inertia T K))
    (ρ : Representation ℂ (inertia T K) V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerRamificationGroup T K i = ⊥) :
    ((inertiaArtinConductor T K ρ : ℚ) : ℂ) =
      (Nat.card (inertia T K) : ℂ)⁻¹ * ∑ g : inertia T K,
        (galoisLowerCount T K b g : ℂ) *
          ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) := by
  classical
  exact inertiaArtinConductor_eq_classSum T K ρ b hb

end Inertia

section TraceOne

universe uG uV

variable {G : Type uG} [Group G] (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)

open VirtualRepresentation in
/-- The trace character at the identity is the virtual degree. -/
theorem trace_apply_one (x : ExactGrothendieckGroup P) :
    ExactGrothendieckGroup.trace P x 1 = (ExactGrothendieckGroup.degree P x : ℂ) := by
  have hl : (LinearMap.proj (1 : G) : (G → ℂ) →ₗ[ℤ] ℂ).comp (ExactGrothendieckGroup.trace P) =
      (Int.castAddHom ℂ).toIntLinearMap.comp (ExactGrothendieckGroup.degree P) := by
    apply ExactGrothendieckGroup.hom_ext P
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change ExactGrothendieckGroup.trace P (ExactGrothendieckGroup.ofRepresentation P A) 1 =
        ((ExactGrothendieckGroup.degree P (ExactGrothendieckGroup.ofRepresentation P A) : ℤ) : ℂ)
      rw [ExactGrothendieckGroup.trace_ofRepresentation,
        ExactGrothendieckGroup.degree_ofRepresentation, FiniteRepresentation.traceFunction_apply,
        map_one, LinearMap.trace_one]
      rfl
  exact LinearMap.congr_fun hl x

end TraceOne

section Functional

universe uF uV

open CommonClosure ConductorExponent Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))

/-- The canonical data of the finite Galois subfield, as a p-adic field. -/
abbrev dataM : (absoluteFiniteExtension F M).TopologicalData :=
  (absoluteFiniteExtension F M).canonicalTopologicalData

/-- The inertia group of `M/F`. -/
abbrev inertiaM : Subgroup ((absoluteFiniteExtension F M).Carrier ≃ₐ[F.Carrier]
    (absoluteFiniteExtension F M).Carrier) :=
  inertia (dataM F M) F.Carrier

instance inertiaM_finite : Finite (inertiaM F M) := by
  have := automorphismGroup_finite' (E := absoluteFiniteExtension F M) F.Carrier
  infer_instance

/-- The chosen fintype structure on the inertia group of `M/F`. -/
abbrev inertiaFintype : Fintype (inertiaM F M) := Fintype.ofFinite _

/-- A chosen bound beyond which the lower ramification groups of `M/F` vanish. -/
def lowerBound : ℕ :=
  Classical.choose (exists_lowerRamificationGroup_eq_bot (dataM F M) F.Carrier)

theorem lowerBound_spec :
    ∀ i ≥ lowerBound F M, lowerRamificationGroup (dataM F M) F.Carrier i = ⊥ :=
  Classical.choose_spec (exists_lowerRamificationGroup_eq_bot (dataM F M) F.Carrier)

/-- A set-theoretic section of Weil inertia over the inertia group of `M/F`. -/
def inertiaSection : inertiaM F M → localInertia F :=
  Function.surjInv (HerbrandBridge.weilInertiaRestriction_surjective F M)

@[simp]
theorem weilInertiaRestriction_inertiaSection (γ : inertiaM F M) :
    weilInertiaRestriction F M (inertiaSection F M γ) = γ :=
  Function.surjInv_eq _ γ

/-- The class-function conductor sum of a function on Weil inertia, read through
the chosen section. -/
def inertiaClassSum (f : localInertia F → ℂ) : ℂ :=
  letI := inertiaFintype F M
  (Nat.card (inertiaM F M) : ℂ)⁻¹ * ∑ γ : inertiaM F M,
    (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) γ : ℂ) *
      (f 1 - f (inertiaSection F M γ))

theorem inertiaClassSum_add (f g : localInertia F → ℂ) :
    inertiaClassSum F M (f + g) = inertiaClassSum F M f + inertiaClassSum F M g := by
  simp only [inertiaClassSum, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- The trace character of a base virtual class, on Weil inertia. -/
def inertiaTrace (x : Virtual.{uF, uV} F (base F)) : localInertia F → ℂ :=
  fun w => ExactGrothendieckGroup.trace (ContinuousPredicate F (base F)) x
    (baseInclusion F w.val)

/-- The conductor functional of `M` on the base exact virtual group. -/
def conductorFunctional : Virtual.{uF, uV} F (base F) →+ ℂ where
  toFun x := inertiaClassSum F M (inertiaTrace F x)
  map_zero' := by
    have h0 : ExactGrothendieckGroup.trace (ContinuousPredicate F (base F))
        (0 : Virtual.{uF, uV} F (base F)) = 0 := LinearMap.map_zero _
    simp only [inertiaClassSum, inertiaTrace, h0, Pi.zero_apply, sub_self, mul_zero,
      Finset.sum_const_zero]
  map_add' x y := by
    rw [← inertiaClassSum_add]
    congr 1
    funext w
    simp [inertiaTrace]

/-- The trivial character has conductor zero. -/
theorem conductorFunctional_one :
    conductorFunctional.{uF, uV} F M (ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F (base F) →ₜ* ℂˣ)) = 0 := by
  change inertiaClassSum F M _ = 0
  simp [inertiaClassSum, inertiaTrace]

/-- On a genuine continuous representation presented at a subfield of `M`, the
functional is the refined presentation conductor. -/
theorem conductorFunctional_baseClass
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A) (h : P.extension ≤ M)
    (hM : Function.Surjective (weilInertiaRestriction F M)) :
    conductorFunctional.{uF, uV} F M (baseClass F A hA) =
      (((P.refine M h).artinConductor hM : ℚ) : ℂ) := by
  let := inertiaFintype F M
  classical
  have key := inertiaArtinConductor_eq_classSum' (dataM F M) F.Carrier (inertiaFintype F M)
    ((P.refine M h).representation hM) (lowerBound F M) (lowerBound_spec F M)
  refine Eq.trans ?_ key.symm
  show inertiaClassSum F M _ = _
  unfold inertiaClassSum
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  have hγ : ((P.refine M h).representation hM) γ =
      (FiniteRepresentation.restrict (baseInclusion F).toMonoidHom A).representation
        (inertiaSection F M γ) := by
    have := FiniteInertiaPresentation.representation_apply (P.refine M h) hM
      (inertiaSection F M γ)
    rwa [show weilInertiaRestriction F (P.refine M h).extension (inertiaSection F M γ) = γ from
      weilInertiaRestriction_inertiaSection F M γ] at this
  congr 1
  · simp only [inertiaTrace, ExactGrothendieckGroup.trace_ofRepresentation,
      FiniteRepresentation.traceFunction_apply, OneMemClass.coe_one, map_one,
      LinearMap.trace_one]
    rfl
  · refine Eq.trans ?_ (congrArg (LinearMap.trace ℂ _) hγ).symm
    simp only [inertiaTrace, ExactGrothendieckGroup.trace_ofRepresentation,
      FiniteRepresentation.traceFunction_apply]
    rfl

end Functional

end Langlands.LocalFactor.SpectralConductor
