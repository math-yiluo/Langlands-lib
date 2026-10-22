import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Subquotients

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Evaluation at one of a map into smooth induction, descended through the
actual unipotent coinvariants when the inducing action is trivial there. -/
def coinvariantEvaluation
    (P N : Subgroup G) (hNP : N ≤ P)
    (ρ : Representation ℂ G V) (σ : Representation ℂ P W)
    (hσ : ∀ (n : N) (w : W), σ ⟨n.val, hNP n.property⟩ w = w)
    (f : ρ.IntertwiningMap (smoothInduced P σ)) :
    Jacquet.Coinvariants ρ N →ₗ[ℂ] W := by
  let e : V →ₗ[ℂ] W :=
    { toFun := fun v => eval P σ (f v) 1
      map_add' := fun _ _ => congrArg (fun φ => eval P σ φ 1) (map_add f _ _)
      map_smul' := fun _ _ => congrArg (fun φ => eval P σ φ 1) (map_smul f _ _) }
  have he : ∀ n : N, e ∘ₗ ρ n = e := by
    intro n
    ext v
    change eval P σ (f (ρ n v)) 1 = eval P σ (f v) 1
    rw [Representation.IntertwiningMap.isIntertwining ρ _ f]
    change eval P σ (f v) (1 * n.val) = eval P σ (f v) 1
    rw [one_mul]
    have hcov := (f v).val.property ⟨n.val, hNP n.property⟩ 1
    change eval P σ (f v) (n.val * 1) =
      σ ⟨n.val, hNP n.property⟩ (eval P σ (f v) 1) at hcov
    simpa only [mul_one, hσ] using hcov
  exact Jacquet.lift ρ N e he

@[simp]
theorem coinvariantEvaluation_mk
    (P N : Subgroup G) (hNP : N ≤ P)
    (ρ : Representation ℂ G V) (σ : Representation ℂ P W)
    (hσ : ∀ (n : N) (w : W), σ ⟨n.val, hNP n.property⟩ w = w)
    (f : ρ.IntertwiningMap (smoothInduced P σ)) (v : V) :
    coinvariantEvaluation P N hNP ρ σ hσ f (Jacquet.mk ρ N v) =
      eval P σ (f v) 1 := rfl

/-- The vanishing part of first adjointness, directly by evaluation and descent. -/
theorem intertwiner_eq_zero_of_coinvariants
    (P N : Subgroup G) (hNP : N ≤ P)
    (ρ : Representation ℂ G V) (σ : Representation ℂ P W)
    (hσ : ∀ (n : N) (w : W), σ ⟨n.val, hNP n.property⟩ w = w)
    [Subsingleton (Jacquet.Coinvariants ρ N)]
    (f : ρ.IntertwiningMap (smoothInduced P σ)) : f = 0 := by
  let l := coinvariantEvaluation P N hNP ρ σ hσ f
  have he0 (v : V) : eval P σ (f v) 1 = 0 := by
    change l (Jacquet.mk ρ N v) = 0
    rw [Subsingleton.elim (Jacquet.mk ρ N v) 0, map_zero]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h := he0 (ρ g v)
  change eval P σ (f (ρ g v)) 1 = 0 at h
  rw [Representation.IntertwiningMap.isIntertwining ρ _ f] at h
  change eval P σ (f v) (1 * g) = 0 at h
  change eval P σ (f v) g = 0
  simpa only [one_mul] using h

end Langlands.Induction

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- A quasicuspidal representation has no nonzero map to proper refined induction. -/
theorem refinedInduced_intertwiner_eq_zero
    (hS : refinedParabolic F B S ≠ ⊤)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (refinedLevi F B S) W)
    (χ : refinedLevi F B S →* ℂˣ) (hρ : IsLeviQuasicuspidal B ρ)
    (f : ρ.IntertwiningMap (normalizedRefinedInducedOf B S χ σ)) : f = 0 := by
  let := hρ S hS
  apply Induction.intertwiner_eq_zero_of_coinvariants
    (refinedParabolic F B S) (refinedUnipotent F B S)
    (refinedUnipotent_le_parabolic F B S) ρ
    (refinedInducingRepresentation B S χ σ) ?_ f
  intro u w
  have hp : refinedLeviProjection F B S
      ⟨u.val, refinedUnipotent_le_parabolic F B S u.property⟩ = 1 :=
    (mem_refinedUnipotentRadical F B S _).mpr u.property
  change (χ (refinedLeviProjection F B S _) : ℂ) •
    σ (refinedLeviProjection F B S _) w = w
  rw [hp, map_one, map_one]
  simp


/-- If one of two complementary invariant subspaces is zero, inclusion of the
other is an actual smooth-representation isomorphism. -/
def complementIsoOfSubsingleton
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F))
    (U Q : Subrepresentation A.representation)
    (hcompl : IsCompl U.toSubmodule Q.toSubmodule)
    [hzero : Subsingleton (SmoothRep.subrepresentation A U)] :
    A ≅ SmoothRep.subrepresentation A Q := by
  have hU : U.toSubmodule = ⊥ := by
    apply le_antisymm
    · intro v hv
      have h : (⟨v, hv⟩ : SmoothRep.subrepresentation A U) = 0 :=
        hzero.elim _ _
      change v = 0
      exact congrArg Subtype.val h
    · exact bot_le
  have hQ : Q.toSubmodule = ⊤ := by
    simpa only [hU, bot_sup_eq] using hcompl.sup_eq_top
  let f := SmoothRep.hom (SmoothRep.subtype A Q)
  have hf : Function.Bijective f := by
    refine ⟨SmoothRep.subtype_injective A Q, ?_⟩
    intro v
    refine ⟨⟨v, ?_⟩, rfl⟩
    change v ∈ Q.toSubmodule
    rw [hQ]
    trivial
  exact (SmoothRep.mkIso (f.ofBijective hf)).symm

end Langlands.CuspidalSupport

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The quasicuspidal subrepresentation of an actual proper normalized
refined induction is zero, without any admissibility restriction. -/
theorem induced_quasicuspidal_subrepresentation_subsingleton :
    letI := T.topology
    ∀ (S : BlockRefinement B), refinedParabolic F.Carrier B S ≠ ⊤ →
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S))
      (U : Subrepresentation ((T.normalizedRefinedInductionFunctor B S).obj A).representation),
      IsLeviQuasicuspidal B (SmoothRep.subrepresentation _ U).representation →
      Subsingleton (SmoothRep.subrepresentation _ U) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro S hS A U hU
  let I := (T.normalizedRefinedInductionFunctor B S).obj A
  let f := SmoothRep.hom (SmoothRep.subtype I U)
  have hf : f = 0 := refinedInduced_intertwiner_eq_zero B S hS
    (SmoothRep.subrepresentation I U).representation A.representation
    (T.refinedLeviHalfModulus B S) hU f
  refine ⟨fun x y => SmoothRep.subtype_injective I U ?_⟩
  change f x = f y
  rw [hf]
  rfl

end Langlands.CuspidalSupport
