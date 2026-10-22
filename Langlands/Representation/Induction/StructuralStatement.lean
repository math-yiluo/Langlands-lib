import Langlands.Representation.Induction.Definitions
import Mathlib.Basic.Complex.Basic

namespace Langlands.Induction

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

section Clauses

variable [IsTopologicalGroup G] (H : Subgroup G)

/-- Evaluation-at-identity formula for the smooth-induction adjunction. -/
def SmoothFrobeniusClause : Prop :=
  ∀ (rho : Representation ℂ G U) (sigma : Representation ℂ H V),
      IsSmooth rho → IsSmooth sigma →
      ∃ e : (rho.IntertwiningMap (smoothInduced H sigma)) ≃ₗ[ℂ]
        (Representation.IntertwiningMap (rho.comp H.subtype) sigma),
        ∀ f u, e f u = eval H sigma (f u) 1

/-- Exactness of the actual postcomposition maps for both induction spaces. -/
def InductionExactnessClause : Prop :=
  ∀ (rho : Representation ℂ H U) (sigma : Representation ℂ H V)
      (tau : Representation ℂ H W)
      (i : rho.IntertwiningMap sigma) (p : sigma.IntertwiningMap tau),
      Function.Injective i → Function.Surjective p →
      LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap →
      IsSmooth sigma →
      (Function.Injective (smoothInducedMap H i) ∧
        LinearMap.range (smoothInducedMap H i).toLinearMap =
          LinearMap.ker (smoothInducedMap H p).toLinearMap ∧
        Function.Surjective (smoothInducedMap H p)) ∧
      (Function.Injective (compactInducedMap H i) ∧
        LinearMap.range (compactInducedMap H i).toLinearMap =
          LinearMap.ker (compactInducedMap H p).toLinearMap ∧
        Function.Surjective (compactInducedMap H p))

/-- Coincidence and admissibility for a compact actual left coset space. -/
def CompactQuotientClause : Prop :=
  ∀ sigma : Representation ℂ H V,
      CompactSpace (LeftQuotient H) → IsAdmissible sigma →
      Function.Bijective (compactInclusion H sigma) ∧
        IsAdmissible (smoothInduced H sigma)

/-- Scalar character compatibility with its explicit function formula. -/
def InductionTwistClause : Prop :=
  ∀ (chi : SmoothCharacter ℂ G) (sigma : Representation ℂ H V),
      IsSmooth sigma →
      (∃ e : (twist chi.toMonoidHom (smoothInduced H sigma)).Equiv
        (smoothInduced H (twist (chi.toMonoidHom.comp H.subtype) sigma)),
        ∀ f x,
          eval H (twist (chi.toMonoidHom.comp H.subtype) sigma) (e f) x =
            (chi.toMonoidHom x : ℂ) • eval H sigma f x) ∧
      (∃ e : (twist chi.toMonoidHom (compactInduced H sigma)).Equiv
        (compactInduced H (twist (chi.toMonoidHom.comp H.subtype) sigma)),
        ∀ f x,
          eval H (twist (chi.toMonoidHom.comp H.subtype) sigma) (e f).1 x =
            (chi.toMonoidHom x : ℂ) • eval H sigma f.1 x)

/-- A prescribed central scalar action passes to both induced actions. -/
def InductionCentralActionClause : Prop :=
  ∀ (hZH : Subgroup.center G ≤ H) (chi : Subgroup.center G →* ℂˣ)
      (sigma : Representation ℂ H V),
      (∀ (z : Subgroup.center G) (v : V),
        sigma ⟨(z : G), hZH z.property⟩ v = (chi z : ℂ) • v) →
      (∀ (z : Subgroup.center G) f,
        smoothInduced H sigma (z : G) f = (chi z : ℂ) • f) ∧
      (∀ (z : Subgroup.center G) f,
        compactInduced H sigma (z : G) f = (chi z : ℂ) • f)

/-- Transitivity through an actual intermediate closed subgroup. -/
def InductionTransitivityClause : Prop :=
  ∀ (P : Subgroup G) (hHP : H ≤ P),
      IsClosed (P : Set G) →
      ∀ rho : Representation ℂ H V, IsSmooth rho →
      let rhoP : Representation ℂ (H.subgroupOf P) V :=
        rho.comp (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
      (∃ e : (smoothInduced P (smoothInduced (H.subgroupOf P) rhoP)).Equiv
        (smoothInduced H rho),
        ∀ f x, eval H rho (e f) x =
          eval (H.subgroupOf P) rhoP
            (eval P (smoothInduced (H.subgroupOf P) rhoP) f x) 1) ∧
      (∃ e : (compactInduced P (compactInduced (H.subgroupOf P) rhoP)).Equiv
        (compactInduced H rho),
        ∀ f x, eval H rho (e f).1 x =
          eval (H.subgroupOf P) rhoP
            (eval P (compactInduced (H.subgroupOf P) rhoP) f.1 x).1 1)

/-- The open-subgroup compact-induction adjunction and its support formula. -/
def OpenSubgroupAdjunctionClause : Prop :=
  IsOpen (H : Set G) →
      ∀ (sigma : Representation ℂ H V) (tau : Representation ℂ G W),
      IsSmooth sigma → IsSmooth tau →
      ∃ e : ((compactInduced H sigma).IntertwiningMap tau) ≃ₗ[ℂ]
        (Representation.IntertwiningMap sigma (tau.comp H.subtype)),
        ∀ T f, (∀ x : G, x ∉ H → eval H sigma f.1 x = 0) →
          e T (eval H sigma f.1 1) = T f

end Clauses

/-- Structural induction properties over a Hausdorff topological group with a
compact-open neighborhood basis and a closed inducing subgroup. The seven
concrete clauses above are not assumed theorem parameters. -/
def StructuralStatement : Prop :=
  ∀ [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ H : Subgroup G, IsClosed (H : Set G) →
    SmoothFrobeniusClause (U := U) (V := V) H ∧
    InductionExactnessClause (U := U) (V := V) (W := W) H ∧
    CompactQuotientClause (V := V) H ∧
    InductionTwistClause (V := V) H ∧
    InductionCentralActionClause (V := V) H ∧
    InductionTransitivityClause (V := V) H ∧
    OpenSubgroupAdjunctionClause (V := V) (W := W) H

end Langlands.Induction
