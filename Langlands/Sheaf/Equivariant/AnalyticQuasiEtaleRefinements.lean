import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Langlands.Geometry.Analytic.QuasiEtaleActionLiftStatement

/-!
# Finite equivariant refinements on the twisted quasi-étale site

Let a topological group `G` act on an analytic space `X`. Quasi-étale `G`-sheaves
are the discrete sheaves on the twisted quasi-étale site for the lifts of the
action to compact quasi-étale objects. Their abelian structure and their derived
compactly supported cohomology use the finite equivariant refinement condition
`HasFiniteEquivariantRefinements` of this local action system. It follows from
three conditions on the plain quasi-étale site of `X`:

* every covering sieve of a compact object contains a finite family of arrows from
  compact objects that generates a covering sieve;
* every compact object carries a lift of the action (the existence half of
  `QuasiEtaleActionLiftStatement`);
* for a morphism of compact objects over `X`, any two lifts are compatible with it
  on an open subgroup (functoriality of Berkovich's canonical actions).
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Conditions

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- Finite compact refinements: every covering sieve of a compact quasi-étale object
contains a finite family of arrows from compact quasi-étale objects that generates a
covering sieve. -/
def HasFiniteCompactQuasiEtaleRefinements : Prop :=
  ∀ ⦃U : QuasiEtaleSite X⦄, IsCompactSpace U.left → ∀ ⦃S : Sieve U⦄,
    S ∈ quasiEtaleTopology X U →
      ∃ (n : ℕ) (V : Fin n → QuasiEtaleSite X) (f : ∀ i, V i ⟶ U),
        (∀ i, IsCompactSpace (V i).left) ∧ (∀ i, S (f i)) ∧
          Sieve.ofArrows V f ∈ quasiEtaleTopology X U

variable {X} {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- Every compact quasi-étale object carries a lift of the action. -/
def HasCompactQuasiEtaleLifts : Prop :=
  ∀ ⦃V : QuasiEtaleSite X⦄, IsCompactSpace V.left → Nonempty (ActionLift ρ V.hom)

/-- Lifts on compact quasi-étale objects are compatible with morphisms over `X`: for
`f : V ⟶ U` and lifts `a` on `U` and `b` on `V`, the arrow `f` intertwines the two
actions on an open subgroup. -/
def HasCompatibleCompactQuasiEtaleLifts : Prop :=
  ∀ ⦃U V : QuasiEtaleSite X⦄ (f : V ⟶ U), IsCompactSpace U.left → IsCompactSpace V.left →
    ∀ (a : ActionLift ρ U.hom) (b : ActionLift ρ V.hom),
      ∃ N : Subgroup G, IsOpen (N : Set G) ∧ ∃ (ha : N ≤ a.subgroup) (hb : N ≤ b.subgroup),
        ∀ (g : G) (hg : g ∈ N),
          (b.action ⟨g, hb hg⟩).hom ≫ f.left = f.left ≫ (a.action ⟨g, ha hg⟩).hom

/-- The existence half of `QuasiEtaleActionLiftStatement` gives lifts on all compact
quasi-étale objects of a Hausdorff space with a continuous action. -/
theorem hasCompactQuasiEtaleLifts_of_actionLiftStatement [IsTopologicalGroup G]
    (hKL : QuasiEtaleActionLiftStatement.{u, v, z} K)
    (hX : T2Space (localizedSpaceFunctor.obj X)) (hρ : IsContinuousAction ρ) :
    HasCompactQuasiEtaleLifts ρ :=
  fun V hV => (hKL G X V.left ρ V.hom hX hρ V.prop hV).1

end Conditions

section Refinements

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] (ρ : G →* Aut X)

/-- The three conditions give finite equivariant refinements for the lifts on compact
quasi-étale objects. Refine a covering sieve of a compact object by the finite compact
family of its untwisted arrows, give each member a lift, and use the compatibility of
the lifts along each arrow on an open subgroup. -/
theorem hasFiniteEquivariantRefinements_compactLiftSystem
    (hA : HasFiniteCompactQuasiEtaleRefinements X) (hB : HasCompactQuasiEtaleLifts ρ)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) :
    (compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ) := by
  constructor
  rintro U H a ⟨hU, l, hH, rfl⟩ S hS
  obtain ⟨n, V, f, hV, hfS, hcov⟩ := hA hU hS
  let m : ∀ i, ActionLift ρ (V i).hom := fun i => (hB (hV i)).some
  refine ⟨n, fun i => (ι quasiEtale ρ).obj (V i), fun i => liftOpenSubgroup (m i),
    fun i => liftAction (U := (ι quasiEtale ρ).obj (V i)) (m i),
    fun i => (ι quasiEtale ρ).map (f i), fun i => ⟨hV i, m i, le_rfl, ?_⟩, fun i => hfS i,
    fun i => ?_, ?_⟩
  · exact MonoidHom.ext fun _ => rfl
  · obtain ⟨N, hN, hNl, hNm, hNf⟩ := hC (f i) hU (hV i) l (m i)
    refine isLocallyEquivariant_of_intertwines (⟨N, hN⟩ ⊓ H) inf_le_right
      (fun g hg => hNm hg.1) fun g hg => ?_
    refine hom_ext ((one_mul _).trans (mul_one _).symm) ?_
    exact hNf g⁻¹ (inv_mem hg.1)
  · change Sieve.functorPullback (ι quasiEtale ρ) _ ∈ quasiEtaleTopology X U.obj
    refine (quasiEtaleTopology X).superset_covering ?_ hcov
    rintro W g ⟨Y, e, _, ⟨i⟩, rfl⟩
    exact ⟨_, (ι quasiEtale ρ).map e, (ι quasiEtale ρ).map (f i), ⟨i⟩,
      ((ι quasiEtale ρ).map_comp e (f i)).symm⟩

end Refinements

end Langlands.Sheaf.Equivariant.Analytic
