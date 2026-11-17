import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Torus.Induced

/-!
# Weakly induced tori over the maximal unramified extension (KP Definition B.6.2)

Tamely ramified finite extensions `L/K` of `K = F^ur` inside `F^sep`, weakly induced
`K`-tori, and the torus clause of condition (1) of KP §13.5.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An intermediate field `L` of `F^sep/K`, `K = F^ur`, is tamely ramified over `K`: some
`e > 0` prime to the residue characteristic `p` of `F` satisfies `|x|^e ∈ |F^×|` for every
nonzero `x ∈ L`. For finite `L/K` this says that the ramification index of `L/K` is prime
to `p`; the residue field of `K` is separably closed, so there is no residue condition. -/
def IsTamelyRamifiedOverUnramifiedClosure
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ¬ ringChar 𝓀[F] ∣ e ∧
    ∀ x : L, x ≠ 0 → ∃ a : F,
      intermediateValuation F L x ^ e =
        LocalGalois.Separable.sepClosureValuation F (algebraMap F (SeparableClosure F) a)

/-- KP Definition B.6.2 over `K = F^ur`: the `K`-torus `T` is weakly induced if `T_L` is an
induced torus for some finite tamely ramified extension `L/K`, taken inside `F^sep`. -/
def IsWeaklyInducedTorus
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) : Prop :=
  ∃ L : IntermediateField (UnramifiedClosure F) (SeparableClosure F),
    FiniteDimensional (UnramifiedClosure F) L ∧ IsTamelyRamifiedOverUnramifiedClosure F L ∧
      IsInducedTorus
        ((CommGroupScheme.baseChange (algebraBaseMap (UnramifiedClosure F) L)).obj T)

/-- The torus clause of condition (1) of KP §13.5: a maximally split maximal torus of
`G_K`, `K = F^ur`, is weakly induced. -/
def HasWeaklyInducedMaximallySplitTorus
    (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (i : T.toGrp ⟶ GaloisPointComparison.baseChanged F (UnramifiedClosure F) G),
    IsMaximallySplitMaximalTorus i ∧ IsWeaklyInducedTorus F T

end Langlands.Geometry.Building
