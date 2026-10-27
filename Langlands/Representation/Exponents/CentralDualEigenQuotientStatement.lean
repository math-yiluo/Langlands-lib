import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Classification.ConstituentRelations
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Irreducible admissible scalar quotients detected by central dual eigenfunctionals

A derived generic statement: a finitely generated admissible complex
representation with a nonzero full algebraic dual functional on which a
central parameter group acts through a prescribed character has an actual
irreducible admissible quotient on which that parameter group acts by exactly
this character. This is a statement, not a proof.
-/

namespace Langlands

universe uG uC uV

/-- Let `G` be a topological group in which compact open subgroups are cofinal
among open subgroups, `z : C →* G` a homomorphism with central image and
`χ : C →* ℂˣ` a character. Every complex representation of `G` that is finitely
generated over the group algebra, admissible, and has a nonzero full algebraic
dual functional `φ` with `φ (ρ (z c) v) = χ c * φ v` admits an actual surjective
intertwiner onto an irreducible admissible representation in the same carrier
universe on which every `z c` acts as the scalar `χ c`. -/
def CentralDualEigenQuotientStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H) →
    ∀ (C : Type uC) [Group C] (z : C →* G),
      (∀ (c : C) (g : G), z c * g = g * z c) →
      ∀ (χ : C →* ℂˣ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V),
        Module.Finite (MonoidAlgebra ℂ G) ρ.asModule →
        IsAdmissible ρ →
        (∃ φ : Module.Dual ℂ V, φ ≠ 0 ∧
          ∀ (c : C) (v : V), φ (ρ (z c) v) = (χ c : ℂ) * φ v) →
        ∃ S : Rep.{uV} ℂ G,
          Representation.IsIrreducible S.ρ ∧ IsAdmissible S.ρ ∧
            Classification.HasScalarCharacter S.ρ z χ ∧
            ∃ q : ρ.IntertwiningMap S.ρ, Function.Surjective q

end Langlands
