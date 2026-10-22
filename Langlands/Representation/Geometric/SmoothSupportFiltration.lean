import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-! Natural support filtrations of restricted smooth induction. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smooth induction of arbitrary algebraic covariance data, restricted to Q. -/
def rawRestrictedSmoothInduction (P Q : Subgroup G) :
    Rep.{uV} R P ⥤ Rep.{max uG uV} R Q :=
  Induction.smoothInductionFunctor P ⋙ SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype

/-- Smoothly induced functions supported in an actual invariant subset of
`P \ G`, for arbitrary algebraic covariance representations. -/
def rawSmoothSupportSubfunctor (P Q : Subgroup G) (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U) :
    RepSubfunctor (rawRestrictedSmoothInduction.{uR, uG, uV} (R := R) P Q) where
  obj A :=
    { toSubmodule :=
        { carrier := {f | ∀ x : G, Induction.eval P A.ρ f x ≠ 0 →
              Induction.quotientMap P x ∈ U}
          zero_mem' := by
            intro x hx
            exact False.elim (hx rfl)
          add_mem' := by
            intro f g hf hg x hx
            by_cases hfx : Induction.eval P A.ρ f x = 0
            · apply hg x
              intro hgx
              apply hx
              change Induction.eval P A.ρ f x +
                Induction.eval P A.ρ g x = 0
              rw [hfx, hgx, add_zero]
            · exact hf x hfx
          smul_mem' := by
            intro a f hf x hx
            apply hf x
            intro hfx
            apply hx
            change a • Induction.eval P A.ρ f x = 0
            rw [hfx, smul_zero] }
      apply_mem_toSubmodule := by
        intro q f hf x hx
        have hu := hU q⁻¹ (Induction.quotientMap P (x * (q : G)))
          (hf (x * (q : G)) hx)
        simpa [Induction.quotientRight, Induction.quotientMap, mul_assoc] using hu }
  map_mem := by
    intro A B f v hv x hx
    apply hv x
    intro hvx
    apply hx
    change f.hom (Induction.eval P A.ρ v x) = 0
    rw [hvx, map_zero]

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ}

/-- The natural filtration by support in initial orbit unions. Monotonicity
follows from containment, the zero endpoint from the empty union, and the full
endpoint from the orbit cover. Graded-piece isomorphisms are separate. -/
def rawSmoothSupportFiltration (s : OrderedDoubleCosets P Q n) :
    RepFunctorFiltration (rawRestrictedSmoothInduction.{uR, uG, uV} (R := R) P Q) n where
  step k := rawSmoothSupportSubfunctor P Q (s.initialOrbits k)
    (fun q _ hx => s.initialOrbits_right_invariant k q hx)
  monotone A := by
    intro i j hij f hf x hx
    exact s.initialOrbits_monotone hij (hf x hx)
  zero A := by
    apply le_antisymm
    · intro f hf
      change f = 0
      apply Subtype.ext
      apply Subtype.ext
      funext x
      by_contra hx
      have hu := hf x hx
      simp [s.initialOrbits_zero] at hu
    · exact bot_le
  top A := by
    apply le_antisymm le_top
    intro f _ x _
    rw [s.initialOrbits_top]
    trivial

end OrderedDoubleCosets

end Langlands.Geometric
