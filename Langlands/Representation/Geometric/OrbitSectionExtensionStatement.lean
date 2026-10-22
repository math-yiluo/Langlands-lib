import Langlands.Representation.Geometric.ClosedSubgroupStatement

/-! Pointwise compact-section extension from a closed orbit in an open subset. -/

namespace Langlands.Geometric

universe uG uV

/-- A compactly induced section on the actual orbit extends to an ambient
compactly induced section supported in any open set in which that orbit is closed.
This is a prerequisite assertion, not an assumed construction. -/
def ClosedOrbitSectionExtension : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
    (P Q : Subgroup G),
    IsClosed (P : Set G) → IsClosed (Q : Set G) →
    ∀ (w : G) (U : Set (Induction.LeftQuotient P)),
      IsOpen U → cosetOrbit P Q w ⊆ U →
      IsClosed ((fun x : U => (x : Induction.LeftQuotient P)) ⁻¹' cosetOrbit P Q w) →
      ∀ (A : Induction.SmoothRep.{0, uG, uV} ℂ P)
        (g : Induction.CompactFunctions (orbitStabilizer P Q w)
          (A.obj.ρ.comp (stabilizerToInducing P Q w))),
        ∃ f : Induction.CompactFunctions P A.obj.ρ,
          (∀ x : G, Induction.eval P A.obj.ρ f.val x ≠ 0 →
            Induction.quotientMap P x ∈ U) ∧
          ∀ q : Q, Induction.eval P A.obj.ρ f.val (w⁻¹ * (q : G)) =
            Induction.eval (orbitStabilizer P Q w)
              (A.obj.ρ.comp (stabilizerToInducing P Q w)) g.val q

end Langlands.Geometric
