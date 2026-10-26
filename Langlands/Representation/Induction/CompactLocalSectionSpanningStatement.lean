import Langlands.Representation.Induction.CompactLocalSection

/-! Spanning target for compact induction by translated identity-centered sections. -/

namespace Langlands.Induction

universe uG uV

/-- Actual compact induction is spanned by right translates of compact
double-coset sections centered at the identity. This defines a proposition;
it does not prove the spanning assertion. -/
def CompactLocalSectionSpanning : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (sigma : Representation ℂ H V),
      Submodule.span ℂ
        {f : CompactFunctions H sigma |
          ∃ (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
            (v : V) (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K 1).toSubgroup),
            f = compactInduced H sigma g
              (compactDoubleCosetSection H sigma K hK 1 v hv)} = ⊤

end Langlands.Induction
