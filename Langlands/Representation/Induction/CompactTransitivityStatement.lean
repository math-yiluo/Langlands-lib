import Langlands.Representation.Induction.SplitQuotientStatement

/-!
# Natural compact induction in stages

Compact induction from a closed subgroup `H` through a closed intermediate subgroup `P`,
compared naturally with compact induction from `H` directly.
-/

open CategoryTheory

namespace Langlands.Induction

universe uG uV

/-- For a Hausdorff topological group `G` with a compact-open subgroup neighborhood basis and
closed subgroups `H ≤ P`, there is a family of `G`-equivalences, natural in the smooth complex
`H`-representation `A`, from compact induction from `P` of compact induction from
`H.subgroupOf P` of `A` restricted along `Subgroup.subgroupOfEquivOfLe`, to compact induction
from `H` of `A`, given by `(e F)(x) = F(x)(1)`. -/
def CompactInductionTransitivityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H P : Subgroup G), IsClosed (H : Set G) → IsClosed (P : Set G) → ∀ hHP : H ≤ P,
      let φ : H.subgroupOf P →* H := (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
      ∃ e : ∀ A : Langlands.SmoothRep.{0, uG, uV} ℂ H,
          Representation.Equiv
            (compactInduced P (compactInduced (H.subgroupOf P) (A.representation.comp φ)))
            (compactInduced H A.representation),
        (∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
            (F : CompactFunctions P (compactInduced (H.subgroupOf P) (A.representation.comp φ)))
            (x : G),
          eval H A.representation (e A F).val x =
            eval (H.subgroupOf P) (A.representation.comp φ)
              (eval P (compactInduced (H.subgroupOf P) (A.representation.comp φ)) F.val x).val
              1) ∧
        (∀ (A B : Langlands.SmoothRep.{0, uG, uV} ℂ H) (T : A ⟶ B)
            (F : CompactFunctions P (compactInduced (H.subgroupOf P) (A.representation.comp φ))),
          e B (compactInducedMap P
              (compactInducedMap (H.subgroupOf P)
                (restrictAlongMap φ (Langlands.SmoothRep.hom T))) F) =
            compactInducedMap H (Langlands.SmoothRep.hom T) (e A F))

end Langlands.Induction
