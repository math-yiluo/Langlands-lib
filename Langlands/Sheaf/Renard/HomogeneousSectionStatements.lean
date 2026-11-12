import Langlands.Sheaf.Renard.HomogeneousSections

/-!
# Renard III.3.2: original compact and smooth-global section comparisons

These are closed proposition targets. The forward maps are the already
published literal alpha maps; the output beta maps must reconstruct actual
original sections, satisfy both inverse laws and the source stalk formula,
and be natural for the original equivariant sheaf morphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousSectionStatements

open CategoryTheory
open Langlands.Induction
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections

attribute [local instance] homogeneousAction

/-- Renard III.3.2: compact alpha has a natural equivariant inverse with the displayed
original-stalk beta formula, under the source's t.d. and countability hypotheses. -/
def CompactAlphaBetaStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G],
    Langlands.Topology.IsLocallyProfinite G →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∃ beta : ∀ F : SmoothActionSheaf G (LeftQuotient H),
      Representation.IntertwiningMap (compactInduced H (stalkRepresentation H F.obj))
        (compactRepresentation F.obj),
      (∀ F,
        Function.LeftInverse (beta F) (alphaCompact H F) ∧
        Function.RightInverse (beta F) (alphaCompact H F) ∧
        ∀ (f : CompactFunctions H (stalkRepresentation H F.obj)) (g : G),
          (CompactSections.ordinary F.obj.obj).Γgerm (g • origin H) (beta F f).val =
            (Godement.stalkPull F.obj.obj g⁻¹ (g • origin H) (origin H)
              (inv_smul_smul g (origin H))).hom
                (eval H (stalkRepresentation H F.obj) f.val g⁻¹)) ∧
      ∀ (F F' : SmoothActionSheaf G (LeftQuotient H)) (u : F ⟶ F'),
        (CompactSections.map u.hom).comp (beta F) =
          (beta F').comp
            (compactInducedMap H
              ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map u.hom).hom)

/-- Renard III.3.2: smooth-global alpha has a natural equivariant inverse on the actual
smooth part, with the analogous displayed original-stalk beta formula. -/
def SmoothGlobalAlphaBetaStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G],
    Langlands.Topology.IsLocallyProfinite G →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∃ beta : ∀ F : SmoothActionSheaf G (LeftQuotient H),
      Representation.IntertwiningMap (smoothInduced H (stalkRepresentation H F.obj))
        (Langlands.smoothPart (globalRepresentation F.obj)),
      (∀ F,
        Function.LeftInverse (beta F) (alphaSmoothGlobal H F.obj) ∧
        Function.RightInverse (beta F) (alphaSmoothGlobal H F.obj) ∧
        ∀ (f : SmoothFunctions H (stalkRepresentation H F.obj)) (g : G),
          (CompactSections.ordinary F.obj.obj).Γgerm (g • origin H) (beta F f).val =
            (Godement.stalkPull F.obj.obj g⁻¹ (g • origin H) (origin H)
              (inv_smul_smul g (origin H))).hom
                (eval H (stalkRepresentation H F.obj) f g⁻¹)) ∧
      ∀ (F F' : SmoothActionSheaf G (LeftQuotient H)) (u : F ⟶ F'),
        (Langlands.smoothMap
            ((sectionRepresentation ℂ G (LeftQuotient H)).map u.hom).hom).comp (beta F) =
          (beta F').comp
            (smoothInducedMap H
              ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map u.hom).hom)

/-- Both literal section comparison assertions of Renard III.3.2. -/
def SectionComparisonStatement : Prop :=
  CompactAlphaBetaStatement ∧ SmoothGlobalAlphaBetaStatement

end Langlands.Sheaf.Renard.HomogeneousSectionStatements
