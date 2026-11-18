import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.FiniteFreeCochainModels
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleCech
import Langlands.Cohomology.SiteCech.FiniteTupleEquivariantModel
import Langlands.Sheaf.Equivariant.AnalyticFiniteLiftDiagramSections

/-! # Analytic finite cochain models from compact lifted tuple cones -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech
open scoped Simplicial

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]
variable {U : QuasiEtaleSite X}
variable (s : FiniteBasisCover (quasiEtaleTopology X) (compactLiftBasisObject ρ) U)
variable (b : ∀ n, (Fin (n + 1) → Fin s.size) → CompactLiftBasis ρ)
variable (c : ∀ n (α : Fin (n + 1) → Fin s.size),
  WidePullbackCone (fun j => s.arrow (α j)))
variable (hc : ∀ n α, IsLimit (c n α))
variable (e : ∀ n α, (c n α).pt ≅ compactLiftBasisObject ρ (b n α))

local instance (S : Type w) [CommRing S]
    [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} S)] (m : ℕ) :
    HasColimitsOfShape (Discrete (Fin m))
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{w} S)) :=
  Sheaf.instHasColimitsOfShape

/-- Supplied compact lifted tuple cones and compact-lift compatibility give
an actual finite signed model fixing the sections of a specified cochain. -/
def finiteFreeModelOfCompactTupleCones
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (n : ℕ)
    (x : (freeCechChainComplex (quasiEtaleTopology X) R
      (s.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))).X (n + 1) ⟶
        (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)
    (Q : OpenSubgroup G) :
    Σ H : OpenSubgroup G,
      {M : OpenSubgroupFiniteFreeThreeTermModel.{u, v, uL, z} ρ R
        (freeCechChainComplex (quasiEtaleTopology X) R
          (s.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))) H n //
        M.FixesCochain I x ∧ H ≤ Q} := by
  classical
  let size (k : ℕ) := Fintype.card (Fin (k + 1) → Fin s.size)
  let basis (k : ℕ) (i : Fin (size k)) :=
    b k ((Fintype.equivFin _).symm i)
  let obj (k : ℕ) (i : Fin (size k)) := compactLiftBasisObject ρ (basis k i)
  let V := Fin (size (n + 2)) ⊕ (Fin (size (n + 1)) ⊕ Fin (size n))
  let W : V → QuasiEtaleSite X := Sum.elim (obj (n + 2))
    (Sum.elim (obj (n + 1)) (obj n))
  let l : ∀ v, ActionLift ρ (W v).hom := fun
    | Sum.inl i => Classical.choice (basis (n + 2) i).property.2
    | Sum.inr (Sum.inl i) => Classical.choice (basis (n + 1) i).property.2
    | Sum.inr (Sum.inr i) => Classical.choice (basis n i).property.2
  have hW : ∀ v, IsCompactSpace (W v).left := by
    rintro (i | (i | i))
    · exact (basis (n + 2) i).property.1
    · exact (basis (n + 1) i).property.1
    · exact (basis n i).property.1
  let E := (Fin (n + 3) × Fin (size (n + 2))) ⊕
    (Fin (n + 2) × Fin (size (n + 1)))
  let source : E → V := Sum.elim
    (fun ji => Sum.inl ji.2) (fun ji => Sum.inr (Sum.inl ji.2))
  let target : E → V := Sum.elim
    (fun ji => Sum.inr (Sum.inl (cechTupleIndexMap (SimplexCategory.δ ji.1) ji.2)))
    (fun ji => Sum.inr (Sum.inr (cechTupleIndexMap (SimplexCategory.δ ji.1) ji.2)))
  let arrow : ∀ a, W (source a) ⟶ W (target a) := by
    rintro (⟨j, i⟩ | ⟨j, i⟩)
    · exact s.tupleMapArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ)
        b c hc e (SimplexCategory.δ j) i
    · exact s.tupleMapArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ)
        b c hc e (SimplexCategory.δ j) i
  let t : ∀ v, I.obj.obj.obj (op ((ι quasiEtale ρ).obj (W v))) := fun
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl i) =>
        finiteFreeCochainSections.{u, v, uL} R (obj (n + 1))
          ((s.cechPresentationOfCones (quasiEtaleTopology X)
            (compactLiftBasisObject ρ) b c hc e).freeTermIso
              (quasiEtaleTopology X) (compactLiftBasisObject ρ) R (n + 1)) _ x i
    | Sum.inr (Sum.inr _) => 0
  let d := commonEquivariantFixedLiftDiagram W l source target arrow Q I.obj.obj t
    hC I.property hW
  let upper := fun i : Fin (size (n + 2)) => d.diagram.globalLift (Sum.inl i)
  let middle := fun i : Fin (size (n + 1)) => d.diagram.globalLift (Sum.inr (Sum.inl i))
  let lower := fun i : Fin (size n) => d.diagram.globalLift (Sum.inr (Sum.inr i))
  have hupper_face : ∀ (j : Fin (n + 3)) i,
      GlobalLift.IsEquivariant
        (L := s.tupleLiftFamily (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b (n + 2) upper (fun _ => rfl) i)
        (M := s.tupleLiftFamily (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b (n + 1) middle (fun _ => rfl)
            (cechTupleIndexMap (SimplexCategory.δ j) i))
        (s.tupleMapArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b c hc e (SimplexCategory.δ j) i) := by
    intro j i g
    exact d.diagram.globalLift_equivariant (Sum.inl ⟨j, i⟩) g
  have hlower_face : ∀ (j : Fin (n + 2)) i,
      GlobalLift.IsEquivariant
        (L := s.tupleLiftFamily (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b (n + 1) middle (fun _ => rfl) i)
        (M := s.tupleLiftFamily (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b n lower (fun _ => rfl) (cechTupleIndexMap (SimplexCategory.δ j) i))
        (s.tupleMapArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ)
          b c hc e (SimplexCategory.δ j) i) := by
    intro j i g
    exact d.diagram.globalLift_equivariant (Sum.inr ⟨j, i⟩) g
  let M := s.finiteFreeThreeTermModelOfCones
    (quasiEtaleTopology X) (compactLiftBasisObject ρ) b c hc e R
    (compactLiftSystem (ρ.comp (d.diagram.subgroup : Subgroup G).subtype)) n
    upper middle lower (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun i => d.diagram.globalLift_eventuallyEquivariant hC hW (Sum.inl i))
    (fun i => d.diagram.globalLift_eventuallyEquivariant hC hW (Sum.inr (Sum.inl i)))
    (fun i => d.diagram.globalLift_eventuallyEquivariant hC hW (Sum.inr (Sum.inr i)))
    hupper_face hlower_face
  refine ⟨d.diagram.subgroup, M, ?_, d.diagram.le_bound⟩
  intro i g
  exact (d.globalFixedSection (Sum.inr (Sum.inl i))).property g

variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

include b c hc e in
/-- Compact lifted tuple cones and compact-lift compatibility make the actual
cover Cech Hom complex exact against every injective quasi-etale coefficient. -/
theorem exactAt_of_compactTupleCones
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (n : ℕ) :
    ((freeCechChainComplex (quasiEtaleTopology X) R
      (s.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))).linearYonedaObj R
        ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)).ExactAt (n + 1) := by
  have := s.presheafArrow_isLocallySurjective
    (quasiEtaleTopology X) (compactLiftBasisObject ρ)
  have := quasiIso_freeCechAugmentation_of_locally_surjective
    (quasiEtaleTopology X) R
    (s.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))
  apply exactAt_of_openSubgroupFiniteFreeModels.{u, v, uL, z} ρ R _ I n
    (chainAugmentation_positive_exact _
      (freeCechAugmentation (quasiEtaleTopology X) R
        (s.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))) n)
  intro x _
  let d := finiteFreeModelOfCompactTupleCones.{u, v, uL, z}
    ρ R s b c hc e hC I n x ⊤
  exact ⟨d.1, d.2.val, d.2.property.1⟩

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
