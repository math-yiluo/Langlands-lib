/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # ProEtaleLisseFiniteModels

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def comparisonConstantIso (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X ≅
        constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (Etale.isTerminalMkId X)).comp
      (AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X)).ofNatIsoRight
    ((toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{u + 1} Λ)
      X.smallEtaleTopology (ProEt.topology X) (op (Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} Λ) (ProEt.isTerminalMkId X))

/-- Finite étale local models remain finite pro-étale models after comparison.
Source: Stacks Project, Tag 099Y, proof of `lemma-compare-locally-constant`.
The proof transports each finite constant trivialization through comparison pullback,
its restriction comparison, and the constant-sheaf comparison.
(auxiliary; not a blueprint node) -/
theorem comparison_finite_models_of_etale_finite_values
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∃ d : LocallyConstantDatum G, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (G.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (X.smallEtaleTopology.over
            (d.cover.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (g i)).obj
            ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G)) ≅
            (constantSheaf (Scheme.ProEt.topology (W i))
              (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨d, hd⟩ := hG
  refine ⟨ULift.{u + 1} d.cover.I₀, (fun i ↦ d.cover.X i.down),
    (fun i ↦ d.cover.f i.down), ?_, ?_⟩
  · have heq : Presieve.ofArrows
        (fun i : ULift.{u + 1} d.cover.I₀ ↦ d.cover.X i.down)
        (fun i ↦ d.cover.f i.down) = d.cover.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (ι := ULift.{u + 1} d.cover.I₀)
        (Y := fun i ↦ d.cover.X i.down) ⟨i⟩
    rw [heq]
    exact etalePrecoverage_le_proetalePrecoverage _ d.cover.mem₀
  · rintro ⟨i⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i
    let V := d.cover.etalePrecoverageToEtale i
    let E := (Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)).functor
    let eG : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj G ≅
        (constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
      (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) V G).symm ≪≫
        E.mapIso e ≪≫ ((Etale.overEquiv V).constantSheafSheafCongrIso
          (X.smallEtaleTopology.over V) V.left.smallEtaleTopology
          (ModuleCat.{u + 1} Λ) Over.mkIdTerminal).app M
    exact ⟨M, hM, ⟨
      (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} Λ) V.hom).app G ≪≫
      (AlgebraicGeometry.ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} Λ) V.left).mapIso eG ≪≫
      (comparisonConstantIso V.left Λ).app M⟩⟩

end AlgebraicGeometry.Scheme
