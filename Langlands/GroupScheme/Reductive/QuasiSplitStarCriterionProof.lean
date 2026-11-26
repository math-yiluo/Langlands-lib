import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionStatement
import Langlands.GroupScheme.Reductive.StarActionQuasiSplitProof
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.SplitPinningExistenceProof
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.TorusTransportPinning
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # The absolute star criterion for quasi-split groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local notation "Ω" => SeparableClosure k
local notation "b" => algebraBaseMap k Ω
local notation "BC" => CommGroupScheme.baseChange b

/-- A `k`-torus that splits over the separable closure and whose geometric characters are
all fixed by the absolute Galois group is split over `k`. -/
private theorem split_of_fixes_characters
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus ((BC).obj T).toGrp)
    (hfix : ∀ (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice ((BC).obj T)),
      characterLattice.galoisRepresentation k Ω T σ χ = χ) : IsSplitTorus T.toGrp := by
  have hMT : IsMultiplicativeType T.toGrp :=
    (IsTorus.of_baseChange (K := Ω) hT.isTorus).isMultiplicativeType
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hS : IsSplitTorus S.toGrp := isSplitTorus_splitTorus I
  let e' : (BC).obj T ≅ (BC).obj S :=
    CommGroupScheme.isoOfGroupIso (e ≪≫ (splitTorus.baseChangeIso b I).symm)
  let a := characterLattice.isoOfEquivariantAbsoluteEquiv hMT hS.isTorus.isMultiplicativeType
    (characterLattice.congr e').toIntLinearEquiv (fun σ χ => by
      rw [hfix, TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus S hS])
  let aG : S.toGrp ≅ T.toGrp :=
    ⟨CommGroupScheme.groupHom a.hom, CommGroupScheme.groupHom a.inv,
      congrArg CommGroupScheme.groupHom a.hom_inv_id,
      congrArg CommGroupScheme.groupHom a.inv_hom_id⟩
  exact IsSplitTorus.of_iso aG.symm hS

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Triviality of the star action does not depend on the choice of Galois pinning data. -/
private theorem trivial_star_transport (d d' : GaloisPinningData k Ω G)
    (h : ∀ σ, d.starAction σ = 1) (σ : Ω ≃ₐ[k] Ω) : d'.starAction σ = 1 := by
  obtain ⟨_, _, e, _, _, _, he⟩ := StarActionIndependence.starActionIndependence k Ω G d d'
  apply Subtype.ext
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro χ
  obtain ⟨χ₀, rfl⟩ := e.weightEquiv.surjective χ
  have hc := he σ
  rw [h σ] at hc
  exact (congrArg (fun x => x.weightMap χ₀) hc).symm

/-- Quasi-split reductive groups split exactly when the absolute star action
on the full based root datum is trivial. -/
theorem quasiSplitStarCriterion : QuasiSplitStarCriterionStatement.{u} := by
  intro k _ G _ _ hQ d
  let K := SeparableClosure k
  let bc := algebraBaseMap k K
  constructor
  · rintro ⟨T, i, hT, hi⟩
    obtain ⟨p⟩ := splitPinningExistence k G hQ.1 T hT i hi
    have : IsAffineHom ((GroupScheme.baseChange bc).obj G).X.hom := by
      change IsAffineHom (pullback.snd G.X.hom bc)
      infer_instance
    let dSplit := GaloisPinningData.ofTorusIso hQ.1 p.torus p.inclusion p.isMaximalTorus
      (p.baseChange (F := K)) (Iso.refl _) (Iso.refl _) (by
        change (GroupScheme.baseChange bc).map p.inclusion ≫ 𝟙 _ =
          𝟙 _ ≫ (GroupScheme.baseChange bc).map p.inclusion
        simp only [Category.comp_id, Category.id_comp])
    apply trivial_star_transport dSplit d
    intro σ
    apply (dSplit.starAction_eq_one_iff σ).mpr
    have hg : dSplit.galoisAction σ = 1 := by
      apply StarActionIndependence.equiv_ext_of_weightMap
      intro χ
      rw [StarActionIndependence.galoisAction_weightMap_apply]
      exact TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus
        p.torus p.isSplitTorus σ χ
    rw [hg]
    exact Subgroup.one_mem _
  · intro h
    obtain ⟨dBorel, hordinary⟩ := starActionQuasiSplit k G hQ
    have hsplit := split_of_fixes_characters dBorel.torus dBorel.isSplitTorus fun σ χ => by
      rw [← StarActionIndependence.galoisAction_weightMap_apply dBorel σ χ, ← hordinary σ,
        trivial_star_transport d dBorel h σ]
      rfl
    obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k K
    have hpb := (IsPullback.of_hasPullback G.X.hom bc).flip
    have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (pullback.fst G.X.hom bc) :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hpb hs,
        MorphismProperty.of_isPullback (P := @Flat) hpb hf⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) hpb hq⟩
    have hclosed : IsClosedSubgroup dBorel.inclusion :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
        (baseChange_map_isPullback bc dBorel.inclusion) hp dBorel.isMaximalTorus.2.1
    exact ⟨dBorel.torus, dBorel.inclusion, hsplit,
      IsMaximalTorus.of_baseChange hclosed dBorel.isMaximalTorus⟩

end Langlands.GroupScheme
