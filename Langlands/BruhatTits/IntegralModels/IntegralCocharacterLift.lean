import Langlands.BruhatTits.IntegralModels.FacetLieWeights

/-! # Integral cocharacters and canonical specialization pairings -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)

include hT in
/-- Lift an actual generic cocharacter through the specified integral split
 torus, preserving both the ambient generic map and canonical special pairing. -/
theorem exists_integralCocharacter_compatible (ν : cocharacterLattice S) :
    ∃ νR : cocharacterLattice T.torus,
      Dynamic.baseChangeCocharacter (Spec.algebraMap R K)
          (CommGroupScheme.groupHom νR ≫ T.inclusion) ≫ D.neutral.genericIso.hom =
        CommGroupScheme.groupHom ν ≫ i ∧
      ∀ a : characterLattice S,
        latticePairing T.specialFibre (T.characterSpecialization hT a)
            (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus νR) =
          latticePairing S a ν := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  obtain ⟨νR, hνR⟩ := (hT.cocharacterLattice_baseChange_bijective
    (Spec.algebraMap R K) T.torus).surjective (ν ≫ e.inv)
  have hνRν : cocharacterLattice.baseChange (Spec.algebraMap R K) T.torus νR ≫ e.hom = ν := by
    rw [hνR]
    simp
  refine ⟨νR, ?_, ?_⟩
  · change (Gm.baseChangeIso (Spec.algebraMap R K)).inv ≫
        (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (CommGroupScheme.groupHom νR ≫ T.inclusion) ≫ D.neutral.genericIso.hom = _
    rw [Functor.map_comp, Category.assoc, T.generic_comm]
    change CommGroupScheme.groupHom
        (cocharacterLattice.baseChange (Spec.algebraMap R K) T.torus νR ≫ e.hom) ≫ i = _
    rw [hνRν]
  · intro a
    let α := (T.genericCharacterEquiv hT).symm a
    have hα : T.genericCharacter α = a := (T.genericCharacterEquiv hT).apply_symm_apply a
    let c : characterLattice S ≃+ characterLattice
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus) :=
      characterLattice.comapIso T.genericIso
    have hαK : characterLattice.baseChange (Spec.algebraMap R K) T.torus α =
        c a := by
      have h := congrArg c hα
      change c
        (c.symm _) = _ at h
      simpa only [AddEquiv.apply_symm_apply] using h
    have hs : T.characterSpecialization hT a = T.specialCharacter α := by
      rw [← hα, T.characterSpecialization_genericCharacter hT α]
    rw [hs]
    change latticePairing ((CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).obj T.torus)
      (characterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus α)
      (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus νR) = _
    rw [latticePairing_baseChange]
    rw [← latticePairing_baseChange (Spec.algebraMap R K) T.torus α νR, hαK]
    change gmEndEquiv K
      (cocharacterLattice.baseChange (Spec.algebraMap R K) T.torus νR ≫ (e.hom ≫ a)) = _
    rw [← Category.assoc, hνRν]
    rfl

/-- An actual compatible integral cocharacter, retaining its generic ambient
map and all the canonical special-fibre pairings. -/
def compatibleIntegralCocharacter (ν : cocharacterLattice S) :
    {νR : cocharacterLattice T.torus //
      Dynamic.baseChangeCocharacter (Spec.algebraMap R K)
          (CommGroupScheme.groupHom νR ≫ T.inclusion) ≫ D.neutral.genericIso.hom =
        CommGroupScheme.groupHom ν ≫ i ∧
      ∀ a : characterLattice S,
        latticePairing T.specialFibre (T.characterSpecialization hT a)
            (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus νR) =
          latticePairing S a ν} :=
  Classical.indefiniteDescription _ (T.exists_integralCocharacter_compatible hT ν)

end IntegralTorusData

end Langlands.BruhatTits.IntegralModels
