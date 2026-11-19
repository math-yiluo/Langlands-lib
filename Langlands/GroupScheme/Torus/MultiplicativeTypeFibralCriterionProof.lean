import Langlands.AlgebraicGeometry.StrictLocalEtaleLimitProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibralCriterionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeLocalDetection
import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianCriterion
import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianLiftProof

/-! # Proof of the fibral criterion for groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

private theorem of_strictLocalBaseChanges
    (hExist : Langlands.AlgebraicGeometry.StrictLocalEtaleLimitExistenceStatement.{u})
    {S : Scheme.{u}} (H : GroupScheme S)
    [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hH : ∀ (A : Type u) [CommRing A] [HenselianLocalRing A]
      [IsSepClosed (IsLocalRing.ResidueField A)] (b : Spec (CommRingCat.of A) ⟶ S),
      RelativeMultiplicativeType.IsMultiplicativeType ((baseChange b).obj H)) :
    RelativeMultiplicativeType.IsMultiplicativeType H := by
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_openCover S.affineCover
  intro i
  let f := S.affineCover.f i
  have : IsAffineHom ((baseChange f).obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom f inferInstance
  have : LocallyOfFinitePresentation ((baseChange f).obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom f inferInstance
  change RelativeMultiplicativeType.IsMultiplicativeType ((baseChange f).obj H)
  apply LocalMultiplicativeType.of_pointwise_localBaseChange
  intro s
  obtain ⟨L⟩ := hExist (S.affineCover.X i) s
  exact ⟨L.toLocal, RelativeMultiplicativeType.IsMultiplicativeType.of_iso
    (baseChangeCompIso f L.baseMap H).symm (hH L.ring (L.baseMap ≫ f))⟩

/-- The connected-fibre and commutative torsion-order criteria for
multiplicative type over an arbitrary base scheme. -/
theorem multiplicativeTypeFibralCriterion : MultiplicativeTypeFibralCriterionStatement.{u} := by
  have hExist := Langlands.AlgebraicGeometry.strictLocalEtaleLimitExistence.{u}
  have hLift := multiplicativeTypeStrictHenselianLift.{u}
  intro S H hFlat hFp hAff
  constructor
  · intro hConnected
    refine ⟨fun h s => h.geometricFiber s, ?_⟩
    intro hGeometric
    apply of_strictLocalBaseChanges hExist H
    intro A _ _ _ b
    let G := (baseChange b).obj H
    have : Flat G.X.hom := MorphismProperty.pullback_snd H.X.hom b hFlat
    have : LocallyOfFinitePresentation G.X.hom :=
      MorphismProperty.pullback_snd H.X.hom b hFp
    have : IsAffineHom G.X.hom := MorphismProperty.pullback_snd H.X.hom b hAff
    have hConnectedG (t : Spec (CommRingCat.of A)) :
        ConnectedSpace (RelativeIdentityComponent.residueFiber G t).X.left :=
      (ExtensionReduction.connectedSpace_residueFiber_baseChange_iff b H t).mpr
        (hConnected (b t))
    exact (StrictHenselianFibral.connectedCriterion hLift A G hConnectedG).mpr
      (fun t => (FpqcMultiplicativeType.geometricFiber_isMultiplicativeType_iff b H t).mpr
        (hGeometric (b t)))
  · intro hComm
    refine ⟨fun h => ⟨fun s => h.geometricFiber s,
      fun n hn => h.isLocallyConstant_torsionFinrank n hn⟩, ?_⟩
    rintro ⟨hGeometric, hOrder⟩
    apply of_strictLocalBaseChanges hExist H
    intro A _ _ _ b
    let G := (baseChange b).obj H
    have : Flat G.X.hom := MorphismProperty.pullback_snd H.X.hom b hFlat
    have : LocallyOfFinitePresentation G.X.hom :=
      MorphismProperty.pullback_snd H.X.hom b hFp
    have : IsAffineHom G.X.hom := MorphismProperty.pullback_snd H.X.hom b hAff
    have : IsCommMonObj G.X := inferInstanceAs (IsCommMonObj ((baseChange b).obj H).X)
    apply (StrictHenselianFibral.commutativeCriterion hLift A G).mpr
    refine ⟨fun t => (FpqcMultiplicativeType.geometricFiber_isMultiplicativeType_iff b H t).mpr
      (hGeometric (b t)), ?_⟩
    intro n hn
    change IsLocallyConstant (FpqcMultiplicativeType.geometricTorsionOrder G (n : ℤ))
    have hOrderChange : FpqcMultiplicativeType.geometricTorsionOrder G (n : ℤ) =
        FpqcMultiplicativeType.geometricTorsionOrder H (n : ℤ) ∘ b :=
      funext (FpqcMultiplicativeType.geometricTorsionOrder_baseChange b H (n : ℤ))
    rw [hOrderChange]
    exact (hOrder n hn).comp_continuous b.continuous

end Langlands.GroupScheme
