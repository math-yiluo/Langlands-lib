import Langlands.GroupScheme.Dilatation.StructureStatement
import Langlands.GroupScheme.Dilatation.CongruenceAddition
import Langlands.AlgebraicGeometry.DvrSmoothFibers

/-! # Reduction of the structural assertions to the special fibre -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry (closedPointResidueSpecIso
  closedPointResidueSpecIso_hom_fromSpecResidueField fractionFieldGenericPointIso
  fractionFieldGenericPointIso_hom_fromSpecResidueField smooth_of_generic_special_fibers)

universe u

private theorem property_of_overIso {S : Scheme.{u}} {X Y : Over S}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (e : X ≅ Y) (h : P X.hom) : P Y.hom := by
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  rw [← e.inv.w]
  exact MorphismProperty.RespectsIso.precomp P e.inv.left X.hom h

private theorem property_of_groupIso {S : Scheme.{u}} {X Y : GroupScheme S}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (e : X ≅ Y) (h : P X.X.hom) : P Y.X.hom :=
  property_of_overIso P ((Grp.forget (Over S)).mapIso e) h

private theorem geoconn_of_quotient_fiber {S T X : Scheme.{u}} (f : X ⟶ S) (x : S) (b : T ⟶ S)
    (e : T ≅ Spec (S.residueField x)) (he : e.hom ≫ S.fromSpecResidueField x = b)
    (h : GeometricallyConnected (pullback.snd f b)) :
    GeometricallyConnected (f.fiberToSpecResidueField x) := by
  let : GeometricallyConnected (pullback.snd f b) := h
  have hb : S.fromSpecResidueField x = e.inv ≫ b := by
    rw [← he, Iso.inv_hom_id_assoc]
  change GeometricallyConnected (pullback.snd f (S.fromSpecResidueField x))
  rw [hb, ← pullbackLeftPullbackSndIso_inv_snd_snd f b e.inv]
  exact MorphismProperty.RespectsIso.precomp @GeometricallyConnected _ _ inferInstance

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The two actual fibres determine geometric connectedness over a DVR. -/
theorem hasGeometricallyConnectedFibres_of_generic_special (M : IntegralModel R K G)
    (hg : GeometricallyConnected G.X.hom) (hs : M.HasGeometricallyConnectedSpecialFibre) :
    M.HasGeometricallyConnectedFibres := by
  rw [M.hasGeometricallyConnectedFibres_iff]
  intro x
  rcases Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness.point_eq_generic_or_closed R x
    with hx | hx
  · have hx' : x = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      exact hx
    rw [hx']
    exact geoconn_of_quotient_fiber M.group.X.hom _ (Spec.algebraMap R K)
      (fractionFieldGenericPointIso (CommRingCat.of R) K)
      (fractionFieldGenericPointIso_hom_fromSpecResidueField (CommRingCat.of R) K)
      (property_of_groupIso @GeometricallyConnected M.genericIso.symm hg)
  · subst x
    exact geoconn_of_quotient_fiber M.group.X.hom _ (residueBaseMap R)
      (closedPointResidueSpecIso R) (closedPointResidueSpecIso_hom_fromSpecResidueField R) hs

/-- A smooth morphism from the dilatation special fibre to the smooth centre, with
geometrically connected fibres, implies the structural conclusions for this dilatation. -/
theorem dilatation_structure_of_specialFibre (M : IntegralModel R K G) {ϖ : R}
    (hϖ : Irreducible ϖ)
    {Y : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (j : Y ⟶ M.specialFibre) [IsClosedImmersion j.hom.hom.left]
    (f : (M.dilatation hϖ j).specialFibre.X ⟶ Y.X)
    (hM : M.IsSmooth) (hY : Smooth Y.X.hom)
    (hf : Smooth f.left) (hc : GeometricallyConnected f.left) :
    (M.dilatation hϖ j).IsSmooth ∧
    (GeometricallyConnected Y.X.hom → (M.dilatation hϖ j).HasGeometricallyConnectedSpecialFibre) ∧
    (GeometricallyConnected G.X.hom → GeometricallyConnected Y.X.hom →
      (M.dilatation hϖ j).HasGeometricallyConnectedFibres) := by
  let D := M.dilatation hϖ j
  let : Smooth M.group.X.hom := hM
  let : Smooth Y.X.hom := hY
  let : Smooth f.left := hf
  have hs : Smooth D.specialFibre.X.hom := by rw [← f.w]; infer_instance
  have hg : Smooth D.genericFibre.X.hom := by
    have hgM : Smooth M.genericFibre.X.hom := by
      change Smooth (pullback.snd M.group.X.hom (Spec.algebraMap R K))
      infer_instance
    exact property_of_groupIso @Smooth (M.genericIso ≪≫ D.genericIso.symm) hgM
  have hconn (h : GeometricallyConnected Y.X.hom) : D.HasGeometricallyConnectedSpecialFibre := by
    let : GeometricallyConnected f.left := hc
    let : GeometricallyConnected Y.X.hom := h
    change GeometricallyConnected D.specialFibre.X.hom
    rw [← f.w]
    exact GeometricallyConnected.comp _ _
  let : Smooth (pullback.snd D.group.X.hom (Spec.algebraMap R K)) := hg
  let : Smooth (pullback.snd D.group.X.hom (Spec.algebraMap R (IsLocalRing.ResidueField R))) := hs
  exact ⟨smooth_of_generic_special_fibers R K D.group.X.hom, hconn,
    fun hG hy => D.hasGeometricallyConnectedFibres_of_generic_special hG (hconn hy)⟩

/-- The structural result for ordinary dilatations implies the corresponding
positive congruence result via successive dilatations at the unit. -/
theorem smoothCongruenceModels_of_smoothDilatation
    (hd : SmoothDilatationStatement.{u}) : SmoothCongruenceModelsStatement.{u} := by
  intro R K _ _ _ _ _ _ G M ϖ hϖ hM n
  have hfirst (P : IntegralModel R K G) (hP : P.IsSmooth) :
      (P.positiveCongruenceModel hϖ 1).IsSmooth ∧
        (P.positiveCongruenceModel hϖ 1).HasGeometricallyConnectedSpecialFibre := by
    let Y := Grp.trivial (Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    let j := kernelUnit P.specialFibre
    let : IsAffineHom P.specialFibre.X.hom := inferInstanceAs
      (IsAffineHom (pullback.snd P.group.X.hom (residueBaseMap R)))
    let : IsSeparated P.specialFibre.X.hom := IsSeparated.of_isAffineHom _
    let : IsClosedImmersion j.hom.hom.left := kernelUnit_isClosedSubgroup _
    have hy : Smooth Y.X.hom := inferInstanceAs (Smooth (𝟙 _))
    have hyc : GeometricallyConnected Y.X.hom := by
      change GeometricallyConnected (𝟙 _)
      refine ⟨?_⟩
      intro L _ y Z fst snd h
      have : IsIso snd := h.isIso_snd_of_isIso
      exact snd.homeomorph.connectedSpace_iff.mpr inferInstance
    have ht := hd R K G P ϖ hϖ Y j hP hy
    change (P.positiveCongruenceModel hϖ 1).IsSmooth ∧ _
    rw [P.positiveCongruenceModel_one hϖ]
    exact ⟨ht.1, ht.2.1 hyc⟩
  have hpos (a : ℕ) :
      (M.positiveCongruenceModel hϖ ⟨a + 1, Nat.succ_pos a⟩).IsSmooth ∧
        (M.positiveCongruenceModel hϖ ⟨a + 1, Nat.succ_pos a⟩).HasGeometricallyConnectedSpecialFibre := by
    induction a with
    | zero => exact hfirst M hM
    | succ a ih =>
      let m : ℕ+ := ⟨a + 1, Nat.succ_pos a⟩
      let P := M.positiveCongruenceModel hϖ m
      let e := M.positiveCongruenceModelAddIso hϖ m 1
      obtain ⟨hs, hc⟩ := hfirst P ih.1
      exact ⟨property_of_groupIso @Smooth e.iso hs,
        property_of_groupIso @GeometricallyConnected ((baseChange (residueBaseMap R)).mapIso e.iso) hc⟩
  rw [M.congruenceModel_coe_pnat]
  have he : (M.positiveCongruenceModel hϖ n).IsSmooth ∧
      (M.positiveCongruenceModel hϖ n).HasGeometricallyConnectedSpecialFibre := by
    rcases n with ⟨_ | a, ha⟩
    · exact (Nat.lt_irrefl 0 ha).elim
    · exact hpos a
  exact ⟨he.1, he.2, fun hg =>
    (M.positiveCongruenceModel hϖ n).hasGeometricallyConnectedFibres_of_generic_special hg he.2⟩

end Langlands.GroupScheme.IntegralModel
