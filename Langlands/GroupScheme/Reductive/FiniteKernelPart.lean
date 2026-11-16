import Langlands.GroupScheme.FiniteClosedFibrePartGroup
import Langlands.GroupScheme.ClopenNormalSubgroup
import Langlands.GroupScheme.Reductive.KernelQuotientFactorization
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.PullbackCarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! # Removing a supplied finite closed-fibre kernel part -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteClosedFibrePart

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {K : GroupScheme (Spec (CommRingCat.of R))} {U : K.X.left.Opens}
  (hU : Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart K.X.hom U)

/-- The supplied finite part is the whole group after a base change supported
at the closed point. -/
theorem isIso_baseChange_inclusion {T : Scheme.{u}}
    (b : T ⟶ Spec (CommRingCat.of R))
    (hb : ∀ t, b t = IsLocalRing.closedPoint R) :
    IsIso ((baseChange b).map (inclusion hU)) := by
  let j := (baseChange b).map (inclusion hU)
  have hj : IsOpenImmersion j.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b
      (inclusion hU).hom.hom inferInstance
  have hs : Surjective j.hom.hom.left := by
    let m := pullback.map (group hU).X.hom b K.X.hom b
        (inclusion hU).hom.hom.left (𝟙 T) (𝟙 _)
        (by simpa only [Category.comp_id] using (Over.w (inclusion hU).hom.hom).symm)
        (by simp)
    have he : j.hom.hom.left = m := by
      apply pullback.hom_ext <;> simp [j, m, Over.pullback_map_left]
    have hm : Surjective m := by
      change Surjective (pullback.map _ _ _ _ _ _ _ _ _)
      rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_map]
      apply Set.eq_univ_of_forall
      intro z
      refine ⟨?_, ⟨pullback.snd K.X.hom b z, rfl⟩⟩
      change pullback.fst K.X.hom b z ∈ Set.range (inclusion hU).hom.hom.left
      apply contains_closedFibre hU
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact hb _
    exact he.symm ▸ hm
  have : IsIso j.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hj, hs⟩
  have : IsIso ((Over.forget _).map j.hom.hom) := ‹IsIso j.hom.hom.left›
  have : IsIso j.hom.hom := isIso_of_reflects_iso j.hom.hom (Over.forget _)
  have : IsIso ((Mon.forget _).map j.hom) := ‹IsIso j.hom.hom›
  have : IsIso j.hom := isIso_of_reflects_iso j.hom (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map j) := ‹IsIso j.hom›
  exact isIso_of_reflects_iso j (Grp.forget₂Mon _)

/-- The supplied finite part is the whole group on the closed fibre. -/
theorem isIso_closedFibre_inclusion :
    IsIso ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R))).map (inclusion hU)) :=
  isIso_baseChange_inclusion hU _ (fun _ => Scheme.fromSpecResidueField_apply _ _)

end FiniteClosedFibrePart

namespace FiniteKernelPart

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
  {U : (kernel f).X.left.Opens}
  (hU : Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart (kernel f).X.hom U)

/-- The actual finite subgroup constructed on the supplied part of the kernel. -/
abbrev group : GroupScheme (Spec (CommRingCat.of R)) := FiniteClosedFibrePart.group hU

/-- Its actual homomorphism to the original source. -/
def inclusion : group f hU ⟶ G := FiniteClosedFibrePart.inclusion hU ≫ kernelι f

instance : Mono (inclusion f hU).hom.hom :=
  inferInstanceAs (Mono ((FiniteClosedFibrePart.inclusion hU).hom.hom ≫ (kernelι f).hom.hom))

/-- The supplied part is contained in the full scheme-theoretic kernel. -/
theorem inclusion_comp : inclusion f hU ≫ f = 0 := by
  apply Grp.hom_ext
  change ((FiniteClosedFibrePart.inclusion hU).hom.hom ≫ (kernelι f).hom.hom) ≫
    f.hom.hom = 1
  rw [Category.assoc, (mem_range_kernelι_iff f _).mp
    (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩), MonObj.comp_one]

/-- Geometric connectedness makes the clopen part of the full kernel normal. -/
theorem normal [GeometricallyConnected G.X.hom] :
    (SubgroupFunctor.range (inclusion f hU)).IsNormal := by
  apply ClopenNormalSubgroup.isNormal_range_comp (kernelι f)
    (FiniteClosedFibrePart.inclusion hU)
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

/-- On the actual closed fibre, the inclusion has the full kernel range. -/
theorem closedFibre_range :
    SubgroupFunctor.range ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R))).map (inclusion f hU)) =
    SubgroupFunctor.range (kernelι ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R))).map f)) := by
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)
  have : IsIso ((baseChange b).map (FiniteClosedFibrePart.inclusion hU)) :=
    FiniteClosedFibrePart.isIso_closedFibre_inclusion hU
  exact (show SubgroupFunctor.range ((baseChange b).map (inclusion f hU)) =
      SubgroupFunctor.range ((baseChange b).map (kernelι f)) from by
    change SubgroupFunctor.range ((baseChange b).map
      (FiniteClosedFibrePart.inclusion hU ≫ kernelι f)) = _
    rw [Functor.map_comp]
    exact SubgroupFunctor.range_iso_comp
      (asIso ((baseChange b).map (FiniteClosedFibrePart.inclusion hU))) _).trans
    (by rw [SubgroupFunctor.range_baseChangeHom, kernel_range_baseChange])

/-- From a supplied finite closed-fibre part, construct the reductive quotient
and the specified remaining fibrewise isogeny, invertible on the closed fibre. -/
def reductiveQuotient (hG : IsReductive G) (hH : IsReductive H)
    (hf : IsFibrewiseIsogeny f) :
    ReductiveKernelQuotientFactorization f (inclusion f hU)
      ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth H.X.hom := hH.smooth
  have : Flat f.hom.hom.left := flat_of_isogeny_fibres f hf
  have : LocallyOfFinitePresentation (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation f.hom.hom.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp
      f.hom.hom.left H.X.hom
  have : Flat (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have : LocallyOfFinitePresentation (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have : GeometricallyConnected G.X.hom := hG.geometricallyConnected
  exact reductiveKernelQuotientFactorization hG hH f hf (inclusion f hU)
    (normal f hU) (inclusion_comp f hU) _ (closedFibre_range f hU)

end FiniteKernelPart

end Langlands.GroupScheme
