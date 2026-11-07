import Langlands.Representation.Jacquet.CoefficientImageFiltration
import Langlands.Representation.Jacquet.RestrictedLocalizationFiltration
import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Filtration.GroupRestriction
import Langlands.Representation.Filtration.IsoTransport
import Langlands.Representation.Filtration.TwistGraded
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Aubert.General.Parabolic

/-! Native subgroup-localization and actual ambient support-image comparisons. -/

noncomputable section
open CategoryTheory

namespace Langlands.Jacquet.Localization.Coefficient

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
  (Q : Subgroup G) (hUQ : U ≤ Q) (hMQ : M ≤ Q)

include hMU hUQ in
/-- The ambient normalizer condition restricts to the literal subgroup copies. -/
theorem nested_normalizes :
    M.subgroupOf Q ≤ Subgroup.normalizer (U.subgroupOf Q) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUQ]
  exact Subgroup.subgroupOf_mono Q hMU

/-- The output Levi is identified with its literal nested subgroup copy. -/
def toNestedNormalizer : M →* M.subgroupOf Q :=
  (Subgroup.subgroupOfEquivOfLe hMQ).symm.toMonoidHom

/-- Native quotient of a representation of `Q`, with output on the original
subgroup `M`, not its nested subtype copy. -/
def subgroupFunctor : Rep.{uV} R Q ⥤ Rep.{uV} R M :=
  functor (U.subgroupOf Q) 1 (M.subgroupOf Q) (nested_normalizes U M hMU Q hUQ)
      (isInvariant_one _ _ _) ⋙
    Rep.resFunctor (toNestedNormalizer M Q hMQ)

/-- The original and subgroup quotients have the same classes naturally.
The comparison sends every actual representative to itself. -/
def subgroupRestrictionIso :
    Rep.resFunctor Q.subtype ⋙ subgroupFunctor (R := R) U M hMU Q hUQ hMQ ≅
      functor (R := R) U 1 M hMU (isInvariant_one U M hMU) := by
  let e := fun A : Rep.{uV} R G =>
    transportEquiv (A.ρ.comp Q.subtype) A.ρ (U.subgroupOf Q) U 1 1
      (Subgroup.subgroupOfEquivOfLe hUQ) (LinearEquiv.refl R A)
      (fun _ _ => rfl) (fun _ => rfl)
  refine NatIso.ofComponents (fun A => Rep.mkIso
    { toLinearEquiv := e A
      isIntertwining' m := by
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := mk_surjective (A.ρ.comp Q.subtype) (U.subgroupOf Q) 1 q
        rfl }) ?_
  intro A B f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := mk_surjective (A.ρ.comp Q.subtype) (U.subgroupOf Q) 1 q
  rfl

@[simp]
theorem subgroupRestrictionIso_hom_mk (A : Rep.{uV} R G) (v : A) :
    ((subgroupRestrictionIso U M hMU Q hUQ hMQ).hom.app A).hom
        (mk (A.ρ.comp Q.subtype) (U.subgroupOf Q) 1 v) =
      mk A.ρ U 1 v := rfl

@[simp]
theorem subgroupRestrictionIso_inv_mk (A : Rep.{uV} R G) (v : A) :
    ((subgroupRestrictionIso U M hMU Q hUQ hMQ).inv.app A).hom
        (mk A.ρ U 1 v) =
      mk (A.ρ.comp Q.subtype) (U.subgroupOf Q) 1 v := rfl

include hUQ in
/-- When the whole subgroup lies in `Q`, compact containment transports along
the canonical subgroup homeomorphism; no closedness of `Q` is required. -/
theorem nested_isLimitOfCompactSubgroups [TopologicalSpace G]
    (hU : IsLimitOfCompactSubgroups U) :
    IsLimitOfCompactSubgroups (U.subgroupOf Q) := by
  let e := Aubert.General.subgroupOfContinuousEquiv hUQ
  intro C hC
  obtain ⟨K, hK, hCK⟩ := hU (e '' C) (hC.image e.continuous)
  refine ⟨K.comap e.toMonoidHom, ?_, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.mpr hK
  · intro x hx
    exact hCK ⟨x, hx, rfl⟩

variable {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

private theorem subfunctor_eq {H : C ⥤ Rep.{uV} R M}
    {S T : RepSubfunctor H} (h : ∀ X, S.obj X = T.obj X) : S = T := by
  cases S with
  | mk S hS =>
    cases T with
    | mk T hT =>
      have heq : S = T := funext h
      subst T
      rfl

/-- Transporting the restricted quotient's actual image recovers exactly
the prescribed ambient image of the same support subfunctor. -/
theorem subgroup_image_transport
    (S : RepSubfunctor (F ⋙ Rep.resFunctor Q.subtype)) :
    ((imageSubfunctor (U.subgroupOf Q) 1 (M.subgroupOf Q)
        (nested_normalizes U M hMU Q hUQ) (isInvariant_one _ _ _) S).restrictGroup
        (toNestedNormalizer M Q hMQ)).isoTransport
          (Functor.isoWhiskerLeft F (subgroupRestrictionIso U M hMU Q hUQ hMQ)) =
      restrictedImageSubfunctor U 1 M hMU (isInvariant_one U M hMU) Q hMQ S := by
  apply subfunctor_eq
  intro X
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro q
  obtain ⟨v, rfl⟩ := mk_surjective (F.obj X).ρ U 1 q
  change (∃ w ∈ S.obj X,
    mk ((F.obj X).ρ.comp Q.subtype) (U.subgroupOf Q) 1 w =
      mk ((F.obj X).ρ.comp Q.subtype) (U.subgroupOf Q) 1 v) ↔
    ∃ w ∈ S.obj X, mk (F.obj X).ρ U 1 w = mk (F.obj X).ρ U 1 v
  constructor
  · rintro ⟨w, hw, heq⟩
    exact ⟨w, hw, congrArg
      ((subgroupRestrictionIso U M hMU Q hUQ hMQ).hom.app (F.obj X)).hom heq⟩
  · rintro ⟨w, hw, heq⟩
    exact ⟨w, hw, congrArg
      ((subgroupRestrictionIso U M hMU Q hUQ hMQ).inv.app (F.obj X)).hom heq⟩

private theorem filtration_eq {H : C ⥤ Rep.{uV} R M} {n : ℕ}
    {s t : RepFunctorFiltration H n} (h : ∀ i, s.step i = t.step i) : s = t := by
  cases s with
  | mk s hs hsz hst =>
    cases t with
    | mk t ht htz htt =>
      have heq : s = t := funext h
      subst t
      rfl

/-- Restricting and transporting the nested image filtration yields the exact
prescribed ambient image filtration, with all indices unchanged. -/
theorem subgroup_imageFiltration_transport {n : ℕ}
    (s : RepFunctorFiltration (F ⋙ Rep.resFunctor Q.subtype) n) :
    ((imageFiltration (U.subgroupOf Q) 1 (M.subgroupOf Q)
        (nested_normalizes U M hMU Q hUQ) (isInvariant_one _ _ _) s).restrictGroup
        (toNestedNormalizer M Q hMQ)).isoTransport
          (Functor.isoWhiskerLeft F (subgroupRestrictionIso U M hMU Q hUQ hMQ)) =
      restrictedImageFiltration U 1 M hMU (isInvariant_one U M hMU) Q hMQ s := by
  apply filtration_eq
  intro i
  exact subgroup_image_transport U M hMU Q hUQ hMQ (s.step i)

variable [Algebra ℂ R] [TopologicalSpace G] [IsTopologicalGroup G]
  (hU : IsLimitOfCompactSubgroups U) (hF : ∀ X, IsSmooth (F.obj X).ρ)

set_option maxHeartbeats 800000 in
/-- Each grade of the actual ambient image filtration is the native quotient
of the original restricted grade, naturally as a representation of the literal
ambient output subgroup `M`. -/
def restrictedImageFiltrationGradedIso {n : ℕ}
    (s : RepFunctorFiltration (F ⋙ Rep.resFunctor Q.subtype) n) (i : Fin n) :
    (restrictedImageFiltration U 1 M hMU (isInvariant_one U M hMU) Q hMQ s).graded i ≅
      s.graded i ⋙ subgroupFunctor U M hMU Q hUQ hMQ := by
  let t := imageFiltration (U.subgroupOf Q) 1 (M.subgroupOf Q)
    (nested_normalizes U M hMU Q hUQ) (isInvariant_one _ _ _) s
  let φ := toNestedNormalizer M Q hMQ
  let e := Functor.isoWhiskerLeft F (subgroupRestrictionIso U M hMU Q hUQ hMQ)
  have ht : (t.restrictGroup φ).isoTransport e =
      restrictedImageFiltration U 1 M hMU (isInvariant_one U M hMU) Q hMQ s :=
    subgroup_imageFiltration_transport U M hMU Q hUQ hMQ s
  exact (eqToIso (congrArg (fun a => a.graded i) ht)).symm ≪≫
    ((t.restrictGroup φ).isoTransportGradedIso e i).symm ≪≫
    t.restrictGroupGradedIso φ i ≪≫
    Functor.isoWhiskerRight
      (imageFiltrationGradedIso (U.subgroupOf Q) (M.subgroupOf Q)
        (nested_normalizes U M hMU Q hUQ)
        (nested_isLimitOfCompactSubgroups U Q hUQ hU)
        (fun X => isSmooth_comp Q.subtype continuous_subtype_val (hF X)) s i)
      (Rep.resFunctor φ)

/-- Scalar normalization retains the same actual support images and commutes
naturally with their graded comparison. -/
def twistedRestrictedImageFiltrationGradedIso {n : ℕ}
    (s : RepFunctorFiltration (F ⋙ Rep.resFunctor Q.subtype) n)
    (χ : Induction.SmoothCharacter R M) (i : Fin n) :
    ((restrictedImageFiltration U 1 M hMU (isInvariant_one U M hMU) Q hMQ s).twist χ).graded i ≅
      s.graded i ⋙ subgroupFunctor U M hMU Q hUQ hMQ ⋙ χ.twistFunctor :=
  (restrictedImageFiltration U 1 M hMU (isInvariant_one U M hMU) Q hMQ s).twistGradedIso χ i ≪≫
    Functor.isoWhiskerRight
      (restrictedImageFiltrationGradedIso U M hMU Q hUQ hMQ hU hF s i) χ.twistFunctor

end Langlands.Jacquet.Localization.Coefficient
