import Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
import Langlands.Group.GL.MirabolicMixedOrbitStages
import Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
import Langlands.Representation.Induction.SplitStagesRetraction
import Langlands.Representation.Induction.SplitKernelLocalizationData
import Langlands.Representation.Induction.SplitQuotientStatement
import Langlands.Representation.Mirabolic.MixedProducts

/-! Actual nested left-orbit character quotients and their section actions. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction
  Induction.SplitKernelLocalization Jacquet.Localization MixedProductTensor

universe uR uV uW

variable {R : Type uR} [CommRing R]

/-- The kernel of the actual plus projection is the actual mirabolic radical. -/
def plusKernelRadicalEquiv (n : ℕ) :
    (plusProjection (n := n) (F := R)).ker ≃* radical (n + 1) R where
  toFun u := ⟨u.val.val, (projection_eq_one_iff u.val.val).mp
    (congrArg Subtype.val u.property)⟩
  invFun u := ⟨plusRadical u, plusProjection_plusRadical u⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp] theorem plusKernelRadicalEquiv_val (n : ℕ)
    (u : (plusProjection (n := n) (F := R)).ker) :
    (plusKernelRadicalEquiv n u).val = u.val.val := rfl

variable (k r : ℕ)

/-- The actual stages group contains the whole kernel, for either left orbit. -/
theorem leftStages_contains_kernel (i : Fin 2) :
    (plusProjection (n := k + r + 1) (F := R)).ker ≤ leftStages k r R i := by
  intro u hu
  change plusProjection u ∈ leftSection k r R i
  rw [show plusProjection u = 1 from hu]
  exact (leftSection k r R i).one_mem

/-- The restricted retraction on the actual left stages group. -/
abbrev leftPhiStagesRetraction (i : Fin 2) :=
  splitStagesRetraction (plusProjection (n := k + r + 1) (F := R))
    plusSuccessor plusProjection_plusSuccessor (leftStages k r R i)
    (leftStages_contains_kernel k r i)

/-- Its actual successor section; the domain is the section preimage in the stages group. -/
abbrev leftPhiStagesSection (i : Fin 2) :=
  plusSuccessor.subgroupComap (leftStages k r R i)

/-- Pulling the actual stages subgroup back along the section recovers the lower section. -/
theorem leftPhiStages_comap_section (i : Fin 2) :
    (leftStages k r R i).comap plusSuccessor = leftSection k r R i := by
  change ((leftSection k r R i).comap plusProjection).comap plusSuccessor = _
  rw [Subgroup.comap_comap, plusProjection_comp_plusSuccessor, Subgroup.comap_id]

/-- The section preimage of the stages group is exactly the lower left section. -/
def leftPhiStagesSectionEquiv (i : Fin 2) :
    (leftStages k r R i).comap plusSuccessor ≃* leftSection k r R i :=
  MulEquiv.subgroupCongr (leftPhiStages_comap_section k r i)

@[simp] theorem leftPhiStagesSectionEquiv_val (i : Fin 2)
    (l : (leftStages k r R i).comap plusSuccessor) :
    (leftPhiStagesSectionEquiv k r i l).val = l.val :=
  MulEquiv.subgroupCongr_apply (leftPhiStages_comap_section k r i) l

/-- The inducing stabilizer with its membership in the stages group retained. -/
abbrev leftPhiStagesStabilizer (i : Fin 2) :=
  (leftStabilizer k r R i).subgroupOf (leftStages k r R i)

/-- Remove just the intermediate stages membership from the actual stabilizer. -/
abbrev leftPhiStagesInducingEquiv (i : Fin 2) :=
  Subgroup.subgroupOfEquivOfLe (leftStabilizer_le_stages k r R i)

/-- The section over the stages quotient takes values in the actual stabilizer. -/
theorem leftPhiStagesSection_mem (i : Fin 2)
    (l : (leftStages k r R i).comap plusSuccessor) :
    leftPhiStagesSection k r i l ∈ leftPhiStagesStabilizer k r i := by
  change plusSuccessor l.val ∈ leftStabilizer k r R i
  rw [← leftPhiStagesSectionEquiv_val k r i l]
  exact (leftPhiStagesSectionEquiv k r i l).property

/-- Removing stages membership carries the nested section to the actual orbit section. -/
theorem leftPhiStagesInducingEquiv_section (i : Fin 2)
    (l : (leftStages k r R i).comap plusSuccessor) :
    leftPhiStagesInducingEquiv k r i
        (subgroupSection (leftPhiStagesSection k r i)
          (leftPhiStagesStabilizer k r i) (leftPhiStagesSection_mem k r i) l) =
      sectionInclusion (leftInducing k r R) (leftRepresentative k r R i)
        (leftPhiStagesSectionEquiv k r i l) := by
  apply Subtype.ext
  exact congrArg plusSuccessor (leftPhiStagesSectionEquiv_val k r i l).symm

/-- The nested kernel is the same actual radical, with the stages membership removed. -/
def leftPhiStagesKernelEquiv (i : Fin 2) :
    (leftPhiStagesRetraction k r (R := R) i).ker ≃* radical (k + r + 2) R :=
  (splitStagesKernelEquiv plusProjection plusSuccessor plusProjection_plusSuccessor
    (leftStages k r R i) (leftStages_contains_kernel k r i)).trans
    (plusKernelRadicalEquiv (k + r + 1))

/-- Switch from a kernel-side intersection to the actual radical intersection. -/
def plusKernelIntersectionEquiv (n : ℕ) (H : Subgroup (plusSubgroup n R)) :
    H.comap (plusProjection (n := n) (F := R)).ker.subtype ≃*
      H.comap plusRadical where
  toFun u := ⟨plusKernelRadicalEquiv n u.val, u.property⟩
  invFun u := ⟨(plusKernelRadicalEquiv n).symm u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual nested coefficient intersection, as a subgroup of the stabilizer. -/
abbrev leftPhiStagesIntersection (i : Fin 2) :=
  kernelIntersection (leftPhiStagesRetraction k r (R := R) i)
    (leftPhiStagesStabilizer k r i)

/-- Remove the nested membership proofs, retaining precisely the same radical matrix. -/
def leftPhiStagesIntersectionEquiv (i : Fin 2) :
    leftPhiStagesIntersection k r (R := R) i ≃* leftRadicalIntersection k r R i :=
  (intersectionEquiv (leftPhiStagesRetraction k r i)
      (leftPhiStagesStabilizer k r i)).trans
    ((splitStagesIntersectionEquiv plusProjection plusSuccessor plusProjection_plusSuccessor
      (leftStages k r R i) (leftStabilizer k r R i)
      (leftStages_contains_kernel k r i)).trans
      (plusKernelIntersectionEquiv (k + r + 1) (leftStabilizer k r R i)))

variable [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R)

/-- The positive ambient character on the actual plus-projection kernel. -/
def plusKernelTheta (n : ℕ) :
    (plusProjection (n := n) (F := R)).ker →* ℂˣ :=
  (Mirabolic.theta ψ n).comp (plusKernelRadicalEquiv n).toMonoidHom

/-- The positive character is fixed by the actual successor section. -/
theorem plusKernelTheta_sectionInvariant (n : ℕ) :
    SectionInvariant plusProjection plusSuccessor (plusKernelTheta ψ n) := by
  intro l u
  have h := Mirabolic.theta_isInvariant ψ n (successorEquiv l⁻¹)
    (plusKernelRadicalEquiv n u)
  have he : plusKernelRadicalEquiv n (kernelConjugate plusProjection plusSuccessor l u) =
      Jacquet.Localization.conjugate (radical (n + 1) R) (successorSubgroup n R)
        successorSubgroup_le_normalizer (successorEquiv l⁻¹)
        (plusKernelRadicalEquiv n u) := by
    apply Subtype.ext
    change (successor l)⁻¹ * u.val.val * successor l =
      successor l⁻¹ * u.val.val * (successor l⁻¹)⁻¹
    rw [map_inv, inv_inv]
  change Mirabolic.theta ψ n
      (plusKernelRadicalEquiv n (kernelConjugate plusProjection plusSuccessor l u)) =
    Mirabolic.theta ψ n (plusKernelRadicalEquiv n u)
  rw [he]
  exact h

/-- The positive ambient character on the actual restricted stages kernel. -/
def leftPhiStagesTheta (i : Fin 2) :
    (leftPhiStagesRetraction k r (R := R) i).ker →* ℂˣ :=
  (Mirabolic.theta ψ (k + r + 1)).comp (leftPhiStagesKernelEquiv k r i).toMonoidHom

/-- Section invariance restricts without enlarging the section-containment hypothesis. -/
theorem leftPhiStagesTheta_sectionInvariant (i : Fin 2) :
    SectionInvariant (leftPhiStagesRetraction k r i) (leftPhiStagesSection k r i)
      (leftPhiStagesTheta k r ψ i) := by
  intro l u
  exact plusKernelTheta_sectionInvariant ψ (k + r + 1) l.val
    (splitStagesKernelEquiv plusProjection plusSuccessor plusProjection_plusSuccessor
      (leftStages k r R i) (leftStages_contains_kernel k r i) u)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The representation of the actual nested stabilizer, obtained solely by restriction. -/
abbrev leftPhiStagesRepresentation (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V) :=
  σ.comp (leftPhiStagesInducingEquiv k r (R := R) i).toMonoidHom

/-- The actual nested localized coefficient with its unnormalized section action. -/
abbrev leftPhiStagesAction (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V) :=
  subgroupAction (leftPhiStagesRetraction k r i) (leftPhiStagesSection k r i)
    (leftPhiStagesTheta k r ψ i) (leftPhiStagesTheta_sectionInvariant k r ψ i)
    (leftPhiStagesStabilizer k r i) (leftPhiStagesSection_mem k r i)
    (leftPhiStagesRepresentation k r i σ)

@[simp] theorem leftPhiStagesAction_mk (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V)
    (l : (leftStages k r R i).comap plusSuccessor) (v : V) :
    leftPhiStagesAction k r ψ i σ l (mk _ _ _ v) =
      mk _ _ _ ((leftPhiStagesRepresentation k r i σ)
        (subgroupSection (leftPhiStagesSection k r i)
          (leftPhiStagesStabilizer k r i) (leftPhiStagesSection_mem k r i) l) v) :=
  subgroupAction_mk _ _ _ _ _ _ _ l v

/-- Identity on representatives identifies the nested quotient with localization
at the whole actual radical intersection. -/
def leftPhiStagesCoefficientEquiv (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V) :
    Coinvariants (leftPhiStagesRepresentation k r i σ)
        (leftPhiStagesIntersection k r i)
        (intersectionCharacter (leftPhiStagesRetraction k r i)
          (leftPhiStagesTheta k r ψ i) (leftPhiStagesStabilizer k r i)) ≃ₗ[ℂ]
      Coinvariants (σ.comp (leftRadicalInclusion k r R i))
        (⊤ : Subgroup (leftRadicalIntersection k r R i))
        ((leftOrbitTheta k r ψ i).comp (⊤ : Subgroup _).subtype) :=
  transportEquiv _ _ _ _ _ _
    ((leftPhiStagesIntersectionEquiv k r i).trans Subgroup.topEquiv.symm)
    (LinearEquiv.refl ℂ V) (fun _ _ => rfl) (fun _ => rfl)

@[simp] theorem leftPhiStagesCoefficientEquiv_mk (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V) (v : V) :
    leftPhiStagesCoefficientEquiv k r ψ i σ (mk _ _ _ v) =
      mk (σ.comp (leftRadicalInclusion k r R i)) ⊤
        ((leftOrbitTheta k r ψ i).comp (⊤ : Subgroup _).subtype) v := rfl

/-- The transported section action retains the actual inducing section on every class. -/
theorem leftPhiStagesCoefficientEquiv_section_mk (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r R i) V)
    (l : (leftStages k r R i).comap plusSuccessor) (v : V) :
    leftPhiStagesCoefficientEquiv k r ψ i σ
        (leftPhiStagesAction k r ψ i σ l (mk _ _ _ v)) =
      mk (σ.comp (leftRadicalInclusion k r R i)) ⊤
        ((leftOrbitTheta k r ψ i).comp (⊤ : Subgroup _).subtype)
        (σ (sectionInclusion (leftInducing k r R) (leftRepresentative k r R i)
          (leftPhiStagesSectionEquiv k r i l)) v) := by
  exact (congrArg (leftPhiStagesCoefficientEquiv k r ψ i σ)
      (leftPhiStagesAction_mk k r ψ i σ l v)).trans
    ((leftPhiStagesCoefficientEquiv_mk k r ψ i σ
      ((leftPhiStagesRepresentation k r i σ)
        (subgroupSection (leftPhiStagesSection k r i)
          (leftPhiStagesStabilizer k r i) (leftPhiStagesSection_mem k r i) l) v)).trans
      (congrArg (fun h => mk (σ.comp (leftRadicalInclusion k r R i)) ⊤
        ((leftOrbitTheta k r ψ i).comp (⊤ : Subgroup _).subtype) (σ h v))
        (leftPhiStagesInducingEquiv_section k r i l)))

omit [TopologicalSpace R] in
/-- On the identity orbit the actual inducing section acts by the lower GL
coefficient and the successor of the lower mirabolic coefficient. -/
theorem leftPhiInducingSection_tmul
    (ρ : Representation ℂ (GeneralLinear (k + 1) R) V)
    (τ : Representation ℂ (mirabolic (r + 1) R) W)
    (g : leftSection k r R 1) (v : V) (w : W) :
    ((external ρ τ).comp (leftCoefficient k r R 1))
        (sectionInclusion (leftInducing k r R) (leftRepresentative k r R 1) g)
        (v ⊗ₜ w) =
      ρ (leftProjection (leftIdentitySectionEquiv k r R g)).1 v ⊗ₜ
        τ (successor (leftProjection (leftIdentitySectionEquiv k r R g)).2) w := by
  change external ρ τ (leftSectionCoefficient k r R 1 g) (v ⊗ₜ w) = _
  rw [leftSectionCoefficient_one]
  rfl

/-- The transported actual identity-orbit section action on every pure tensor class. -/
theorem leftPhiStagesCoefficientEquiv_one_section_tmul
    (ρ : Representation ℂ (GeneralLinear (k + 1) R) V)
    (τ : Representation ℂ (mirabolic (r + 1) R) W)
    (l : (leftStages k r R 1).comap plusSuccessor) (v : V) (w : W) :
    leftPhiStagesCoefficientEquiv k r ψ 1 ((external ρ τ).comp (leftCoefficient k r R 1))
        (leftPhiStagesAction k r ψ 1 ((external ρ τ).comp (leftCoefficient k r R 1))
          l (mk _ _ _ (v ⊗ₜ w))) =
      mk (((external ρ τ).comp (leftCoefficient k r R 1)).comp
          (leftRadicalInclusion k r R 1)) ⊤
        ((leftOrbitTheta k r ψ 1).comp (⊤ : Subgroup _).subtype)
        (ρ (leftProjection (leftIdentitySectionEquiv k r R
            (leftPhiStagesSectionEquiv k r 1 l))).1 v ⊗ₜ
          τ (successor (leftProjection (leftIdentitySectionEquiv k r R
            (leftPhiStagesSectionEquiv k r 1 l))).2) w) := by
  exact (leftPhiStagesCoefficientEquiv_section_mk k r ψ 1
      ((external ρ τ).comp (leftCoefficient k r R 1)) l (v ⊗ₜ w)).trans
    (congrArg (mk (((external ρ τ).comp (leftCoefficient k r R 1)).comp
        (leftRadicalInclusion k r R 1)) ⊤
      ((leftOrbitTheta k r ψ 1).comp (⊤ : Subgroup _).subtype))
      (leftPhiInducingSection_tmul k r ρ τ (leftPhiStagesSectionEquiv k r 1 l) v w))

/-- The actual nested subgroup map, for an arbitrary stabilizer intertwiner. -/
abbrev leftPhiStagesMap (i : Fin 2)
    {σ : Representation ℂ (leftStabilizer k r R i) V}
    {τ : Representation ℂ (leftStabilizer k r R i) W} (f : σ.IntertwiningMap τ) :=
  subgroupMap (leftPhiStagesRetraction k r i) (leftPhiStagesSection k r i)
    (leftPhiStagesTheta k r ψ i) (leftPhiStagesTheta_sectionInvariant k r ψ i)
    (leftPhiStagesStabilizer k r i) (leftPhiStagesSection_mem k r i)
    (restrictAlongMap (leftPhiStagesInducingEquiv k r i).toMonoidHom f)

@[simp] theorem leftPhiStagesMap_mk (i : Fin 2)
    {σ : Representation ℂ (leftStabilizer k r R i) V}
    {τ : Representation ℂ (leftStabilizer k r R i) W}
    (f : σ.IntertwiningMap τ) (v : V) :
    leftPhiStagesMap k r ψ i f (mk _ _ _ v) = mk _ _ _ (f v) :=
  subgroupMap_mk _ _ _ _ _ _ _ v

/-- Class-preserving transport is natural for arbitrary intertwiners on
independent carrier universes. -/
theorem leftPhiStagesCoefficientEquiv_natural (i : Fin 2)
    {σ : Representation ℂ (leftStabilizer k r R i) V}
    {τ : Representation ℂ (leftStabilizer k r R i) W}
    (f : σ.IntertwiningMap τ)
    (z : Coinvariants (leftPhiStagesRepresentation k r i σ)
      (leftPhiStagesIntersection k r i)
      (intersectionCharacter (leftPhiStagesRetraction k r i)
        (leftPhiStagesTheta k r ψ i) (leftPhiStagesStabilizer k r i))) :
    leftPhiStagesCoefficientEquiv k r ψ i τ (leftPhiStagesMap k r ψ i f z) =
      mapLinear ⊤ ((leftOrbitTheta k r ψ i).comp (⊤ : Subgroup _).subtype)
        (restrictAlongMap (leftRadicalInclusion k r R i) f)
        (leftPhiStagesCoefficientEquiv k r ψ i σ z) := by
  refine Submodule.Quotient.induction_on _ z (fun v => ?_)
  exact (congrArg (leftPhiStagesCoefficientEquiv k r ψ i τ)
      (leftPhiStagesMap_mk k r ψ i f v)).trans
    (leftPhiStagesCoefficientEquiv_mk k r ψ i τ (f v))

end Langlands.Derivative.MirabolicProductMinus
