import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Representation.Induction.SmoothGroupTransport
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Normalized parabolic functors across an equivalence of ambient groups -/

noncomputable section

open CategoryTheory Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV

namespace GroupTransport

section Subgroups

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction of an ambient continuous group equivalence to actual subgroups. -/
def subgroupEquiv (e : H ≃ₜ* G) {P : Subgroup G} {Q : Subgroup H}
    (hPQ : ∀ x : H, x ∈ Q ↔ e x ∈ P) : Q ≃ₜ* P where
  toFun x := ⟨e x, (hPQ x).mp x.property⟩
  invFun x := ⟨e.symm x, (hPQ _).mpr (by simp)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem subgroupEquiv_apply (e : H ≃ₜ* G) {P : Subgroup G} {Q : Subgroup H}
    (hPQ : ∀ x : H, x ∈ Q ↔ e x ∈ P) (x : Q) :
    (subgroupEquiv e hPQ x : G) = e (x : H) := rfl

@[simp]
theorem subgroupEquiv_symm_apply (e : H ≃ₜ* G) {P : Subgroup G} {Q : Subgroup H}
    (hPQ : ∀ x : H, x ∈ Q ↔ e x ∈ P) (x : P) :
    ((subgroupEquiv e hPQ).symm x : H) = e.symm (x : G) := rfl

end Subgroups

section Characters

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  {U M : Subgroup G} {U' M' : Subgroup H}

/-- Haar modulus restricted to corresponding normalizing subgroups is preserved. -/
theorem closedRestrictCharacter_transport (e : H ≃ₜ* G)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set H)) (m : M') :
    HaarModulus.closedRestrictCharacter U' hU' M' hM'U' m =
      HaarModulus.closedRestrictCharacter U hU M hMU (subgroupEquiv e hMM' m) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace U' := borel U'
  let : BorelSpace U' := ⟨rfl⟩
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar
      (HaarModulus.normalizerConj U' (Subgroup.inclusion hM'U' m)) =
    MeasureTheory.mulEquivHaarChar
      (HaarModulus.normalizerConj U (Subgroup.inclusion hMU (subgroupEquiv e hMM' m)))
  have hconj : HaarModulus.normalizerConj U' (Subgroup.inclusion hM'U' m) =
      ((subgroupEquiv e hUU').trans
        (HaarModulus.normalizerConj U (Subgroup.inclusion hMU (subgroupEquiv e hMM' m)))).trans
          (subgroupEquiv e hUU').symm := by
    ext u
    apply e.injective
    change e ((m : H) * (u : H) * (m : H)⁻¹) =
      e (e.symm (e (m : H) * e (u : H) * (e (m : H))⁻¹))
    simp only [map_mul, map_inv, e.apply_symm_apply]
  rw [hconj, mulEquivHaarChar_trans_symm]

/-- The positive half modulus agrees under ambient group transport. -/
theorem closedHalfCharacter_transport (e : H ≃ₜ* G)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set H)) (m : M') :
    HaarModulus.closedHalfCharacter U' hU' M' hM'U' m =
      HaarModulus.closedHalfCharacter U hU M hMU (subgroupEquiv e hMM' m) := by
  unfold HaarModulus.closedHalfCharacter Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.comp_apply]
  rw [closedRestrictCharacter_transport e hUU' hMM' hU hU' hMU hM'U' m]

/-- The inverse half modulus agrees under ambient group transport. -/
theorem closedInverseHalfCharacter_transport (e : H ≃ₜ* G)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hM'U' : M' ≤ Subgroup.normalizer (U' : Set H)) (m : M') :
    HaarModulus.closedInverseHalfCharacter U' hU' M' hM'U' m =
      HaarModulus.closedInverseHalfCharacter U hU M hMU (subgroupEquiv e hMM' m) := by
  unfold HaarModulus.closedInverseHalfCharacter Jacquet.inverseHalfCharacter
    Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
  rw [closedRestrictCharacter_transport e hUU' hMM' hU hU' hMU hM'U' m]

end Characters

section Projection

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {P M U : Subgroup G} {P' M' U' : Subgroup H}

/-- The actual semidirect-product projections agree after transport. -/
theorem projection_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U) (p : P') :
    subgroupEquiv e hMM' (h'.projection p) = h.projection (subgroupEquiv e hPP' p) := by
  symm
  rw [h.projection_eq_iff]
  have hmem := (hUU' _).mp (h'.projection_inv_mul_mem p)
  change (e ((h'.projection p : M') : H))⁻¹ * e (p : H) ∈ U
  simpa only [map_mul, map_inv] using hmem

end Projection

section Functors

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {P M U : Subgroup G} {P' M' U' : Subgroup H}

/-- Normalized Jacquet restriction commutes with the specified group equivalence.
The component is the identity on vector representatives of the two quotients. -/
def jacquetIsoApp (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    (SmoothRep.pullbackFunctor (subgroupEquiv e hMM')).obj ((jacquetFunctor h hU).obj A) ≅
      (jacquetFunctor h' hU').obj ((SmoothRep.pullbackFunctor e).obj A) :=
  let t := Jacquet.Localization.transportEquiv
    (A.representation.comp e.toMonoidHom) A.representation U' U 1 1
    (subgroupEquiv e hUU').toMulEquiv (LinearEquiv.refl ℂ A)
    (fun _ _ => rfl) (fun _ => rfl)
  SmoothRep.mkIso (Representation.Equiv.mk t.symm (fun m => by
    apply Jacquet.Localization.hom_ext
    ext v
    have ht (w : A) : t.symm (Jacquet.Localization.mk A.representation U 1 w) =
        Jacquet.Localization.mk (A.representation.comp e.toMonoidHom) U' 1 w := by
      apply t.injective
      rw [t.apply_symm_apply]
      rfl
    change t.symm (((jacquetFunctor h hU).obj A).representation
        (subgroupEquiv e hMM' m) (Jacquet.Localization.mk A.representation U 1 v)) =
      ((jacquetFunctor h' hU').obj (SmoothRep.pullback e A)).representation m
        (t.symm (Jacquet.Localization.mk A.representation U 1 v))
    rw [ht]
    change t.symm
        (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
          (subgroupEquiv e hMM' m) : ℂˣ) : ℂ) •
            Jacquet.Localization.mk A.representation U 1
              (A.representation (e (m : H)) v)) =
      ((HaarModulus.closedInverseHalfCharacter U' hU' M' h'.levi_le_normalizer m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk (A.representation.comp e.toMonoidHom) U' 1
          (A.representation (e (m : H)) v)
    rw [closedInverseHalfCharacter_transport e hUU' hMM' hU hU'
      h.levi_le_normalizer h'.levi_le_normalizer m, map_smul, ht]))

/-- The Jacquet component retains the actual vector representative. -/
@[simp]
theorem jacquetIsoApp_hom_mk (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    SmoothRep.hom (jacquetIsoApp h h' e hMM' hUU' hU hU' A).hom
        (Jacquet.Localization.mk A.representation U 1 v) =
      Jacquet.Localization.mk (A.representation.comp e.toMonoidHom) U' 1 v := rfl

/-- Normalized Jacquet restriction is natural under ambient group transport. -/
def jacquetIso (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H)) :
    jacquetFunctor.{uG, uV} h hU ⋙ SmoothRep.pullbackFunctor (subgroupEquiv e hMM') ≅
      SmoothRep.pullbackFunctor e ⋙ jacquetFunctor h' hU' :=
  NatIso.ofComponents (jacquetIsoApp h h' e hMM' hUU' hU hU') (fun {A B} f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext v
    rfl)

/-- Half modulus and Levi projection identify the actual inducing actions. -/
theorem inducingRepresentation_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ M) (p : P') :
    inducingRepresentation h' hU' ((SmoothRep.pullbackFunctor (subgroupEquiv e hMM')).obj A) p =
      inducingRepresentation h hU A (subgroupEquiv e hPP' p) := by
  change ((HaarModulus.closedHalfCharacter U' hU' P' h'.le_normalizer p : ℂˣ) : ℂ) •
      A.representation (subgroupEquiv e hMM' (h'.projection p)) =
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer (subgroupEquiv e hPP' p) : ℂˣ) :
        ℂ) • A.representation (h.projection (subgroupEquiv e hPP' p))
  rw [closedHalfCharacter_transport e hUU' hPP' hU hU' h.le_normalizer h'.le_normalizer p,
    projection_transport h h' e hPP' hMM' hUU' p]

/-- Precomposition by the ambient equivalence transports normalized induction. -/
def inductionIsoApp (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    (SmoothRep.pullbackFunctor e).obj ((normalizedInductionFunctor h hU).obj A) ≅
      (normalizedInductionFunctor h' hU').obj
        ((SmoothRep.pullbackFunctor (subgroupEquiv e hMM')).obj A) :=
  SmoothRep.mkIso (Induction.precomposeSmoothInducedGroupEquiv e
    (subgroupEquiv e hPP').toMulEquiv (fun _ => rfl)
    (fun p => (inducingRepresentation_transport h h' e hPP' hMM' hUU' hU hU' A p).symm))

/-- Naturality of normalized induction under the specified ambient equivalence. -/
def inductionIso (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H)) :
    normalizedInductionFunctor.{uG, uV} h hU ⋙ SmoothRep.pullbackFunctor e ≅
      SmoothRep.pullbackFunctor (subgroupEquiv e hMM') ⋙ normalizedInductionFunctor h' hU' :=
  NatIso.ofComponents (inductionIsoApp h h' e hPP' hMM' hUU' hU hU') (fun {A B} f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    apply Subtype.ext
    funext y
    rfl)

/-- The induction isomorphism sends a function to its precomposition by `e`. -/
@[simp]
theorem inductionIsoApp_hom_eval (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (y : H) :
    Induction.eval P'
        (inducingRepresentation h' hU' ((SmoothRep.pullbackFunctor (subgroupEquiv e hMM')).obj A))
        (SmoothRep.hom (inductionIsoApp h h' e hPP' hMM' hUU' hU hU' A).hom f) y =
      Induction.eval P (inducingRepresentation h hU A) f (e y) := rfl

section K0

open SmoothRep.FiniteLengthGrothendieckGroup

/-- The exact K0 maps of normalized induction commute with group transport. -/
theorem inductionK0_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hl' : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h' hU'))
    (hx' : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h' hU')) :
    (FiniteLengthGrothendieckGroup.pullback.{uG, uG, max uG uV} e).comp (inductionK0 h hU hl hx) =
      (inductionK0 h' hU' hl' hx').comp (FiniteLengthGrothendieckGroup.pullback (subgroupEquiv e hMM')) :=
  calc
    _ = map (normalizedInductionFunctor.{uG, max uG uV} h hU ⋙ SmoothRep.pullbackFunctor e)
        (hl.comp (SmoothRep.pullbackFunctor_preservesFiniteLength e))
        (PreservesFiniteLengthShortExact.comp hl hx
          (SmoothRep.pullbackFunctor_preservesShortExact e)) :=
      (map_comp _ _ hl hx (SmoothRep.pullbackFunctor_preservesFiniteLength e)
        (SmoothRep.pullbackFunctor_preservesShortExact e) _ _).symm
    _ = map (SmoothRep.pullbackFunctor (subgroupEquiv e hMM') ⋙
          normalizedInductionFunctor.{uG, max uG uV} h' hU')
        ((SmoothRep.pullbackFunctor_preservesFiniteLength _).comp hl')
        (PreservesFiniteLengthShortExact.comp
          (SmoothRep.pullbackFunctor_preservesFiniteLength _)
          (SmoothRep.pullbackFunctor_preservesShortExact _) hx') :=
      map_eq_of_iso (inductionIso.{uG, max uG uV} h h' e hPP' hMM' hUU' hU hU') _ _ _ _
    _ = _ := map_comp _ _ (SmoothRep.pullbackFunctor_preservesFiniteLength _)
      (SmoothRep.pullbackFunctor_preservesShortExact _) hl' hx' _ _

/-- The exact K0 maps of normalized Jacquet restriction commute with transport. -/
theorem jacquetK0_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hl : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h hU))
    (hl' : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h' hU'))
    (hx' : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h' hU')) :
    (FiniteLengthGrothendieckGroup.pullback.{uG, uG, max uG uV} (subgroupEquiv e hMM')).comp (jacquetK0 h hU hl hx) =
      (jacquetK0 h' hU' hl' hx').comp (FiniteLengthGrothendieckGroup.pullback e) :=
  calc
    _ = map (jacquetFunctor.{uG, max uG uV} h hU ⋙
          SmoothRep.pullbackFunctor (subgroupEquiv e hMM'))
        (hl.comp (SmoothRep.pullbackFunctor_preservesFiniteLength _))
        (PreservesFiniteLengthShortExact.comp hl hx
          (SmoothRep.pullbackFunctor_preservesShortExact _)) :=
      (map_comp _ _ hl hx (SmoothRep.pullbackFunctor_preservesFiniteLength _)
        (SmoothRep.pullbackFunctor_preservesShortExact _) _ _).symm
    _ = map (SmoothRep.pullbackFunctor e ⋙ jacquetFunctor.{uG, max uG uV} h' hU')
        ((SmoothRep.pullbackFunctor_preservesFiniteLength e).comp hl')
        (PreservesFiniteLengthShortExact.comp
          (SmoothRep.pullbackFunctor_preservesFiniteLength e)
          (SmoothRep.pullbackFunctor_preservesShortExact e) hx') :=
      map_eq_of_iso (jacquetIso.{uG, max uG uV} h h' e hMM' hUU' hU hU') _ _ _ _
    _ = _ := map_comp _ _ (SmoothRep.pullbackFunctor_preservesFiniteLength e)
      (SmoothRep.pullbackFunctor_preservesShortExact e) hl' hx' _ _

/-- The actual normalized induction-after-Jacquet term commutes with transport. -/
theorem inductionJacquetK0_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hfl : ParabolicFiniteLength.{uG, max uG uV} h hU)
    (hfl' : ParabolicFiniteLength.{uG, max uG uV} h' hU') :
    (FiniteLengthGrothendieckGroup.pullback.{uG, uG, max uG uV} e).comp
        ((inductionK0 h hU hfl.1 hfl.2.1).comp
          (jacquetK0 h hU hfl.2.2.1 hfl.2.2.2)) =
      ((inductionK0 h' hU' hfl'.1 hfl'.2.1).comp
        (jacquetK0 h' hU' hfl'.2.2.1 hfl'.2.2.2)).comp (FiniteLengthGrothendieckGroup.pullback e) := by
  rw [← LinearMap.comp_assoc,
    inductionK0_transport h h' e hPP' hMM' hUU' hU hU' hfl.1 hfl.2.1 hfl'.1 hfl'.2.1,
    LinearMap.comp_assoc,
    jacquetK0_transport h h' e hMM' hUU' hU hU' hfl.2.2.1 hfl.2.2.2
      hfl'.2.2.1 hfl'.2.2.2,
    LinearMap.comp_assoc]

end K0

end Functors

end GroupTransport
end Langlands.Aubert.General
