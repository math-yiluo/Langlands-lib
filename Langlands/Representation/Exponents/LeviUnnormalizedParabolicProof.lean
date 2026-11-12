import Langlands.Representation.Exponents.LeviUnnormalizedParabolicStatements
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Exponents.LeviParabolicFunctorsPreserveLimitsProof

/-! # Renard VI.1.1 for the actual unnormalized parabolic functors -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

namespace UnnormalizedParabolic

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U)

/-- Smooth induction of the trivial extension along the Levi projection. -/
abbrev induction : SmoothRep.{0, u, v} ℂ M ⥤ SmoothRep.{0, u, max u v} ℂ G :=
  inflationFunctor h ⋙ Induction.smoothInductionFunctor P

/-- The radical relation quotient with the untwisted Levi action. -/
abbrev jacquet : SmoothRep.{0, u, v} ℂ G ⥤ SmoothRep.{0, u, v} ℂ M :=
  Jacquet.Localization.smoothFunctor U 1 M h.levi_le_normalizer
    (Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer)

variable (A : SmoothRep.{0, u, w} ℂ G) (σ : SmoothRep.{0, u, v} ℂ M)

/-- Evaluation at one as a linear map on the original representation. -/
def evaluation (F : A.representation.IntertwiningMap ((induction h).obj σ).representation) :
    A →ₗ[ℂ] σ where
  toFun x := Induction.eval P (σ.representation.comp h.projection) (F x) 1
  map_add' _ _ := by change (F _).1.1 1 = _; rw [map_add]; rfl
  map_smul' _ _ := by change (F _).1.1 1 = _; rw [map_smul]; rfl

omit [LocallyCompactSpace G] in
/-- Translating before evaluation gives the value at that group element. -/
theorem evaluation_translate
    (F : A.representation.IntertwiningMap ((induction h).obj σ).representation)
    (g : G) (x : A) :
    evaluation h A σ F (A.representation g x) =
      Induction.eval P (σ.representation.comp h.projection) (F x) g := by
  have he := Representation.IntertwiningMap.isIntertwining _ _ F g x
  have hh := congrArg (fun f => Induction.eval P (σ.representation.comp h.projection) f 1) he
  change (F (A.representation g x)).1.1 1 = (F x).1.1 (1 * g) at hh
  change (F (A.representation g x)).1.1 1 = (F x).1.1 g
  simpa only [one_mul] using hh

omit [LocallyCompactSpace G] in
/-- Evaluation is covariant for the inflated Levi action. -/
theorem evaluation_covariance
    (F : A.representation.IntertwiningMap ((induction h).obj σ).representation)
    (p : P) (x : A) :
    evaluation h A σ F (A.representation p x) =
      σ.representation (h.projection p) (evaluation h A σ F x) := by
  rw [evaluation_translate]
  have he := (F x).1.property p 1
  change (F x).1.1 ((p : G) * 1) =
    σ.representation (h.projection p) ((F x).1.1 1) at he
  change (F x).1.1 p = σ.representation (h.projection p) ((F x).1.1 1)
  simpa only [mul_one] using he

/-- Evaluation kills the radical relations and descends to the Levi coinvariants. -/
def forward (F : A.representation.IntertwiningMap ((induction h).obj σ).representation) :
    ((jacquet h).obj A).representation.IntertwiningMap σ.representation where
  toLinearMap := Jacquet.Localization.lift A.representation U 1 (evaluation h A σ F) (by
    intro n x
    have he := evaluation_covariance h A σ F ⟨n, h.unipotent_le n.2⟩ x
    simpa only [h.projection_unipotent, map_one, Module.End.one_apply,
      MonoidHom.one_apply, Units.val_one, one_smul] using he)
  isIntertwining' m := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 q
    change evaluation h A σ F (A.representation m x) =
      σ.representation m (evaluation h A σ F x)
    simpa only [h.projection_levi] using
      evaluation_covariance h A σ F ⟨m, h.levi_le m.2⟩ x

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The inflated Levi action agrees with the parabolic action on coinvariants. -/
theorem quotient_covariance
    (f : ((jacquet h).obj A).representation.IntertwiningMap σ.representation)
    (p : P) (x : A) :
    f (Jacquet.Localization.mk A.representation U 1 (A.representation p x)) =
      σ.representation (h.projection p) (f (Jacquet.Localization.mk A.representation U 1 x)) := by
  let m := h.projection p
  let n : U := ⟨(m : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hp : (p : G) = (m : G) * (n : G) := by simp [n]
  rw [hp, map_mul, Module.End.mul_apply]
  change f (((jacquet h).obj A).representation m
      (Jacquet.Localization.mk A.representation U 1 (A.representation n x))) = _
  rw [Representation.IntertwiningMap.isIntertwining, Jacquet.Localization.mk_apply_subgroup]
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rfl

/-- The inverse to descended evaluation, before taking smooth vectors. -/
def orbitMap (f : ((jacquet h).obj A).representation.IntertwiningMap σ.representation) :
    A.representation.IntertwiningMap
      (Induction.equivariantAction P (σ.representation.comp h.projection)) where
  toLinearMap :=
    { toFun := fun x => ⟨fun g => f (Jacquet.Localization.mk A.representation U 1
          (A.representation g x)), by
        intro p g
        change f (Jacquet.Localization.mk A.representation U 1
          (A.representation ((p : G) * g) x)) =
            σ.representation (h.projection p)
              (f (Jacquet.Localization.mk A.representation U 1 (A.representation g x)))
        rw [map_mul, Module.End.mul_apply]
        exact quotient_covariance h A σ f p (A.representation g x)⟩
      map_add' x y := by
        ext g
        exact (f.toLinearMap.comp ((Jacquet.Localization.mk A.representation U 1).comp
          (A.representation g))).map_add x y
      map_smul' c x := by
        ext g
        exact (f.toLinearMap.comp ((Jacquet.Localization.mk A.representation U 1).comp
          (A.representation g))).map_smul c x }
  isIntertwining' g := by
    ext x y
    change f (Jacquet.Localization.mk A.representation U 1
      (A.representation y (A.representation g x))) =
        f (Jacquet.Localization.mk A.representation U 1 (A.representation (y * g) x))
    rw [map_mul, Module.End.mul_apply]

/-- Evaluation and covariant orbit functions give unnormalized first adjointness. -/
def equiv :
    A.representation.IntertwiningMap ((induction h).obj σ).representation ≃ₗ[ℂ]
      ((jacquet h).obj A).representation.IntertwiningMap σ.representation where
  toFun := forward h A σ
  invFun f := smoothLift A.isSmooth (orbitMap h A σ f)
  left_inv F := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact evaluation_translate h A σ F g x
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext x
    change f (Jacquet.Localization.mk A.representation U 1 (A.representation 1 x)) = _
    rw [map_one, Module.End.one_apply]
    rfl
  map_add' _ _ := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext x
    rfl
  map_smul' _ _ := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext x
    rfl

/-- A scalar twist is an equivalence, with inverse the reciprocal twist. -/
def characterTwistEquivalence (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) :
    SmoothRep.{0, u, v} ℂ M ≌ SmoothRep.{0, u, v} ℂ M where
  functor := SmoothRep.twistFunctor χ hχ
  inverse := SmoothRep.twistFunctor χ⁻¹ (isOpen_ker_inv hχ)
  unitIso := NatIso.ofComponents (fun X =>
    (show (SmoothRep.twistFunctor χ hχ ⋙ SmoothRep.twistFunctor χ⁻¹ (isOpen_ker_inv hχ)).obj X ≅ X
      from SmoothRep.mkIso (equivOfRepresentationEq (twist_inv_twist χ X.representation))).symm)
    (by intro X Y f; apply ObjectProperty.hom_ext; ext x; rfl)
  counitIso := NatIso.ofComponents (fun X =>
    SmoothRep.mkIso (equivOfRepresentationEq (twist_twist_inv χ X.representation)))
    (by intro X Y f; apply ObjectProperty.hom_ext; ext x; rfl)
  functor_unitIso_comp X := by apply ObjectProperty.hom_ext; ext x; rfl

/-- Inverse-half twisting before normalized induction cancels its normalizing character.
The comparison keeps every value of every induced function. -/
def cancelNormalizationIso (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU) :
    SmoothRep.twistFunctor.{0, u, v}
        (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
        (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M h.levi_le_normalizer) ⋙
      normalizedInductionFunctor h hU ≅ induction h :=
  NatIso.ofComponents (fun X => SmoothRep.mkIso (Induction.smoothInducedEquiv P
    (equivOfRepresentationEq (by
      ext p x
      change ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
        (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
          (h.projection p) : ℂˣ) : ℂ) • X.representation (h.projection p) x) = _
      rw [smul_smul]
      have hc : ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) *
          ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
            (h.projection p) : ℂˣ) : ℂ) = 1 := by
        rw [closedHalfCharacter_eq_comp_projection h hU hδ, MonoidHom.comp_apply,
          ← Units.val_mul]
        simp [HaarModulus.closedHalfCharacter, HaarModulus.closedInverseHalfCharacter,
          Jacquet.inverseHalfCharacter]
      rw [hc, one_smul]
      rfl)))) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    ext x
    rfl)

/-- Unnormalized induction preserves limits at the original diagram size. -/
theorem induction_preservesLimits (hU : IsClosed (U : Set G))
    (hδ : IsUnimodularModulus U hU) :
    PreservesLimitsOfSize.{v, v} (induction.{u, v} h) := by
  have := normalizedInductionFunctor_preservesLimits.{u, v} h hU hδ
  have : (SmoothRep.twistFunctor.{0, u, v}
      (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
      (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M h.levi_le_normalizer)).IsEquivalence :=
    (characterTwistEquivalence.{u, v}
    (HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer)
    (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M h.levi_le_normalizer)).isEquivalence_functor
  exact preservesLimits_of_natIso (cancelNormalizationIso h hU hδ)

/-- Unnormalized induction preserves colimits for a compact parabolic quotient. -/
theorem induction_preservesColimits [T2Space G] (hU : IsClosed (U : Set G))
    (hδ : IsUnimodularModulus U hU) (hcof : CompactOpenCofinal G)
    (hP : IsClosed (P : Set G)) (hproj : Continuous h.projection)
    [CompactSpace (Induction.LeftQuotient P)] :
    PreservesColimitsOfSize.{v, v} (induction.{u, v} h) := by
  have := normalizedInductionFunctor_preservesColimits.{u, v} h hU hcof hP hproj
  exact preservesColimits_of_natIso (cancelNormalizationIso h hU hδ)

omit [LocallyCompactSpace G] in
/-- Removing the scalar twist leaves the underlying coinvariant module functor unchanged. -/
theorem jacquet_preservesColimits :
    PreservesColimitsOfSize.{v, v} (jacquet.{u, v} h) := by
  have : PreservesColimitsOfSize.{v, v}
      (SmoothRep.toRep : SmoothRep.{0, u, v} ℂ G ⥤ Rep.{v} ℂ G) :=
    (SmoothRep.toRepSmoothPartAdjunction ℂ G).leftAdjoint_preservesColimits
  let e : jacquet.{u, v} h ⋙ SmoothRep.forgetToModule M ≅
      SmoothRep.toRep ⋙ Rep.resFunctor U.subtype ⋙ Rep.coinvariantsFunctor ℂ U :=
    NatIso.ofComponents
      (fun X => (Jacquet.Localization.trivialEquiv X.representation U M
        h.levi_le_normalizer).toLinearEquiv.toModuleIso)
      (by
        intro X Y f
        ext q
        obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective X.representation U 1 q
        rfl)
  have : PreservesColimitsOfSize.{v, v}
      (jacquet.{u, v} h ⋙ SmoothRep.forgetToModule M) :=
    preservesColimits_of_natIso e.symm
  exact preservesColimits_of_reflects_of_preserves _ (SmoothRep.forgetToModule M)

end UnnormalizedParabolic

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.1.1: unnormalized Frobenius reciprocity on the actual Levi points. -/
theorem leviUnnormalizedFrobeniusReciprocity :
    LeviUnnormalizedFrobeniusReciprocityStatement.{u, v, w} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  dsimp only
  intro π σ
  exact ⟨(UnnormalizedParabolic.equiv
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul) π
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)).trans
    (intertwiningPullbackEquiv (leviPointsEquiv p l hp hl) _ σ.representation),
    fun _ _ => rfl⟩

/-- Renard VI.1.1: the two unnormalized functors preserve actual short exact sequences. -/
theorem leviUnnormalizedFunctorsExact : LeviUnnormalizedFunctorsExactStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  refine ⟨fun f g hfg => ?_, fun f g hfg => ?_⟩
  · have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have := hG.smooth
    have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
    have hcof := Plancherel.rationalPoint_compactOpenCofinal k G
    have hsm (X : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
        IsSmooth ((SmoothRep.pullback (leviPointsEquiv p l hp hl).symm X).representation.comp
          h.projection) :=
      isSmooth_comp h.projection (continuous_projection_pointImage p l r hp hl hr hmul)
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm X).isSmooth
    refine ⟨Induction.smoothInducedMap_injective (pointImage p) _ hfg.1, ?_,
      Induction.smoothInducedMap_range_eq_ker (pointImage p) _ _ hfg.1 hfg.2.2⟩
    exact Induction.smoothInductionSurjectivity (rationalPoints G)
      (fun K => (hcof K).imp fun L hL => hL) (pointImage p)
      (isClosed_pointImage p hp.isClosedSubgroup) _ _ _ _ (hsm _) (hsm _) _ hfg.2.1
  · exact (leviParabolicFunctorsExact k G hG P M U p l r hp hl hr hmul).2 f g hfg

/-- Renard VI.1.1: Jacquet colimits and induction limits and colimits, at size v. -/
theorem leviUnnormalizedFunctorsPreserveLimits :
    LeviUnnormalizedFunctorsPreserveLimitsStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hδ := isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  have : (SmoothRep.pullbackFunctor.{u, u, v} (leviPointsEquiv p l hp hl).symm).IsEquivalence :=
    (SmoothRep.pullbackEquivalence (leviPointsEquiv p l hp hl).symm).isEquivalence_functor
  have := UnnormalizedParabolic.jacquet_preservesColimits.{u, v} h
  have := UnnormalizedParabolic.induction_preservesLimits.{u, v} h hU hδ
  have := UnnormalizedParabolic.induction_preservesColimits.{u, v} h hU hδ
    (Plancherel.rationalPoint_compactOpenCofinal k G)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
  refine ⟨?_, ?_, ?_⟩
  · change PreservesColimitsOfSize.{v, v}
      (UnnormalizedParabolic.jacquet h ⋙ SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl))
    infer_instance
  · change PreservesLimitsOfSize.{v, v}
      (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙
        UnnormalizedParabolic.induction h)
    infer_instance
  · change PreservesColimitsOfSize.{v, v}
      (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙
        UnnormalizedParabolic.induction h)
    infer_instance

/-- Renard VI.1.1 in full: adjunction, exactness and limit and colimit preservation
for the unchanged actual unnormalized parabolic functors. -/
theorem leviUnnormalizedParabolicStatements : LeviUnnormalizedParabolicStatements.{u, v, w} :=
  ⟨leviUnnormalizedFrobeniusReciprocity, leviUnnormalizedFunctorsExact,
    leviUnnormalizedFunctorsPreserveLimits⟩

end Langlands.Aubert.General.RepresentedParabolic
