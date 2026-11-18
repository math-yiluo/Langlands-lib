import Langlands.AlgebraicGeometry.DvrStableNormalization.SpecTensorSquare
import Langlands.AlgebraicGeometry.DvrStableNormalization.AffineNormalization
import Langlands.AlgebraicGeometry.DvrStableNormalization.Powers
import Langlands.CommutativeAlgebra.IntegralClosureTransfer
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof

/-! # Finiteness and geometric reducedness of the normalization model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Finiteness and geometric reducedness of the normalization of the base change `X'`, from the
corresponding properties of the integral closure for the global sections of a finite affine
cover. -/
theorem finite_geometricallyReduced_of_cover (X : Over (Spec (CommRingCat.of R)))
    [Flat X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    (hfin : letI := (globalAlgebraMap (coverOver X)).toAlgebra
      Module.Finite (R' ⊗[R] Γ((coverOver X).left, ⊤))
        (integralClosure (R' ⊗[R] Γ((coverOver X).left, ⊤))
          ((R' ⊗[R] Γ((coverOver X).left, ⊤)) ⊗[R'] FractionRing R')))
    (hred : letI := (globalAlgebraMap (coverOver X)).toAlgebra
      ∀ (F : Type u) [Field F] [Algebra R' F],
        IsReduced (F ⊗[R'] integralClosure (R' ⊗[R] Γ((coverOver X).left, ⊤))
          ((R' ⊗[R] Γ((coverOver X).left, ⊤)) ⊗[R'] FractionRing R'))) :
    IsFinite (map ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj X)).left ∧
      GeometricallyReduced
        (source ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj X)).hom := by
  have : IsAffine (coverOver X).left := isAffine_coverScheme X.left
  let := (globalAlgebraMap (coverOver X)).toAlgebra
  have hsq := isPullback_spec_tensor (coverOver X) R'
  let q := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
    Γ((coverOver X).left, ⊤) →ₐ[R] R' ⊗[R] Γ((coverOver X).left, ⊤)).toRingHom) ≫
      (coverOver X).left.isoSpec.inv
  let Z'' : Over (Spec (CommRingCat.of R')) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] Γ((coverOver X).left, ⊤)))))
  let p'' : Z''.left ⟶ pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    pullback.lift (q ≫ coverMap X.left) Z''.hom (by rw [Category.assoc]; exact hsq.w)
  have hp1 : p'' ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      q ≫ coverMap X.left := pullback.lift_fst _ _ _
  have hp2 : p'' ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Z''.hom := pullback.lift_snd _ _ _
  have sq : IsPullback q p'' (coverMap X.left)
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :=
    IsPullback.of_bot (by rw [hp2]; exact hsq) hp1.symm (IsPullback.of_hasPullback _ _)
  have : Smooth p'' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) sq inferInstance
  have : Surjective p'' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq inferInstance
  have : QuasiCompact p'' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq inferInstance
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have : IsAffine Z''.left := inferInstanceAs (IsAffine (Spec _))
  let X' := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj X
  let φ := pullback.snd (genericι X') p''
  have hp2' : p'' ≫ X'.hom = Z''.hom := hp2
  have hφr : φ.opensRange = Z''.left.basicOpen (pullSec Z'' ϖ') := by
    rw [Scheme.Hom.opensRange_pullbackSnd, opensRange_genericι X' hϖ',
      Scheme.preimage_basicOpen_top]
    congr 1
    change p''.appTop (X'.hom.appTop (sec R' ϖ')) = Z''.hom.appTop (sec R' ϖ')
    rw [← hp2', Scheme.Hom.comp_appTop]
    rfl
  let := (φ.app ⊤).hom.toAlgebra
  have hloc := isLocalization_app_of_opensRange_eq φ (pullSec Z'' ϖ') hφr (isAffineOpen_top _)
  have hres : Z''.left.presheaf.map (homOfLE le_top : (⊤ : Z''.left.Opens) ⟶ ⊤).op
      (pullSec Z'' ϖ') = globalAlgebraMap Z'' ϖ' := by
    rw [show (homOfLE le_top : (⊤ : Z''.left.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
      Z''.left.presheaf.map_id]
    rfl
  rw [hres] at hloc
  let := (globalAlgebraMap Z'').toAlgebra
  have hloc' : IsLocalization.Away (algebraMap R' Γ(Z''.left, ⊤) ϖ')
      Γ(pullback (genericι X') p'', φ ⁻¹ᵁ ⊤) := hloc
  let E : (R' ⊗[R] Γ((coverOver X).left, ⊤)) ≃ₐ[R'] Γ(Z''.left, ⊤) :=
    { (Scheme.ΓSpecIso (CommRingCat.of (R' ⊗[R] Γ((coverOver X).left, ⊤)))).symm.commRingCatIsoToRingEquiv with
      commutes' := fun s => by
        have := congrArg (fun h => h s) (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] Γ((coverOver X).left, ⊤)))))
        exact this }
  have hK' := isLocalizationAway_fractionRing_of_dvr R' (FractionRing R') hϖ'
  have hL1 : IsLocalization.Away (algebraMap R' (R' ⊗[R] Γ((coverOver X).left, ⊤)) ϖ')
      ((R' ⊗[R] Γ((coverOver X).left, ⊤)) ⊗[R'] FractionRing R') :=
    IsLocalization.Away.tensor ..
  let : Algebra R' (integralClosure Γ(Z''.left, ⊤) Γ(pullback (genericι X') p'', φ ⁻¹ᵁ ⊤)) :=
    ((algebraMap Γ(Z''.left, ⊤) _).comp (globalAlgebraMap Z'')).toAlgebra
  obtain ⟨hfin₂, hred₂⟩ := Langlands.CommutativeAlgebra.IntegralClosureTransfer.transfer
    (L₂ := Γ(pullback (genericι X') p'', φ ⁻¹ᵁ ⊤)) (fun _ => rfl) E ϖ' hfin hred
  obtain ⟨hφfin, hφred⟩ := finite_geometricallyReduced_normalization Z'' φ hfin₂ hred₂
  have hsnd : pullback.snd (genericι X').fromNormalization p'' =
      inv ((genericι X').normalizationPullback p'') ≫ φ.fromNormalization := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.normalizationPullback_snd]
  have hlft' : LocallyOfFiniteType (pullback.snd (genericι X').fromNormalization p'') := by
    rw [hsnd]; infer_instance
  have hlft : LocallyOfFiniteType (genericι X').fromNormalization :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback _ _).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hlft'
  have hfinX : IsFinite (genericι X').fromNormalization := by
    rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
    exact ⟨inferInstance, hlft⟩
  refine ⟨hfinX, ?_⟩
  have hgr1 : GeometricallyReduced
      (pullback.fst (genericι X').fromNormalization p'' ≫
        ((genericι X').fromNormalization ≫ X'.hom)) := by
    have hq : pullback.fst (genericι X').fromNormalization p'' ≫
        ((genericι X').fromNormalization ≫ X'.hom) =
        inv ((genericι X').normalizationPullback p'') ≫ (φ.fromNormalization ≫ Z''.hom) := by
      rw [← Category.assoc, pullback.condition, Category.assoc, hp2', ← Category.assoc, hsnd,
        Category.assoc]
    rw [hq]
    have sqi : IsPullback (inv ((genericι X').normalizationPullback p''))
        (inv ((genericι X').normalizationPullback p'') ≫ (φ.fromNormalization ≫ Z''.hom))
        (φ.fromNormalization ≫ Z''.hom) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @GeometricallyReduced)
      sqi hφred
  constructor
  intro K _ y W fst snd h
  have hr1 : IsReduced (pullback (pullback.fst (genericι X').fromNormalization p'' ≫
      ((genericι X').fromNormalization ≫ X'.hom)) y) :=
    GeometricallyReduced.geometrically_isReduced (f := pullback.fst _ _ ≫ _) y
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let e := pullbackRightPullbackFstIso ((genericι X').fromNormalization ≫ X'.hom) y
    (pullback.fst (genericι X').fromNormalization p'')
  have hr2 : IsReduced (pullback (pullback.fst (genericι X').fromNormalization p'')
      (pullback.fst ((genericι X').fromNormalization ≫ X'.hom) y)) :=
    isReduced_of_isOpenImmersion e.hom
  have hr3 : IsReduced (pullback ((genericι X').fromNormalization ≫ X'.hom) y) :=
    GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
      (pullback.snd (pullback.fst (genericι X').fromNormalization p'')
        (pullback.fst ((genericι X').fromNormalization ≫ X'.hom) y))
  have hr4 : IsReduced (pullback (source X').hom y) := hr3
  exact isReduced_of_isOpenImmersion h.isoPullback.hom

end Langlands.AlgebraicGeometry.DvrStableNormalization
