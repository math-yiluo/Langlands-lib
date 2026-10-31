import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionReductionStatement
import Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingStatement
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Valuative extension of rigidified Picard-zero classes, conditionally

The theorem `picardZeroValuativeExtension_of_prerequisites` proves
`PicardZeroValuativeExtensionStatement` from four focused propositions:
translation-difference lifting over algebraically closed fields, ample existence over
algebraically closed fields, the Picard-zero property of the actual Mumford family, and
ample extension from the generic fibre over a valuation ring. Over an algebraic closure
`K'` of `K` and a dominating valuation ring `R'`, the given class is compared with the
pullback of the rigidified Mumford family of a normalized line bundle along a section
extended by the valuative criterion. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-- The rigidified Mumford comparison at a field-valued point of an arbitrary base. -/
theorem mumfordPointComparison
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.obj.carrier M.obj ≅
      Langlands.Scheme.Modules.structureSheaf A.X.left)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk b ⟶ A.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange b).obj A).X)
    (hx : x.left ≫ pullback.fst A.X.hom b = a.left)
    (Q : RigidifiedFamily A (Over.mk b))
    (premise : LineBundle.tensor preservation
          ((LineBundle.pullback
            (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
              ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
                ((RigidifiedLineBundle.forget (unitSection A)).obj L)))
          ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M) ≅
        familyLineBundle A (T := Over.mk b) Q) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) (T := Over.mk b) a).obj
          (mumfordBundle A preservation L M evaluation) ≅ Q) :=
  ⟨RigidifiedLineBundle.isoOfCarrierIso preservation
    ((relativeProjection A.X.hom).app (Over.mk b))
    (relativeSection_projection _ _ _ _)
    (FieldMumfordPoint.carrierIso A a preservation x hx L.obj.carrier M.obj Q.obj.carrier
      (fieldLineBundleTriviality K ((LineBundle.pullback a.left).obj M)).some
      ((LineBundle.forget _).mapIso premise))⟩

open Langlands.AbelianScheme.MumfordPicardZero (pullbackTensorIso pullbackCompIso tensorIsoOf) in
/-- Normalizing a line bundle along the unit section keeps the restriction to a
field-valued fibre ample: the added factor is pulled back from the spectrum of a field. -/
theorem isAmple_fibre_normalize
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) (K : Type u) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (M : LineBundle A.X.left) (B : LineBundle S)
    (evaluation : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj M.obj) B.obj ≅
      structureSheaf S)
    (hM : ((LineBundle.pullback (pullback.fst A.X.hom t)).obj M).IsAmple) :
    ((LineBundle.pullback (pullback.fst A.X.hom t)).obj
      ((RigidifiedLineBundle.forget _).obj
        (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
          M B evaluation))).IsAmple := by
  let i := pullback.fst A.X.hom t
  let j := pullback.snd A.X.hom t
  let triv := (fieldLineBundleTriviality K ((LineBundle.pullback t).obj B)).some
  refine hM.of_iso ?_
  exact (pullbackTensorIso preservation i M.obj ((Scheme.Modules.pullback A.X.hom).obj B.obj) ≪≫
    tensorIsoOf (Iso.refl _)
      ((pullbackCompIso i A.X.hom (i ≫ A.X.hom) rfl B.obj).symm ≪≫
        pullbackCompIso j t (i ≫ A.X.hom) pullback.condition.symm B.obj ≪≫
        (Scheme.Modules.pullback j).mapIso triv ≪≫ pullbackUnitIso j) ≪≫
    tensorRightUnitor _).symm

/-- A point of the generic fibre of an abelian scheme over a valuation ring extends to a
section over the valuation ring, by the valuative criterion for the proper structure map.
The generic point is a variable `t` equal to the actual morphism. -/
theorem exists_section_extending
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (ht : Spec.map (CommRingCat.ofHom (algebraMap R K)) = t)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange t).obj A).X) :
    ∃ x' : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ A.X,
      t ≫ x'.left = x.left ≫ pullback.fst A.X.hom t := by
  subst ht
  have hE : ValuativeCriterion.Existence A.X.hom := by
    have h : UniversallyClosed A.X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hx : x.left ≫ pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      𝟙 _ := Over.w x
  let sq : ValuativeCommSq A.X.hom :=
    { R := R, K := K
      i₁ := x.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      i₂ := 𝟙 _
      commSq := ⟨by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
        exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hE sq
  exact ⟨Over.homMk l (by simpa using hl₂), hl₁⟩

/-- Over a valuation ring with algebraically closed fraction field, some line bundle on an
abelian scheme has ample restriction to the generic fibre, by ample existence over the
fraction field and the ample extension proposition. -/
theorem exists_ample_generic
    (h2 : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (h4 : ValuationRingAmpleExtensionStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (ht : Spec.map (CommRingCat.ofHom (algebraMap R K)) = t) :
    ∃ M : LineBundle A.X.left,
      ((LineBundle.pullback (pullback.fst A.X.hom t)).obj M).IsAmple := by
  subst ht
  obtain ⟨L₀, hL₀⟩ := h2 K ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).toGrp
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).smooth
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).proper
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).geometricallyConnected
  exact h4 R K A ⟨L₀, hL₀⟩


open Langlands.SchemeModule in
/-- The extension step over a valuation ring with algebraically closed fraction field,
assuming the four focused prerequisite propositions. -/
theorem exists_picardZero_extension_of_isAlgClosed
    (h1 : AlgClosedFieldTranslationDifferenceLiftingStatement.{u})
    (h2 : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (h3 : MumfordBundlePicardZeroStatement.{u})
    (h4 : ValuationRingAmpleExtensionStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    (b : Spec (CommRingCat.of R) ⟶ S) (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (ht : Spec.map (CommRingCat.ofHom (algebraMap R K)) = t)
    (p : PicardZeroClasses A (Over.mk (t ≫ b))) :
    ∃ q' : PicardZeroClasses A (Over.mk b),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (Over.homMk t rfl : Over.mk (t ≫ b) ⟶ Over.mk b) q'.val = p.val := by
  have coherence := RigidifiedModule.pullbackCoherence.{u}
  have preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    @Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
  let A' := (baseChange b).obj A
  obtain ⟨M, hM⟩ := exists_ample_generic h2 h4 R K A' t ht
  obtain ⟨B, ⟨evB⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection A')).obj M)
  let Lr := LineBundle.normalize preservation A'.X.hom (unitSection A') (unitSection_comp A')
    M B evB
  obtain ⟨M₀, ⟨ev₀⟩⟩ :=
    LineBundle.exists_tensorObj_iso_structureSheaf ((RigidifiedLineBundle.forget _).obj Lr)
  have hamp := isAmple_fibre_normalize preservation A' K t M B evB hM
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep p.val
  have hPQ : IsPicardZeroFamily A Q := by
    have h := p.property
    rw [← hQ] at h
    exact h
  let T : Over (Spec (CommRingCat.of R)) := Over.mk t
  let U : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let F := familyBaseChange b A T
  let G := familyBaseChangeInverse b A T
  let Q' := F.obj Q
  have hPQ' : IsPicardZeroFamily A' Q' := (picardZeroFamilyBaseChange S _ b A T Q).mp hPQ
  have hP := isTranslationInvariant_of_isGeometricallyPicardZero K ((baseChange t).obj A') hPQ'
  let i := pullback.fst A'.X.hom t
  let L1 : LineBundle ((baseChange t).obj A').X.left :=
    (LineBundle.pullback i).obj ((RigidifiedLineBundle.forget _).obj Lr)
  let N1 : LineBundle ((baseChange t).obj A').X.left := (LineBundle.pullback i).obj M₀
  let ev1 : tensorObj L1.obj N1.obj ≅ structureSheaf ((baseChange t).obj A').X.left :=
    Langlands.Scheme.Modules.pullbackTensorEvaluation preservation i _ _ ev₀
  let P1 : LineBundle ((baseChange t).obj A').X.left := familyLineBundle A' (T := T) Q'
  have hamp1 : L1.IsAmple := hamp
  have hP1 : GroupScheme.IsTranslationInvariant ((baseChange t).obj A').toGrp P1 := hP
  obtain ⟨x, ⟨ex⟩⟩ := h1 preservation K ((baseChange t).obj A') L1 N1 ev1 P1 hamp1 hP1
  obtain ⟨x', hx'⟩ := exists_section_extending A' t ht x
  let g : T ⟶ U := Over.homMk t (Category.comp_id t)
  obtain ⟨cmp⟩ := mumfordPointComparison preservation A' Lr M₀ ev₀ K t (g ≫ x') x hx'.symm
    Q' ex
  let Φ := mumfordBundle A' preservation Lr M₀ ev₀
  have hΦ : IsPicardZeroFamily A' Φ := h3 preservation _ A' Lr M₀ ev₀
  let Ψ' := (RigidifiedLineBundle.relativePullback A'.X.hom (unitSection A')
    (unitSection_comp A') x').obj Φ
  have hΨ' : IsPicardZeroFamily A' Ψ' := picardZeroPullback _ A' _ _ x' Φ hΦ
  let Ψ₀ := (familyBaseChangeInverse b A U).obj Ψ'
  have hΨ₀ : IsPicardZeroFamily A Ψ₀ := (picardZeroFamilyBaseChange S _ b A U Ψ₀).mpr
    ((isPicardZeroFamily_iff_of_iso _ ((familyBaseChangeCounitIso b A U).app Ψ')).mpr hΨ')
  let k : Over.mk b ⟶ (Over.map b).obj U := Over.homMk (𝟙 _) (by simp [U])
  let Ψ := (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    k).obj Ψ₀
  have hΨ : IsPicardZeroFamily A Ψ := picardZeroPullback S A _ _ k Ψ₀ hΨ₀
  refine ⟨⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) Ψ, hΨ⟩,
    ?_⟩
  rw [← hQ]
  let h₁ : Over.mk (t ≫ b) ⟶ Over.mk b := Over.homMk t rfl
  have hk : h₁ ≫ k = (Over.map b).map g := by
    ext
    simp [h₁, k, g]
  let e : F.obj ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) h₁).obj Ψ) ≅ F.obj Q :=
    F.mapIso ((RigidifiedLineBundle.relativePullbackComp coherence A.X.hom (unitSection A)
        (unitSection_comp A) h₁ k).app Ψ₀ ≪≫ eqToIso (by rw [hk])) ≪≫
      (familyBaseChangeNaturality b A g).app Ψ₀ ≪≫
      (RigidifiedLineBundle.relativePullback A'.X.hom (unitSection A') (unitSection_comp A')
        g).mapIso ((familyBaseChangeCounitIso b A U).app Ψ') ≪≫
      (RigidifiedLineBundle.relativePullbackComp coherence A'.X.hom (unitSection A')
        (unitSection_comp A') g x').app Φ ≪≫
      cmp
  exact Quotient.sound ⟨((familyBaseChangeUnitIso b A T).app _).symm ≪≫ G.mapIso e ≪≫
    (familyBaseChangeUnitIso b A T).app Q⟩

/-- An algebraic closure `K'` of `K` and a valuation subring `R'` of `K'` dominating `R`,
with the types in the input universe. -/
theorem exists_algClosed_valuation_domination
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (K' : Type u) (_ : Field K') (_ : IsAlgClosed K')
      (_ : Algebra R' K') (_ : IsFractionRing R' K')
      (φ : R →+* R') (_ : IsLocalHom φ) (ψ : K →+* K'),
      (algebraMap R' K').comp φ = ψ.comp (algebraMap R K) := by
  let f : R →+* AlgebraicClosure K :=
    (algebraMap K (AlgebraicClosure K)).comp (algebraMap R K)
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  exact ⟨V, inferInstance, inferInstance, inferInstance, AlgebraicClosure K,
    inferInstance, inferInstance, inferInstance, inferInstance,
    f.codRestrict V.toSubring hV, hlocal, algebraMap K (AlgebraicClosure K), rfl⟩

/-- Pulling back a class satisfying the geometric Picard-zero condition keeps the condition. -/
theorem isPicardZeroClass_classesPullback {S : Scheme.{u}} (A : AbelianScheme S)
    {T U : Over S} (h : T ⟶ U) (r : PicardZeroClasses A U) :
    IsPicardZeroClass A
      (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
        r.val) := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep r.val
  have hr := r.property
  rw [← hQ] at hr ⊢
  exact picardZeroPullback S A T U h Q hr

/-- The extension step with the generic point of the target written as a variable `c`. -/
theorem exists_picardZero_extension_of_isAlgClosed'
    (h1 : AlgClosedFieldTranslationDifferenceLiftingStatement.{u})
    (h2 : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (h3 : MumfordBundlePicardZeroStatement.{u})
    (h4 : ValuationRingAmpleExtensionStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    (b : Spec (CommRingCat.of R) ⟶ S) (c : Spec (CommRingCat.of K) ⟶ S)
    (hc : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b = c)
    (p : PicardZeroClasses A (Over.mk c)) :
    ∃ q' : PicardZeroClasses A (Over.mk b),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) hc :
            Over.mk c ⟶ Over.mk b) q'.val = p.val := by
  subst hc
  exact exists_picardZero_extension_of_isAlgClosed h1 h2 h3 h4 A R K b _ rfl p

/-- The target proposition, conditional on the four focused prerequisite propositions:
translation-difference lifting and ample existence over algebraically closed fields,
the Picard-zero property of the Mumford family, and ample extension from the generic
fibre over a valuation ring. -/
theorem picardZeroValuativeExtension_of_prerequisites
    (h1 : AlgClosedFieldTranslationDifferenceLiftingStatement.{u})
    (h2 : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (h3 : MumfordBundlePicardZeroStatement.{u})
    (h4 : ValuationRingAmpleExtensionStatement.{u}) :
    PicardZeroValuativeExtensionStatement.{u} := by
  intro S _ A R _ _ _ K _ _ _ i₂ q
  obtain ⟨R', _, _, _, K', _, _, _, _, φ, hφ, ψ, hφψ⟩ :=
    exists_algClosed_valuation_domination R K
  let h₂ : Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ)) rfl
  let p : PicardZeroClasses A (Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂)) :=
    ⟨RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h₂ q.val,
      isPicardZeroClass_classesPullback A h₂ q⟩
  have hc : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
      (Spec.map (CommRingCat.ofHom φ) ≫ i₂) =
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ]
  obtain ⟨q', hq'⟩ := exists_picardZero_extension_of_isAlgClosed' h1 h2 h3 h4 A R' K'
    (Spec.map (CommRingCat.ofHom φ) ≫ i₂) _ hc p
  refine ⟨R', inferInstance, inferInstance, inferInstance, K', inferInstance, inferInstance,
    inferInstance, φ, hφ, ψ, hφψ, q', ?_⟩
  exact hq'

/-- The reduction proposition `PicardZeroValuativeExtensionReductionStatement` holds. -/
theorem picardZeroValuativeExtensionReduction :
    PicardZeroValuativeExtensionReductionStatement.{u} :=
  fun h1 h2 h3 h4 => picardZeroValuativeExtension_of_prerequisites h1 h2 h3 h4

end Langlands.AbelianScheme
