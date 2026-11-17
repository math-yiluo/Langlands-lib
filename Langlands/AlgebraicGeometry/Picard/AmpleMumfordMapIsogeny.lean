import Langlands.GroupScheme.AlgClosedFiniteKernelHomIsogeny
import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof
import Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AbelianScheme.IsogenySpecialization

/-! # The Mumford homomorphism of an ample line bundle is an isogeny -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.AmpleMumfordIsogeny

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules TranslationStabilizer
open Langlands.AbelianScheme.Rosati

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (P : Prerequisites.{u}) (k : Type u) [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  (W : DualData A) (ψ : A ⟶ W.dual P)

/-- An explicit ample Mumford presentation of `ψ`: an ample line bundle `L` on `A`,
unit-section normalization data `B`, `evaluationB`, an inverse `M` of the normalized bundle with
its evaluation isomorphism, and the equation identifying the underlying scheme morphism of `ψ`
with the actual Mumford map `mumfordSchemeMapOfLineBundle` of these data. These are the
presentation hypotheses of the Library's `MumfordMixedEulerTraceStatement`. -/
structure AmpleMumfordPresentation where
  /-- The ample line bundle. -/
  L : LineBundle A.X.left
  /-- The line bundle on the base used to normalize `L` along the unit section. -/
  B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
  /-- The normalization isomorphism `e^*L ⊗ B ≅ O`. -/
  evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
    B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
  /-- An inverse of the normalized bundle. -/
  M : LineBundle A.X.left
  /-- The evaluation isomorphism `N ⊗ M ≅ O_A` for the normalized bundle `N`. -/
  evaluation : tensorObj
    (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left
  /-- `L` is ample. -/
  isAmple : L.IsAmple
  /-- The underlying scheme morphism of `ψ` is the Mumford map of these data. -/
  hom_eq : (groupHom ψ).hom.hom =
    mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
      P.square W.hasDual

variable (L : LineBundle A.X.left)
  (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
    B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  (M : LineBundle A.X.left)
  (evaluation : tensorObj
    (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅
        structureSheaf A.X.left)

set_option maxHeartbeats 1600000 in
/-- The scheme-theoretic kernel of a homomorphism whose underlying map is the Mumford map of
an ample line bundle is finite over the field. -/
theorem isFinite_kernel (hL : L.IsAmple)
    (hψ : (groupHom ψ).hom.hom =
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual) :
    IsFinite (GroupScheme.kernel (groupHom ψ)).X.hom := by
  let N := LineBundle.normalize P.preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB
  let Z := (GroupScheme.kernel (groupHom ψ)).X.left
  let j : Z ⟶ A.X.left := (GroupScheme.kernelι (groupHom ψ)).hom.hom.left
  have hj : IsClosedImmersion j := by
    change IsClosedImmersion (GroupScheme.kernelι (groupHom ψ)).hom.hom.left
    infer_instance
  have hjw : j ≫ A.X.hom = (GroupScheme.kernel (groupHom ψ)).X.hom :=
    Over.w (GroupScheme.kernelι (groupHom ψ)).hom.hom
  -- the tautological point of the kernel is sent to the unit of the dual
  let e : testObject A j ⟶ (GroupScheme.kernel (groupHom ψ)).X :=
    Over.homMk (𝟙 Z) (by simp [hjw])
  have ht : tautological A j = e ≫ (GroupScheme.kernelι (groupHom ψ)).hom.hom := by
    ext
    simp [tautological, e, j]
  have hone : tautological A j ≫ (groupHom ψ).hom.hom = 1 := by
    rw [ht, Category.assoc, (GroupScheme.kernel_isPullback (groupHom ψ)).w,
      ← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]
    rfl
  -- the Mumford family is trivial along the tautological point
  have hpts := mumfordSchemeMapOfLineBundle_points P.preservation A L B evaluationB M evaluation
    P.square W.hasDual (testObject A j) (tautological A j)
  rw [← hψ, hone] at hpts
  let := picardZeroClassesCommMonoid P.preservation P.unitCoherence P.associativity
    P.comparison P.symmetry A (testObject A j)
  have h1 := congrArg Subtype.val ((dualAbelianSchemePointMulEquiv A W.hasDual W.geometry
    P.preservation W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry (testObject A j)).map_one)
  have hcls := hpts.symm.trans h1
  obtain ⟨E₀⟩ := Quotient.exact hcls
  let E : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (tautological A j)).obj (mumfordBundle A P.preservation N M evaluation) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (tautological A j)).obj (RigidifiedLineBundle.trivial _) :=
    E₀ ≪≫ (RigidifiedLineBundle.pullbackTrivialIso _ _ _).symm
  let anti := antidiagonalTrivialization A j P.preservation N M evaluation E
  -- Picard-group bookkeeping: the inverse `M` of `N` is trivial on the antidiagonal, hence so is
  -- `N` itself
  let ι' : A.X.left ⟶ A.X.left := (inversion A).left
  let Nl : LineBundle A.X.left := (RigidifiedLineBundle.forget (unitSection A)).obj N
  have hNM : Nl.classOf + M.classOf = 0 := by
    rw [← LineBundle.classOf_tensor P.preservation, ← LineBundle.classOf_trivial A.X.left]
    exact (LineBundle.classOf_eq_iff _ _).mpr ⟨evaluation⟩
  have hZM : ((LineBundle.pullback j).obj M).classOf +
      ((LineBundle.pullback (j ≫ ι')).obj M).classOf = 0 := by
    rw [← LineBundle.classOf_tensor P.preservation, ← LineBundle.classOf_trivial Z]
    exact (LineBundle.classOf_eq_iff _ _).mpr ⟨anti⟩
  let T₀ : LineBundle Z := LineBundle.tensor P.preservation
    ((LineBundle.pullback j).obj Nl) ((LineBundle.pullback (j ≫ ι')).obj Nl)
  have hT₀ : T₀.classOf = (LineBundle.trivial Z).classOf := by
    have hN : Nl.classOf = -M.classOf := eq_neg_of_add_eq_zero_left hNM
    have hjN : ((LineBundle.pullback j).obj Nl).classOf =
        -((LineBundle.pullback j).obj M).classOf := by
      rw [← Group.pullback_lineBundle_classOf, ← Group.pullback_lineBundle_classOf, hN,
        map_neg]
    have hiN : ((LineBundle.pullback (j ≫ ι')).obj Nl).classOf =
        -((LineBundle.pullback (j ≫ ι')).obj M).classOf := by
      rw [← Group.pullback_lineBundle_classOf, ← Group.pullback_lineBundle_classOf, hN,
        map_neg]
    have hsum : T₀.classOf = ((LineBundle.pullback j).obj Nl).classOf +
        ((LineBundle.pullback (j ≫ ι')).obj Nl).classOf :=
      LineBundle.classOf_tensor P.preservation _ _
    rw [hsum, hjN, hiN, LineBundle.classOf_trivial, ← neg_add, hZM, neg_zero]
  have hNl : Nl.IsAmple :=
    ampleIso _ L Nl ⟨(nonempty_normalize_carrier_iso P.preservation k A L B evaluationB).some.symm⟩ hL
  have : IsIso ι' := inferInstanceAs (IsIso (inversion A).left)
  have h₁ := closedImmersionPullbackAmple _ _ j Nl hj hNl
  have h₂ := closedImmersionPullbackAmple _ _ (j ≫ ι') Nl inferInstance hNl
  have hT : T₀.IsAmple := ampleTensor Z _ _ _ ⟨Iso.refl _⟩ h₁ h₂
  have hfin : IsFinite (j ≫ A.X.hom) :=
    properAmpleTrivialFinite k Z (j ≫ A.X.hom) T₀ inferInstance hT
      ((LineBundle.classOf_eq_iff _ _).mp hT₀)
  rw [← hjw]
  exact hfin

/-- Over an algebraically closed field, a homomorphism to the dual whose underlying map is the
Mumford map of an ample line bundle is an isogeny: finite, flat and surjective. -/
theorem isIsogeny [IsAlgClosed k] (hL : L.IsAmple)
    (hψ : (groupHom ψ).hom.hom =
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual) :
    IsIsogeny ψ := by
  have hk := isFinite_kernel P k A W ψ L B evaluationB M evaluation hL hψ
  have hfin : IsFinite (groupHom ψ).hom.hom.left :=
    GroupScheme.HomIsogeny.isFinite_of_finite_kernel (groupHom ψ)
  have hsurj : Surjective (groupHom ψ).hom.hom.left := by
    have hmap : (groupHom ψ).hom.hom.left =
        (mumfordSchemeMap P.preservation P.square A
          (LineBundle.normalize P.preservation A.X.hom (unitSection A)
            (unitSection_comp A) L B evaluationB) M evaluation W.hasDual).left := by
      rw [hψ]
      rfl
    rw [hmap] at hfin ⊢
    exact ⟨fieldFiniteMumfordMapSurjective P.preservation P.square k A W.hasDual _ M
      evaluation hfin⟩
  exact GroupScheme.HomIsogeny.isIsogeny_of_finite_kernel_of_surjective (groupHom ψ)
    inferInstance inferInstance inferInstance inferInstance hk hsurj

variable {P k A W ψ} in
/-- A homomorphism with an ample Mumford presentation over an algebraically closed field is an
isogeny. -/
theorem AmpleMumfordPresentation.isIsogeny [IsAlgClosed k]
    (h : AmpleMumfordPresentation P k A W ψ) : IsIsogeny ψ :=
  AmpleMumfordIsogeny.isIsogeny P k A W ψ h.L h.B h.evaluationB h.M h.evaluation h.isAmple
    h.hom_eq

end Langlands.AbelianScheme.AmpleMumfordIsogeny
