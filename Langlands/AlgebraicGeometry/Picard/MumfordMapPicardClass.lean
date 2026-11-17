import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective
import Langlands.AbelianScheme.FieldMumfordFiniteLocus
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordTransport

/-! # Maps to the dual through forgotten Picard classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.MumfordPicardClass

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.Rosati

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (P : Prerequisites.{u}) {S : Scheme.{u}} (A : AbelianScheme S) (W : DualData A)

/-- The forgotten Picard class on `T ×_S A` of the family classified by a point `p` of the
dual. -/
def pointClass {T : Over S} (p : T ⟶ dualScheme A W.hasDual) :
    Langlands.AlgebraicGeometry.Picard.Group ((relativeSpace A.X.hom).obj T) :=
  RigidifiedLineBundle.forgetClasses A.X.hom (unitSection A) (unitSection_comp A) T
    (dualPointClass P.stability A W.hasDual p).val

lemma pointClass_injective (T : Over S) :
    Function.Injective (pointClass P A W (T := T)) := by
  intro p q h
  apply dualPointClass_injective P.stability A W.hasDual T
  apply Subtype.ext
  exact RigidifiedLineBundle.forgetClasses_injective _ _ _ T h

lemma pointClass_mul {T : Over S} (p q : T ⟶ (W.dual P).X) :
    pointClass P A W (p * q) = pointClass P A W p + pointClass P A W q := by
  let := picardZeroClassesCommMonoid P.preservation P.unitCoherence P.associativity
    P.comparison P.symmetry A T
  have h := (dualAbelianSchemePointMulEquiv A W.hasDual W.geometry P.preservation
    W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry T).map_mul p q
  simp only [dualAbelianSchemePointMulEquiv_apply] at h
  unfold pointClass
  rw [h]
  obtain ⟨x, hx⟩ := dualPointClass P.stability A W.hasDual p
  obtain ⟨y, hy⟩ := dualPointClass P.stability A W.hasDual q
  induction x using Quotient.inductionOn with
  | h L =>
    induction y using Quotient.inductionOn with
    | h M =>
      change RelativePicard.classOf A.X.hom T _ =
        RelativePicard.classOf A.X.hom T _ + RelativePicard.classOf A.X.hom T _
      rw [← RelativePicard.classOf_tensor]
      rfl

/-- Precomposition with a map of test objects pulls the class back along the induced map of
fibre products. -/
lemma pointClass_comp {T U : Over S} (h : T ⟶ U) (p : U ⟶ dualScheme A W.hasDual) :
    pointClass P A W (h ≫ p) =
      Langlands.AlgebraicGeometry.Picard.Group.pullback ((relativeSpace A.X.hom).map h)
        (pointClass P A W p) := by
  unfold pointClass
  rw [dualPointClass_comp]
  exact FieldMumfordFiniteLocus.forgetClasses_classesPullback A.X.hom (unitSection A)
    (unitSection_comp A) h (dualPointClass P.stability A W.hasDual p).val

/-- Postcomposition with the dual of an endomorphism `g` pulls the class back along
`T ×_S A → T ×_S A`, `(t, a) ↦ (t, g a)`. -/
lemma pointClass_dualSchemeMap (g : A ⟶ A) {T : Over S} (p : T ⟶ dualScheme A W.hasDual) :
    pointClass P A W (p ≫ dualSchemeMap homPicardZeroPullback g W.hasDual W.hasDual) =
      Langlands.AlgebraicGeometry.Picard.Group.pullback ((homFamilySpaceMap g).app T)
        (pointClass P A W p) := by
  unfold pointClass
  rw [dualPointClass_dualSchemeMap]
  obtain ⟨x, hx⟩ := dualPointClass P.stability A W.hasDual p
  induction x using Quotient.inductionOn with
  | h L =>
    change ((RigidifiedLineBundle.forget _).obj ((homFamilyPullback g T).obj L)).classOf =
      Langlands.AlgebraicGeometry.Picard.Group.pullback _
        ((RigidifiedLineBundle.forget _).obj L).classOf
    rw [Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf]
    exact (LineBundle.classOf_eq_iff_iso _ _).2
      ⟨(RigidifiedLineBundle.pullbackForgetIso _ _ _).app L⟩

/-- The class of the actual Mumford map of a presented line bundle is the class of its
normalized Mumford family. -/
lemma pointClass_mumfordSchemeMapOfLineBundle (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left) :
    pointClass P A W (mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M
        evaluation P.square W.hasDual) =
      ((RigidifiedLineBundle.forget _).obj
        (mumfordFamilyOfLineBundle P.preservation A L B evaluationB M evaluation)).classOf := by
  unfold pointClass
  have hv : (dualPointClass P.stability A W.hasDual (mumfordSchemeMapOfLineBundle
      P.preservation A L B evaluationB M evaluation P.square W.hasDual)).val =
      RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        (mumfordFamilyOfLineBundle P.preservation A L B evaluationB M evaluation) :=
    (RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ (poincareFamily A W.hasDual) _ _).mpr
      ⟨mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L B evaluationB M evaluation
        P.square W.hasDual⟩
  rw [hv]
  rfl

section Hom

variable {S : Scheme.{u}}

/-- The underlying morphism of a sum of homomorphisms is the pointwise product. -/
lemma hom_add_eq_mul {A B : AbelianScheme S} (a b : A ⟶ B) :
    (groupHom (a + b)).hom.hom = (groupHom a).hom.hom * (groupHom b).hom.hom := by
  rfl

/-- The underlying morphism of `n • a` is the `n`-th power of that of `a`. -/
lemma hom_nsmul_eq_pow {A B : AbelianScheme S} (a : A ⟶ B) (n : ℕ) :
    (groupHom (n • a)).hom.hom = (groupHom a).hom.hom ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ_nsmul, hom_add_eq_mul, ih, pow_succ]

end Hom

/-- The unit point classifies the trivial family. -/
lemma pointClass_one {T : Over S} :
    pointClass P A W (1 : T ⟶ (W.dual P).X) = 0 := by
  let := picardZeroClassesCommMonoid P.preservation P.unitCoherence P.associativity
    P.comparison P.symmetry A T
  have h := (dualAbelianSchemePointMulEquiv A W.hasDual W.geometry P.preservation
    W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry T).map_one
  simp only [dualAbelianSchemePointMulEquiv_apply] at h
  unfold pointClass
  rw [h]
  exact FieldMumfordFiniteLocus.forgetClasses_trivialClass A.X.hom (unitSection A)
    (unitSection_comp A) T

lemma pointClass_pow {T : Over S} (p : T ⟶ (W.dual P).X) (n : ℕ) :
    pointClass P A W (p ^ n) = n • pointClass P A W p := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact pointClass_one P A W
  | succ n ih => rw [pow_succ, pointClass_mul, ih, succ_nsmul]

section Field

variable (k : Type u) [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Over a field, the class of the ordinary Mumford family of a presented line bundle `L` is
`m^*[L] - p₁^*[L] - p₂^*[L]`. -/
lemma classOf_mumfordFamily (L : LineBundle A.X.left)
    (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left) :
    ((RigidifiedLineBundle.forget _).obj
        (mumfordFamilyOfLineBundle P.preservation A L B evaluationB M evaluation)).classOf =
      Langlands.AlgebraicGeometry.Picard.Group.pullback (mumfordAddition A) L.classOf -
        (show Langlands.AlgebraicGeometry.Picard.Group (mumfordProduct A).left from
          Langlands.AlgebraicGeometry.Picard.Group.pullback
            (pullback.fst A.X.hom A.X.hom) L.classOf) -
        (show Langlands.AlgebraicGeometry.Picard.Group (mumfordProduct A).left from
          Langlands.AlgebraicGeometry.Picard.Group.pullback
            (pullback.snd A.X.hom A.X.hom) L.classOf) := by
  have hB : B.classOf = 0 := by
    rw [← LineBundle.classOf_trivial]
    exact (LineBundle.classOf_eq_iff _ _).2 ⟨(fieldLineBundleTriviality k B).some⟩
  have hπB : ((LineBundle.pullback A.X.hom).obj B).classOf = 0 := by
    rw [← Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf, hB, map_zero]
  have hN : (LineBundle.tensor P.preservation L
      ((LineBundle.pullback A.X.hom).obj B)).classOf = L.classOf := by
    rw [LineBundle.classOf_tensor, hπB, add_zero]
  have hNM : (LineBundle.tensor P.preservation L
      ((LineBundle.pullback A.X.hom).obj B)).classOf + M.classOf = 0 := by
    rw [← LineBundle.classOf_tensor P.preservation, ← LineBundle.classOf_trivial A.X.left]
    exact (LineBundle.classOf_eq_iff _ _).2 ⟨evaluation⟩
  rw [hN] at hNM
  have hM : M.classOf = -L.classOf := eq_neg_of_add_eq_zero_right hNM
  rw [mumfordFamilyOfLineBundle_forget, LineBundle.classOf_tensor, LineBundle.classOf_tensor,
    ← Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf,
    ← Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf,
    ← Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf, hN, hM,
    map_neg, map_neg, sub_eq_add_neg, sub_eq_add_neg]
  rfl

/-- The map `(t, a) ↦ (g t, g a)` of `A ×_S A` used by the two pullbacks is the product map. -/
lemma homFamilySpaceMap_comp_relativeSpace_map (g : A ⟶ A) :
    (homFamilySpaceMap g).app A.X ≫ (relativeSpace A.X.hom).map (groupHom g).hom.hom =
      mumfordProductMap g := by
  apply pullback.hom_ext
  · simp [homFamilySpaceMap, relativeSpace, mumfordProductMap, Over.pullback]
  · simp [homFamilySpaceMap, relativeSpace, mumfordProductMap, Over.pullback]

set_option synthInstance.maxHeartbeats 1000000 in
/-- Pulling back along the two maps induced by `g` and then along `r` is pulling back along
`g` and then along `r`, whenever `r` commutes with the product map of `g`. -/
lemma pullback_twice (g : A ⟶ A) (r : (mumfordProduct A).left ⟶ A.X.left)
    (hr : mumfordProductMap g ≫ r = r ≫ hom g)
    (x : Langlands.AlgebraicGeometry.Picard.Group A.X.left) :
    Langlands.AlgebraicGeometry.Picard.Group.pullback ((homFamilySpaceMap g).app A.X)
        (Langlands.AlgebraicGeometry.Picard.Group.pullback
          ((relativeSpace A.X.hom).map (groupHom g).hom.hom)
          (Langlands.AlgebraicGeometry.Picard.Group.pullback r x)) =
      Langlands.AlgebraicGeometry.Picard.Group.pullback r
        (Langlands.AlgebraicGeometry.Picard.Group.pullback (hom g) x) := by
  calc _ = Langlands.AlgebraicGeometry.Picard.Group.pullback ((homFamilySpaceMap g).app A.X ≫
          (relativeSpace A.X.hom).map (groupHom g).hom.hom ≫ r) x := by
        rw [Langlands.AlgebraicGeometry.Picard.Group.pullback_comp,
          Langlands.AlgebraicGeometry.Picard.Group.pullback_comp]
        rfl
    _ = Langlands.AlgebraicGeometry.Picard.Group.pullback (mumfordProductMap g ≫ r) x := by
        rw [← Category.assoc, homFamilySpaceMap_comp_relativeSpace_map]
        rfl
    _ = Langlands.AlgebraicGeometry.Picard.Group.pullback (r ≫ hom g) x := by rw [hr]
    _ = _ := by
        rw [Langlands.AlgebraicGeometry.Picard.Group.pullback_comp]
        rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The class of `g ≫ φ_L ≫ g^∨` is the Mumford class of `g^*L`. -/
lemma pointClass_comp_mumford_comp_dual (g : A ⟶ A) (L : LineBundle A.X.left)
    (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (W : DualData A) :
    pointClass P A W ((groupHom g).hom.hom ≫ mumfordSchemeMapOfLineBundle P.preservation A L B
        evaluationB M evaluation P.square W.hasDual ≫
        dualSchemeMap homPicardZeroPullback g W.hasDual W.hasDual) =
      Langlands.AlgebraicGeometry.Picard.Group.pullback (mumfordAddition A)
          ((LineBundle.pullback (hom g)).obj L).classOf -
        (show Langlands.AlgebraicGeometry.Picard.Group (mumfordProduct A).left from
          Langlands.AlgebraicGeometry.Picard.Group.pullback
            (pullback.fst A.X.hom A.X.hom) ((LineBundle.pullback (hom g)).obj L).classOf) -
        (show Langlands.AlgebraicGeometry.Picard.Group (mumfordProduct A).left from
          Langlands.AlgebraicGeometry.Picard.Group.pullback
            (pullback.snd A.X.hom A.X.hom) ((LineBundle.pullback (hom g)).obj L).classOf) := by
  rw [← Category.assoc, pointClass_dualSchemeMap, pointClass_comp,
    pointClass_mumfordSchemeMapOfLineBundle, classOf_mumfordFamily P k A]
  simp only [map_sub]
  rw [← Langlands.AlgebraicGeometry.Picard.Group.pullback_lineBundle_classOf,
    pullback_twice k A g _ (mumfordProductMap_addition g)]
  erw [pullback_twice k A g _ (mumfordProductMap_fst g),
    pullback_twice k A g _ (mumfordProductMap_snd g)]
  rfl

end Field

end Langlands.AbelianScheme.MumfordPicardClass
