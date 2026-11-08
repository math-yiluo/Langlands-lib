import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement
import Langlands.AlgebraicGeometry.Picard.MumfordProductEulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.MumfordSecondProjectionSupport
import Langlands.AlgebraicGeometry.Picard.MumfordProductMultiplicationTwist
import Langlands.AlgebraicGeometry.Modules.FiniteFlatBaseChangeEuler
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.MultiplicationDegree
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingCoprimeExtension

/-! # The `k^(2g)` scaling of the Euler product from the cube and square statements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.ScalingAssembly

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AbelianScheme.MultiplicationTwist

section Square

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Multiplication by `k` on the abelian scheme, as a morphism over the base. -/
abbrev mulK (k : ℕ) : A.X ⟶ A.X := (Langlands.GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom

/-- The endomorphism `1 × [k]` of the self-product `A ×_K A`. -/
def mulOnSecond (k : ℕ) : mumfordProduct A ⟶ mumfordProduct A :=
  mumfordProductLift A (mumfordFirst A) (mumfordSecond A ^ k)

lemma mulOnSecond_first (k : ℕ) : mulOnSecond A k ≫ mumfordFirst A = mumfordFirst A :=
  mumfordProductLift_first A _ _

lemma mulOnSecond_second (k : ℕ) : mulOnSecond A k ≫ mumfordSecond A = mumfordSecond A ^ k :=
  mumfordProductLift_second A _ _

lemma second_comp_mulK (k : ℕ) : mumfordSecond A ≫ mulK A k = mumfordSecond A ^ k := by
  rw [Langlands.GroupScheme.points_multiplication, zpow_natCast]

/-- `1 × [k]` is the base change of `[k]` along the second projection. -/
lemma isPullback_mulOnSecond (k : ℕ) :
    IsPullback (mulOnSecond A k).left (pullback.snd A.X.hom A.X.hom)
      (pullback.snd A.X.hom A.X.hom) (mulK A k).left := by
  have hp : (mulOnSecond A k).left ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd A.X.hom A.X.hom ≫ (mulK A k).left := by
    have h := congrArg CommaMorphism.left (mulOnSecond_second A k)
    rw [← second_comp_mulK A k] at h
    exact h
  have hf : (mulOnSecond A k).left ≫ pullback.fst A.X.hom A.X.hom =
      pullback.fst A.X.hom A.X.hom :=
    congrArg CommaMorphism.left (mulOnSecond_first A k)
  have hm : (mulK A k).left ≫ A.X.hom = A.X.hom := Over.w (mulK A k)
  refine IsPullback.of_right ?_ hp (IsPullback.of_hasPullback A.X.hom A.X.hom)
  rw [hf, hm]
  exact IsPullback.of_hasPullback A.X.hom A.X.hom

end Square

section Main

/-- A line bundle has free charts of rank one. -/
lemma exists_freeChart_one {X : Scheme.{u}} (L : LineBundle X) (y : X) :
    ∃ V : X.Opens, y ∈ V ∧ Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj L.obj ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) := by
  obtain ⟨V, hy, ⟨e⟩⟩ := L.property y
  exact ⟨V, hy, ⟨e ≪≫ (coproductUniqueIso
    (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit V.toScheme.ringCatSheaf)).symm⟩⟩

/-- Euler characteristics along equal structure morphisms agree. -/
lemma eulerCharacteristic_congr_hom {K : Type u} [Field K] {X : Scheme.{u}}
    {f f' : X ⟶ Spec (CommRingCat.of K)} (h : f = f') (M : X.Modules)
    (hM : HasFiniteCohomology f M) (hM' : HasFiniteCohomology f' M) :
    eulerCharacteristic f M hM = eulerCharacteristic f' M hM' := by
  subst h
  rfl

/-- **Conditional assembly.** For `k` nonzero in `K`, the `k^(2g)` scaling of the Euler
product follows from the balanced cube identity and the theorem of the square. -/
theorem algClosedFieldAmpleEulerInverseScaling_of_ne_zero
    (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (square : Langlands.GroupScheme.FieldTheoremOfTheSquareStatement.{u}) :
    AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement.{u} := by
  intro K _ _ A g hg H N hH ⟨eN⟩ k hk hkK Nk ⟨eNk⟩ hH' hN' hHk hNk
  let q := pullback.snd A.X.hom A.X.hom
  have hqs : q ≫ A.X.hom = (mumfordProduct A).hom := pullback.condition.symm
  let Z := (mumfordProduct A).left
  let Hk : LineBundle A.X.left := powLB H k
  let Q0 : LineBundle Z := ⟨twistedProduct A H.obj N.obj,
    IsLocallyFreeRankOne.tensor pullbackTensorComparisonIsIso (H.property.pullback _)
      (N.property.pullback _)⟩
  let Q1 : LineBundle Z := ⟨twistedProduct A Hk.obj Nk.obj,
    IsLocallyFreeRankOne.tensor pullbackTensorComparisonIsIso (Hk.property.pullback _)
      (Nk.property.pullback _)⟩
  let E : LineBundle A.X.left := ⟨multiplicationTwist A H Nk k,
    IsLocallyFreeRankOne.tensor pullbackTensorComparisonIsIso (H.property.pullback _)
      Nk.property⟩
  have hsm : Smooth (mumfordProduct A).hom :=
    inferInstanceAs (Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom))
  have hpr : IsProper (mumfordProduct A).hom :=
    inferInstanceAs (IsProper (pullback.fst A.X.hom A.X.hom ≫ A.X.hom))
  have fin : ∀ L : LineBundle Z, HasFiniteCohomology (q ≫ A.X.hom) L.obj := fun L => by
    rw [hqs]
    exact smoothProperLineBundleFiniteCohomology K Z _ hsm hpr L
  have hHkA : Hk.IsAmple := positiveTensorPowerAmple _ H Hk k (by omega) hH ⟨Iso.refl _⟩
  have supp0 := hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst A square
    H N hH eN
  have supp1 := hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst A square
    Hk Nk hHkA eNk
  obtain ⟨hT, hχT⟩ := eulerCharacteristic_twist q Q1 E.obj 1 A.X.hom (exists_freeChart_one E)
    supp1 (fin Q1)
  obtain ⟨eΦ⟩ := nonempty_pullback_twistedProduct_iso A cube H N Nk eN k eNk (mulOnSecond A k)
    (mulOnSecond_first A k) (mulOnSecond_second A k)
  obtain ⟨hfin, hflat, -⟩ := multiplication_isIsogeny_of_ne_zero A k hkK
  have : IsFinite (mulK A k).left := hfin
  have : Flat (mulK A k).left := hflat
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : LocallyOfFinitePresentation (mulK A k).left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨hΦ, hχΦ⟩ := eulerCharacteristic_finiteFlatBaseChange A.X.hom q (mulK A k).left
    (mulOnSecond A k).left q (isPullback_mulOnSecond A k) (k ^ (2 * g))
    (finrank_multiplication_eq_of_ne_zero A cube g hg H hH k hkK) Q0 supp0 (fin Q0)
  have hΦs : (mulOnSecond A k).left ≫ q ≫ A.X.hom = q ≫ A.X.hom := by
    rw [← Category.assoc, (isPullback_mulOnSecond A k).w, Category.assoc, Over.w (mulK A k)]
  have hQ0 := hasFiniteCohomology_mumfordAddition_tensor_fst A H N hH' hN'
  have hQ1 := hasFiniteCohomology_mumfordAddition_tensor_fst A Hk Nk hHk hNk
  have hP : HasFiniteCohomology (q ≫ A.X.hom)
      ((Scheme.Modules.pullback (mulOnSecond A k).left).obj Q0.obj) :=
    hasFiniteCohomology_of_iso (q ≫ A.X.hom) eΦ.symm hT
  calc eulerCharacteristic A.X.hom (tensorPow H.obj k) hHk *
        eulerCharacteristic A.X.hom Nk.obj hNk
      = eulerCharacteristic (mumfordProduct A).hom Q1.obj hQ1 :=
        (eulerCharacteristic_mumfordAddition_tensor_fst A Hk Nk hHk hNk hQ1).symm
    _ = eulerCharacteristic (q ≫ A.X.hom) Q1.obj (fin Q1) :=
        eulerCharacteristic_congr_hom hqs.symm _ _ _
    _ = eulerCharacteristic (q ≫ A.X.hom)
          (tensorObj Q1.obj ((Scheme.Modules.pullback q).obj E.obj)) hT := by
        rw [hχT hT, Nat.cast_one, one_mul]
    _ = eulerCharacteristic (q ≫ A.X.hom)
          ((Scheme.Modules.pullback (mulOnSecond A k).left).obj Q0.obj) hP :=
        eulerCharacteristic_eq_of_iso (q ≫ A.X.hom) hT hP eΦ.symm
    _ = eulerCharacteristic ((mulOnSecond A k).left ≫ q ≫ A.X.hom)
          ((Scheme.Modules.pullback (mulOnSecond A k).left).obj Q0.obj) hΦ :=
        eulerCharacteristic_congr_hom hΦs.symm _ _ _
    _ = ((k ^ (2 * g) : ℕ) : ℤ) * eulerCharacteristic (q ≫ A.X.hom) Q0.obj (fin Q0) := hχΦ hΦ
    _ = (k : ℤ) ^ (2 * g) * eulerCharacteristic (mumfordProduct A).hom Q0.obj hQ0 := by
        rw [eulerCharacteristic_congr_hom hqs _ (fin Q0) hQ0]
        push_cast
        rfl
    _ = (k : ℤ) ^ (2 * g) *
          (eulerCharacteristic A.X.hom H.obj hH' * eulerCharacteristic A.X.hom N.obj hN') := by
        rw [eulerCharacteristic_mumfordAddition_tensor_fst A H N hH' hN' hQ0]

/-- The reduction proved in this module: the balanced cube identity and the theorem of the
square together imply the `k^(2g)` scaling of the Euler product. -/
def AlgClosedFieldAmpleEulerInverseScalingReductionStatement : Prop :=
  Langlands.GroupScheme.FieldCubePullbackStatement.{u} →
    Langlands.GroupScheme.FieldTheoremOfTheSquareStatement.{u} →
      AlgClosedFieldAmpleEulerInverseScalingStatement.{u}

theorem algClosedFieldAmpleEulerInverseScalingReduction :
    AlgClosedFieldAmpleEulerInverseScalingReductionStatement.{u} :=
  fun cube square => algClosedFieldAmpleEulerInverseScaling_of_coprime
    (algClosedFieldAmpleEulerInverseScaling_of_ne_zero cube square)

end Main

end Langlands.AbelianScheme.ScalingAssembly
