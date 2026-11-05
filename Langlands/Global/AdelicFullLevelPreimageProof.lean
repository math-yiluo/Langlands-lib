import Langlands.Global.AdelicFullLevelPreimageStatement
import Langlands.Global.AdelicLocalIntegralPreimageProof
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs

/-! # Full-level preimages by local lifts and product comparison -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

private theorem changeRing_comp
    {C A B D : Type u} [CommRing C] [CommRing A] [CommRing B] [CommRing D]
    [Algebra C A] [Algebra C B] [Algebra C D]
    {X : Over (Spec (CommRingCat.of C))} (p : RingPoint C X A)
    (f : A →ₐ[C] B) (g : B →ₐ[C] D) :
    (p.changeRing f).changeRing g = p.changeRing (g.comp f) := by
  let p₀ : ringTest C A ⟶ X := p
  change ringTestMap C g ≫ (ringTestMap C f ≫ p₀) = ringTestMap C (g.comp f) ≫ p₀
  rw [← Category.assoc, ← ringTestMap_comp]

/-- Local coefficient lifts assemble into a point of the actual level algebra. -/
private theorem mem_range_of_local_lifts
    (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B]
    {ι : Type u} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, CommRing (L i)]
    [∀ i, Algebra C (R i)] [∀ i, Algebra C (L i)]
    [∀ i, IsLocalRing (R i)] [∀ i, IsReduced (L i)]
    (a : A →ₐ[C] B) (e : A ≃ₐ[C] ∀ i, R i)
    (b : B →ₐ[C] ∀ i, L i) (hb : Function.Injective b)
    (r : ∀ i, R i →ₐ[C] L i)
    (hcompat : ∀ i, (Pi.evalAlgHom C L i).comp (b.comp a) =
      (r i).comp ((Pi.evalAlgHom C R i).comp e.toAlgHom))
    (X : Over (Spec (CommRingCat.of C)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [IsSeparated X.hom]
    (z : RingPoint C X B)
    (hlift : ∀ i, ∃ q : RingPoint C X (R i),
      q.changeRing (r i) = z.changeRing ((Pi.evalAlgHom C L i).comp b)) :
    z ∈ Set.range (RingPoint.changeRing (X := X) a) := by
  classical
  let q : ∀ i, RingPoint C X (R i) := fun i => Classical.choose (hlift i)
  have hq (i) : (q i).changeRing (r i) =
      z.changeRing ((Pi.evalAlgHom C L i).comp b) :=
    Classical.choose_spec (hlift i)
  obtain ⟨p, hp⟩ := productPointMap_surjective C R X q
  let pA : RingPoint C X A := (ringPointChangeRingEquiv C X e).symm p
  have hpA : productPointMap C R X (pA.changeRing e.toAlgHom) = q := by
    change productPointMap C R X
      ((ringPointChangeRingEquiv C X e) ((ringPointChangeRingEquiv C X e).symm p)) = q
    rw [Equiv.apply_symm_apply]
    exact hp
  refine ⟨pA, ?_⟩
  let : IsReduced B := isReduced_of_injective b hb
  apply schemeSeparatedCoefficientInjectivity_proof C B (∀ i, L i) X b hb
  apply productPointMap_injective C L X
  funext i
  change ((pA.changeRing a).changeRing b).changeRing (Pi.evalAlgHom C L i) =
    (z.changeRing b).changeRing (Pi.evalAlgHom C L i)
  calc
    ((pA.changeRing a).changeRing b).changeRing (Pi.evalAlgHom C L i) =
        pA.changeRing ((Pi.evalAlgHom C L i).comp (b.comp a)) := by
          simp only [changeRing_comp]
    _ = pA.changeRing ((r i).comp ((Pi.evalAlgHom C R i).comp e.toAlgHom)) := by
      rw [hcompat i]
    _ = ((pA.changeRing e.toAlgHom).changeRing (Pi.evalAlgHom C R i)).changeRing
        (r i) := by simp only [changeRing_comp]
    _ = (q i).changeRing (r i) := by
      exact congrArg (RingPoint.changeRing (r i)) (congrFun hpA i)
    _ = z.changeRing ((Pi.evalAlgHom C L i).comp b) := hq i
    _ = (z.changeRing b).changeRing (Pi.evalAlgHom C L i) :=
      (changeRing_comp z b (Pi.evalAlgHom C L i)).symm

private theorem changeRing_postcomp
    {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B]
    {X Y : Over (Spec (CommRingCat.of C))}
    (p : RingPoint C X A) (f : X ⟶ Y) (a : A →ₐ[C] B) :
    RingPoint.changeRing a (p ≫ f : RingPoint C Y A) = p.changeRing a ≫ f := by
  let p₀ : ringTest C A ⟶ X := p
  exact (Category.assoc (ringTestMap C a) p₀ f).symm

private theorem preimage_eq_of_local_preimages
    (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B]
    {ι : Type u} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, CommRing (L i)]
    [∀ i, Algebra C (R i)] [∀ i, Algebra C (L i)]
    [∀ i, IsLocalRing (R i)] [∀ i, IsReduced (L i)]
    (a : A →ₐ[C] B) (e : A ≃ₐ[C] ∀ i, R i)
    (b : B →ₐ[C] ∀ i, L i) (hb : Function.Injective b)
    (r : ∀ i, R i →ₐ[C] L i)
    (hcompat : ∀ i, (Pi.evalAlgHom C L i).comp (b.comp a) =
      (r i).comp ((Pi.evalAlgHom C R i).comp e.toAlgHom))
    (X Y : Over (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [IsSeparated X.hom]
    (hlocal : ∀ i,
      (fun p : RingPoint C X (L i) => (p ≫ f : RingPoint C Y (L i))) ⁻¹'
          Set.range (RingPoint.changeRing (X := Y) (r i)) =
        Set.range (RingPoint.changeRing (X := X) (r i))) :
    (fun p : RingPoint C X B => (p ≫ f : RingPoint C Y B)) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) a) =
      Set.range (RingPoint.changeRing (X := X) a) := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    apply mem_range_of_local_lifts C A B R L a e b hb r hcompat X z
    intro i
    change z.changeRing ((Pi.evalAlgHom C L i).comp b) ∈
      Set.range (RingPoint.changeRing (X := X) (r i))
    rw [← hlocal i]
    refine ⟨w.changeRing ((Pi.evalAlgHom C R i).comp e.toAlgHom), ?_⟩
    rw [changeRing_comp, ← hcompat i]
    change w.changeRing (((Pi.evalAlgHom C L i).comp b).comp a) = _
    rw [← changeRing_comp, hw]
    exact changeRing_postcomp z f _
  · rintro ⟨q, rfl⟩
    exact ⟨q ≫ f, changeRing_postcomp q f a⟩

private theorem preimage_eq_of_bijective
    {C R L : Type u} [CommRing C] [CommRing R] [CommRing L]
    [Algebra C R] [Algebra C L] (r : R →ₐ[C] L) (hr : Function.Bijective r)
    (X Y : Over (Spec (CommRingCat.of C))) (f : X ⟶ Y) :
    (fun p : RingPoint C X L => (p ≫ f : RingPoint C Y L)) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) r) =
      Set.range (RingPoint.changeRing (X := X) r) := by
  have hX : Function.Surjective (RingPoint.changeRing (X := X) r) :=
    (ringPointChangeRingEquiv C X (AlgEquiv.ofBijective r hr)).surjective
  have hY : Function.Surjective (RingPoint.changeRing (X := Y) r) :=
    (ringPointChangeRingEquiv C Y (AlgEquiv.ofBijective r hr)).surjective
  ext z
  constructor
  · intro _
    exact hX z
  · intro _
    exact hY (z ≫ f)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

private def curveFullFactor (S : Finset (AlgebraicCurve.Place k F)) :
    CurvePlaceLevelFactorIndex k F S → Type u
  | .inl v => curvePlaceCompletion v.1
  | .inr v => curvePlaceCompletion v.1

private instance curveFullFactorField (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) : Field (curveFullFactor k F S i) := by
  cases i <;> dsimp [curveFullFactor] <;> infer_instance

private instance curveFullFactorAlgebra (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    Algebra (curvePlaceSIntegers k F S) (curveFullFactor k F S i) := by
  cases i with
  | inl v => exact ((algebraMap F (curvePlaceCompletion v.1)).comp
      (curvePlaceSIntegers k F S).subtype).toAlgebra
  | inr v => exact ((algebraMap F (curvePlaceCompletion v.1)).comp
      (curvePlaceSIntegers k F S).subtype).toAlgebra

private def curveFullProjection (S : Finset (AlgebraicCurve.Place k F)) :
    ∀ i : CurvePlaceLevelFactorIndex k F S,
      curvePlaceAdeleOver k F S →+* curveFullFactor k F S i
  | .inl v => RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v.1
  | .inr v => RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v.1

private def curveFullProductMap (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S]
      ∀ i, curveFullFactor k F S i :=
  { toRingHom := RingHom.pi (curveFullProjection k F S)
    commutes' := by intro c; funext i; cases i <;> rfl }

private theorem curveFullProductMap_injective (S : Finset (AlgebraicCurve.Place k F)) :
    Function.Injective (curveFullProductMap k F S) := by
  classical
  intro a b h
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v ∈ S
  · exact congrFun h (.inl ⟨v, hv⟩)
  · exact congrFun h (.inr ⟨v, hv⟩)

private def curveFullLocalMap (S : Finset (AlgebraicCurve.Place k F)) :
    ∀ i : CurvePlaceLevelFactorIndex k F S,
      CurvePlaceLevelFactor k F S i →ₐ[curvePlaceSIntegers k F S]
        curveFullFactor k F S i
  | .inl _ => { toRingHom := RingHom.id _, commutes' := fun _ => rfl }
  | .inr v =>
      { toRingHom := (curvePlaceCompletionIntegers v.1).subtype
        commutes' := fun _ => rfl }

end Curve

/-- The actual curve-place full-adele preimage equality. -/
theorem curvePlaceFullLevelPreimage : CurvePlaceFullLevelPreimageStatement.{u} := by
  intro k F _ _ _ S
  dsimp only
  intro X Y _ _ f _
  let : QuasiCompact X.hom := by rw [← Over.w f]; infer_instance
  let : IsSeparated X.hom := by rw [← Over.w f]; infer_instance
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  refine preimage_eq_of_local_preimages (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevel k F S) (curvePlaceAdeleOver k F S)
    (CurvePlaceLevelFactor k F S) (curveFullFactor k F S)
    _ (curvePlaceLevelFactorAlgEquiv k F S) (curveFullProductMap k F S)
    (curveFullProductMap_injective k F S) (curveFullLocalMap k F S) ?_ X Y f ?_
  · intro i
    ext a
    cases i <;> rfl
  · intro i
    cases i with
    | inl v =>
      exact preimage_eq_of_bijective (curveFullLocalMap k F S (.inl v))
        Function.bijective_id X Y f
    | inr v =>
      let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
        inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F S (.inr v)))
      let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
        inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
          (curveFullFactor k F S (.inr v)))
      let : IsScalarTower (curvePlaceSIntegers k F S)
          (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) :=
        IsScalarTower.of_algebraMap_eq (R := curvePlaceSIntegers k F S)
          (S := curvePlaceCompletionIntegers v.1) (A := curvePlaceCompletion v.1)
          fun _ => rfl
      exact universallyClosed_ringPoint_preimage (curvePlaceSIntegers k F S)
        (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) X Y f

section NumberField

variable (K : Type u) [Field K] [NumberField K]

private def numberFullFactor (S : Finset (FinitePlace K)) :
    NumberFieldLevelFactorIndex K S → Type u
  | .inl v => InfiniteCompletion K v
  | .inr (.inl v) => FiniteCompletion K v.1
  | .inr (.inr v) => FiniteCompletion K v.1

private instance numberFullFactorField (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) : Field (numberFullFactor K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (Field (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [numberFullFactor] <;> infer_instance

private instance numberFullFactorAlgebra (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) :
    Algebra ((S : Set (FinitePlace K)).integer K) (numberFullFactor K S i) := by
  cases i with
  | inl v => exact ((algebraMap K (InfiniteCompletion K v)).comp
      ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra
  | inr j =>
    cases j with
    | inl v => exact ((algebraMap K (FiniteCompletion K v.1)).comp
        ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra
    | inr v => exact ((algebraMap K (FiniteCompletion K v.1)).comp
        ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra

private def numberFullProjection (S : Finset (FinitePlace K)) :
    ∀ i : NumberFieldLevelFactorIndex K S,
      numberFieldAdeleOver K S →+* numberFullFactor K S i
  | .inl v => infiniteProjection K v
  | .inr (.inl v) => finiteProjection K v.1
  | .inr (.inr v) => finiteProjection K v.1

private def numberFullProductMap (S : Finset (FinitePlace K)) :
    numberFieldAdeleOver K S →ₐ[(S : Set (FinitePlace K)).integer K]
      ∀ i, numberFullFactor K S i :=
  { toRingHom := RingHom.pi (numberFullProjection K S)
    commutes' := by
      intro c
      funext i
      cases i with
      | inl v => rfl
      | inr j => cases j <;> rfl }

private theorem numberFullProductMap_injective (S : Finset (FinitePlace K)) :
    Function.Injective (numberFullProductMap K S) := by
  classical
  intro a b h
  apply Prod.ext
  · funext v
    exact congrFun h (.inl v)
  · apply RestrictedProduct.ext
    intro v
    by_cases hv : v ∈ S
    · exact congrFun h (.inr (.inl ⟨v, hv⟩))
    · exact congrFun h (.inr (.inr ⟨v, hv⟩))

private def numberFullLocalMap (S : Finset (FinitePlace K)) :
    ∀ i : NumberFieldLevelFactorIndex K S,
      NumberFieldLevelFactor K S i →ₐ[(S : Set (FinitePlace K)).integer K]
        numberFullFactor K S i
  | .inl _ => { toRingHom := RingHom.id _, commutes' := fun _ => rfl }
  | .inr (.inl _) => { toRingHom := RingHom.id _, commutes' := fun _ => rfl }
  | .inr (.inr v) =>
      { toRingHom := (v.1.adicCompletionIntegers K).subtype
        commutes' := fun _ => rfl }

end NumberField

/-- The actual number-field full-adele preimage equality, including all infinite places. -/
theorem numberFieldFullLevelPreimage : NumberFieldFullLevelPreimageStatement.{u} := by
  intro K _ _ S
  dsimp only
  intro X Y _ _ f _
  let : QuasiCompact X.hom := by rw [← Over.w f]; infer_instance
  let : IsSeparated X.hom := by rw [← Over.w f]; infer_instance
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  refine preimage_eq_of_local_preimages ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevel K S) (numberFieldAdeleOver K S)
    (NumberFieldLevelFactor K S) (numberFullFactor K S)
    _ (numberFieldLevelFactorAlgEquiv K S) (numberFullProductMap K S)
    (numberFullProductMap_injective K S) (numberFullLocalMap K S) ?_ X Y f ?_
  · intro i
    ext a
    cases i with
    | inl v => rfl
    | inr j => cases j <;> rfl
  · intro i
    cases i with
    | inl v =>
      exact preimage_eq_of_bijective (numberFullLocalMap K S (.inl v))
        Function.bijective_id X Y f
    | inr j =>
      cases j with
      | inl v =>
        exact preimage_eq_of_bijective (numberFullLocalMap K S (.inr (.inl v)))
          Function.bijective_id X Y f
      | inr v =>
        let : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
          inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
            (NumberFieldLevelFactor K S (.inr (.inr v))))
        let : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
          inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
            (numberFullFactor K S (.inr (.inr v))))
        let : SMul ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
          (inferInstance : Algebra ((S : Set (FinitePlace K)).integer K)
            (FiniteCompletion K v.1)).toSMul
        let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
            (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) :=
          IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace K)).integer K)
            (S := v.1.adicCompletionIntegers K) (A := FiniteCompletion K v.1)
            fun _ => rfl
        exact universallyClosed_ringPoint_preimage ((S : Set (FinitePlace K)).integer K)
          (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) X Y f

/-- The exact conjunction of both actual-arithmetic full-level preimage assertions. -/
theorem adelicFullLevelPreimage : AdelicFullLevelPreimageStatement.{u} :=
  ⟨curvePlaceFullLevelPreimage, numberFieldFullLevelPreimage⟩

end Langlands.Global
