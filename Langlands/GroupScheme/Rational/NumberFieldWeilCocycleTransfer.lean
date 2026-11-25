import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.AffineWeilCocycleTransfer
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.Global.AdelicFunctoriality.Extension

/-! # Number-field transfer for cocycles on an affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct

namespace Langlands.Global

variable (A B : Type u) [Field A] [Field B] [NumberField A] [NumberField B] [Algebra A B]

/-- The place of the base field obtained by restriction along the number-field extension. -/
def restrictPlace : Place B → Place A
  | .inl w => .inl (w.comap (algebraMap A B))
  | .inr w => .inr (w.under (𝓞 A))

/-- The homomorphism of actual completed fields at an extension of places. -/
def placeCompletionExtension (w : Place B) :
    placeCompletion A (restrictPlace A B w) →+* placeCompletion B w := by
  rcases w with w | w
  · let v := w.comap (algebraMap A B)
    let : w.LiesOver v := ⟨rfl⟩
    exact NumberField.LiesOver.completionMap (v := v) (w := w)
  · let v := w.under (𝓞 A)
    let : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 A)))
    exact AdelicFunctoriality.FiniteExtension.completionMap v w

/-- The homomorphism of completions agrees with the global embedding on the base field. -/
theorem placeCompletionExtension_algebraMap (w : Place B) (x : A) :
    placeCompletionExtension A B w (algebraMap A (placeCompletion A (restrictPlace A B w)) x) =
      algebraMap B (placeCompletion B w) (algebraMap A B x) := by
  rcases w with w | w
  · let v := w.comap (algebraMap A B)
    let : w.LiesOver v := ⟨rfl⟩
    change NumberField.LiesOver.completionMap (v := v) (w := w)
        ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.Completion) =
      ((WithAbs.toAbs w.1 (algebraMap A B x) : WithAbs w.1) : w.Completion)
    exact NumberField.LiesOver.completionMap_coe v w (WithAbs.toAbs v.1 x)
  · let v := w.under (𝓞 A)
    let : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 A)))
    exact AdelicFunctoriality.FiniteExtension.completionMap_coe v w x

end Langlands.Global

namespace Langlands.GroupScheme.AffineWeil

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [Field A] [Field B] [NumberField A] [NumberField B] [Algebra A B]
  [Module.Finite A B]
  (H : GroupScheme (Spec (CommRingCat.of B))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- Transfer to an extension field preserves triviality at every place. -/
theorem locallyTrivial_transferCocycle {U : Over (Spec (CommRingCat.of A))}
    (ξ : Cocycle (groupScheme A B H) U) (hξ : ξ.LocallyTrivial) :
    (transferCocycle A B H ξ).LocallyTrivial := by
  intro w
  let v := Global.restrictPlace A B w
  let b := algebraBaseMap A B
  let c := algebraBaseMap B (Global.placeCompletion B w)
  let d := algebraBaseMap A (Global.placeCompletion A v)
  let e := Spec.map (CommRingCat.ofHom (Global.placeCompletionExtension A B w))
  have hsq : c ≫ b = e ≫ d := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f : A →+* Global.placeCompletion B w => Spec.map (CommRingCat.ofHom f))
    ext x
    exact (Global.placeCompletionExtension_algebraMap A B w x).symm
  have ht := Cocycle.isTrivial_baseChangePullback_twice b c d e hsq ξ (hξ v)
  obtain ⟨f, hf⟩ := ht.map ((GroupScheme.baseChange c).map (cocycleEvaluation A B H))
  refine ⟨f, fun x y => ?_⟩
  change (((ξ.baseChangePullback b).map (cocycleEvaluation A B H)).baseChangePullback c).toFun x y = _
  unfold Cocycle.baseChangePullback
  rw [Cocycle.baseChange_map_toFun]
  exact hf x y

open Algebra.TensorProduct in
/-- The transfer can be tested over a finite Galois field covering the extension base.
The chart obtained from a maximal ideal of the tensor product supplies the cover map. -/
theorem exists_finiteGalois_transfer {L : Type u} [Field L] [Algebra A L] [FiniteDimensional A L]
    (ξ : Cocycle (groupScheme A B H) (ringTest A L)) (hξ : ξ.LocallyTrivial) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra B E) (_ : FiniteDimensional B E) (_ : IsGalois B E)
      (r : ringTest B E ⟶ (Over.pullback (algebraBaseMap A B)).obj (ringTest A L)),
      ((transferCocycle A B H ξ).refine r).LocallyTrivial ∧
      (((transferCocycle A B H ξ).refine r).IsTrivial → ξ.IsTrivial) := by
  let D := B ⊗[A] L
  have : Nontrivial D := nontrivial_of_algebraMap_injective_of_isDomain A B L
    (algebraMap A B).injective (algebraMap A L).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal D
  let : Field (D ⧸ m) := Ideal.Quotient.field m
  have : FiniteDimensional B D := inferInstanceAs (Module.Finite B (B ⊗[A] L))
  have : FiniteDimensional B (D ⧸ m) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ B m).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨E, hEfin, hEgal, ⟨i⟩⟩ := exists_finite_galois_algHom B (D ⧸ m)
  let r := ringTestMap B (i.comp (Ideal.Quotient.mkₐ B m)) ≫ (ringBaseChangeSpectrumIso A B L).inv
  let ζ := transferCocycle A B H ξ
  refine ⟨E, inferInstance, inferInstance, hEfin, hEgal, r, ?_, ?_⟩
  · intro w
    let c := algebraBaseMap B (Global.placeCompletion B w)
    obtain ⟨f, hf⟩ := ((locallyTrivial_transferCocycle A B H ξ hξ) w).refine ((Over.pullback c).map r)
    refine ⟨f, fun x y => ?_⟩
    rw [Cocycle.baseChange_pullback_refine_toFun]
    exact hf x y
  · intro h
    obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc B E
    let : Surjective (ringTest B E).hom := hs
    let : Flat (ringTest B E).hom := hf
    let : QuasiCompact (ringTest B E).hom := hq
    exact isTrivial_of_transferCocycle A B H ξ (Cocycle.IsTrivial.of_refine_fpqcCover r h)

end Langlands.GroupScheme.AffineWeil
