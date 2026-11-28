import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-! # Transitivity on the geometric fibre of a connected finite étale cover -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))

/-- A map of finite étale covers which is surjective on underlying schemes is surjective on
geometric fibres. -/
theorem surjective_fiber_of_surjective {Y Z : Cover S} (i : Z ⟶ Y)
    (hi : Function.Surjective i.hom.left) :
    Function.Surjective (fun p : Fiber s Z => p ≫ i.hom) := by
  intro p
  have : IsFinite i.hom.left := by
    have : IsFinite (i.hom.left ≫ Y.obj.hom) := by rw [Over.w i.hom]; infer_instance
    exact IsFinite.of_comp i.hom.left Y.obj.hom
  have : Etale i.hom.left := by
    have : Etale (i.hom.left ≫ Y.obj.hom) := by rw [Over.w i.hom]; infer_instance
    exact Etale.of_comp i.hom.left Y.obj.hom
  obtain ⟨r, hr⟩ := Scheme.Hom.exists_lift_of_isSepClosed i.hom.left p.left
    ⟨IsLocalRing.closedPoint Ω, hi _⟩
  refine ⟨Over.homMk r ?_, ?_⟩
  · change r ≫ Z.obj.hom = s
    rw [← Over.w i.hom, ← Category.assoc, hr]
    exact Over.w p
  · exact Over.OverMorphism.ext hr

/-- **Transitivity on a connected cover.** If `S` is connected and locally Noetherian and the
underlying scheme of a finite étale cover `Y` is connected, the pointed fundamental group acts
transitively on the geometric fibre of `Y`. -/
theorem exists_smul_eq_of_connectedSpace [ConnectedSpace S] [IsLocallyNoetherian S]
    (Y : Cover S) [ConnectedSpace Y.obj.left] (p p' : Fiber s Y) :
    ∃ σ : FundamentalGroup s hs, σ • p = p' := by
  let hG := geometricGaloisFiberFunctor s hs
  let _ : GaloisCategory (Cover S) := Classical.choose hG
  let _ : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := Classical.choose_spec hG
  let F := fiberFunctor s hs
  have hconn : PreGaloisCategory.IsConnected Y := by
    refine ⟨fun h => ?_, fun Z i _ hZ => ?_⟩
    · have := (PreGaloisCategory.initial_iff_fiber_empty F Y).1 ⟨h⟩
      exact this.false p
    · obtain ⟨z⟩ : Nonempty (Fiber s Z) := (PreGaloisCategory.not_initial_iff_fiber_nonempty F Z).1 hZ
      let φ := i.hom.left
      have : IsFinite φ := by
        have : IsFinite (φ ≫ Y.obj.hom) := by rw [Over.w i.hom]; infer_instance
        exact IsFinite.of_comp φ Y.obj.hom
      have : Etale φ := by
        have : Etale (φ ≫ Y.obj.hom) := by rw [Over.w i.hom]; infer_instance
        exact Etale.of_comp φ Y.obj.hom
      have hc : IsClopen (Set.range φ) :=
        ⟨φ.isClosedMap.isClosed_range, φ.isOpenMap.isOpen_range⟩
      have hr : Set.range φ = Set.univ :=
        hc.eq_univ ⟨_, z.left (IsLocalRing.closedPoint Ω), rfl⟩
      have hsurj := surjective_fiber_of_surjective s i (Set.range_eq_univ.1 hr)
      by_contra hni
      have hlt := PreGaloisCategory.lt_card_fiber_of_mono_of_notIso F i hni
      exact (Nat.card_le_card_of_surjective _ hsurj).not_gt hlt
  have htr : MulAction.IsPretransitive (Aut F) (F.obj Y) :=
    PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected F Y
  exact htr.exists_smul_eq p p'

end Langlands.AlgebraicGeometry.FiniteEtale
