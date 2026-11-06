import Langlands.AlgebraicGeometry.TangentSmoothness
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! # Dense range from tangent surjectivity at a point with values in a field extension -/

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.TangentSmoothness

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.Langlands.AlgebraicGeometry.Picard

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` of schemes over `Spec k` is surjective on tangent vectors at a
`K`-valued point `x` of `X`, for a field extension `K` of `k`, when every `K[ε]`-valued point of
`Y` over `k` restricting to `x ≫ f` is the image under `f` of a `K[ε]`-valued point of `X` over
`k` restricting to `x`. -/
def IsTangentSurjectiveAtExtension (p : X ⟶ Spec (CommRingCat.of k))
    (q : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : Spec (CommRingCat.of K) ⟶ X) : Prop :=
  ∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ Y,
    t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber K))) →
    dualNumberAugmentation K ≫ t = x ≫ f →
    ∃ s : Spec (CommRingCat.of (DualNumber K)) ⟶ X,
      s ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber K))) ∧
      dualNumberAugmentation K ≫ s = x ∧ s ≫ f = t

/-- The structure morphism of `Spec K[ε]` over `Spec k` factors through `Spec K`. -/
lemma specMap_algebraMap_dualNumber :
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber K))) =
      dualNumberProjection K ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [dualNumberProjection, ← Spec.map_comp]
  congr 1

/-- The spectrum of a field extension is surjective onto the spectrum of the base field. -/
lemma surjective_specMap_algebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨z, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩

/-- **Dense range from tangent surjectivity at a point with values in a field extension.**
Let `f : X ⟶ Y` be a morphism over `Spec k` with `X` smooth over `k` and `Y` locally of finite
type and geometrically irreducible over `k`. If `f` is surjective on tangent
vectors at some `K`-valued point of `X`, for a field extension `K` of `k`, then `f` has dense
range. -/
theorem denseRange_of_isTangentSurjectiveAtExtension {p : X ⟶ Spec (CommRingCat.of k)}
    {q : Y ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType q]
    [GeometricallyIrreducible q] (f : X ⟶ Y) (hf : f ≫ q = p)
    {x : Spec (CommRingCat.of K) ⟶ X}
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (h : IsTangentSurjectiveAtExtension p q f x) : DenseRange f := by
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let fK : pullback p b ⟶ pullback q b :=
    pullback.map p b q b f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hfK₁ : fK ≫ pullback.fst q b = pullback.fst p b ≫ f := pullback.lift_fst _ _ _
  have hfK₂ : fK ≫ pullback.snd q b = pullback.snd p b :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let xK : Spec (CommRingCat.of K) ⟶ pullback p b :=
    pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])
  have hxK : IsRationalPoint (pullback.snd p b) xK := pullback.lift_snd _ _ _
  have hK : IsTangentSurjectiveAt (pullback.snd p b) (pullback.snd q b) fK xK := by
    rintro t ⟨ht₁, ht₂⟩
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := h (t ≫ pullback.fst q b)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, ht₁,
        specMap_algebraMap_dualNumber])
      (by rw [← Category.assoc, ht₂, Category.assoc, hfK₁, ← Category.assoc,
        pullback.lift_fst])
    refine ⟨pullback.lift s (dualNumberProjection K)
      (by rw [hs₁, specMap_algebraMap_dualNumber]), ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hs₂]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
          dualNumberAugmentation_comp_dualNumberProjection]
    · apply pullback.hom_ext
      · rw [Category.assoc, hfK₁, ← Category.assoc, pullback.lift_fst, hs₃]
      · rw [Category.assoc, hfK₂, pullback.lift_snd, ht₁]
  have hdK : DenseRange fK := denseRange_of_isTangentSurjectiveAt fK hfK₂ hxK hK
  have : Surjective b := surjective_specMap_algebraMap
  have hcomp : DenseRange (fun z => pullback.fst q b (fK z)) :=
    (pullback.fst q b).surjective.denseRange.comp hdK (pullback.fst q b).continuous
  have heq : (fun z => pullback.fst q b (fK z)) = fun z => f (pullback.fst p b z) := by
    funext z
    change (fK ≫ pullback.fst q b) z = (pullback.fst p b ≫ f) z
    rw [hfK₁]
  rw [heq] at hcomp
  exact hcomp.mono (Set.range_comp_subset_range (pullback.fst p b) f)

end Langlands.AlgebraicGeometry.TangentSmoothness
