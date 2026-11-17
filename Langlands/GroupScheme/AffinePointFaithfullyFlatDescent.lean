import Langlands.GroupScheme.AffinePoints
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Descent of points of a group scheme along faithfully flat algebra maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.AffinePointDescent

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {T T' : CommAlgCat.{u} R} (ι : T ⟶ T')

/-- The spectrum map of an algebra map `ι : T ⟶ T'` is `Spec.map ι`. -/
theorem algSpec_map_left :
    ((algSpec R).map ι.op).left = Spec.map (CommRingCat.ofHom ι.hom.toRingHom) :=
  rfl

theorem flat_surjective (hι : ι.hom.toRingHom.FaithfullyFlat) :
    Flat (Spec.map (CommRingCat.ofHom ι.hom.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom ι.hom.toRingHom)) :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ι.hom.toRingHom)).2 hι

theorem epi_left (hι : ι.hom.toRingHom.FaithfullyFlat) : Epi ((algSpec R).map ι.op).left := by
  obtain ⟨h₁, h₂⟩ := flat_surjective ι hι
  rw [algSpec_map_left]
  exact Flat.epi_of_flat_of_surjective _

theorem effectiveEpi_left (hι : ι.hom.toRingHom.FaithfullyFlat) :
    EffectiveEpi (Spec.map (CommRingCat.ofHom ι.hom.toRingHom)) := by
  obtain ⟨h₁, h₂⟩ := flat_surjective ι hι
  infer_instance

/-- Points of a group scheme are determined after a faithfully flat extension of coefficients. -/
theorem affinePointMap_injective (hι : ι.hom.toRingHom.FaithfullyFlat) :
    Function.Injective (G.affinePointMap ι) := by
  intro x y hxy
  have := epi_left ι hι
  rw [affinePointMap_apply, affinePointMap_apply] at hxy
  apply Over.OverMorphism.ext
  exact (cancel_epi ((algSpec R).map ι.op).left).1 (congrArg CommaMorphism.left hxy)

/-- The tensor square `T' ⊗[T] T'`, as an algebra over `R`. -/
abbrev square : CommAlgCat.{u} R :=
  letI : Algebra T T' := ι.hom.toRingHom.toAlgebra
  letI : Algebra R (T' ⊗[T] T') := Algebra.compHom _ (algebraMap R T)
  CommAlgCat.of R (T' ⊗[T] T')

/-- The first inclusion into the tensor square. -/
def inl : T' ⟶ square ι :=
  letI : Algebra T T' := ι.hom.toRingHom.toAlgebra
  letI : Algebra R (T' ⊗[T] T') := Algebra.compHom _ (algebraMap R T)
  CommAlgCat.ofHom (X := T') (Y := T' ⊗[T] T')
    { Algebra.TensorProduct.includeLeftRingHom with
      commutes' := fun r => by
        change algebraMap R T' r ⊗ₜ[T] (1 : T') = ι.hom (algebraMap R T r) ⊗ₜ[T] (1 : T')
        rw [ι.hom.commutes] }

/-- The second inclusion into the tensor square. -/
def inr : T' ⟶ square ι :=
  letI : Algebra T T' := ι.hom.toRingHom.toAlgebra
  letI : Algebra R (T' ⊗[T] T') := Algebra.compHom _ (algebraMap R T)
  CommAlgCat.ofHom (X := T') (Y := T' ⊗[T] T')
    { (Algebra.TensorProduct.includeRight (R := T) (A := T') (B := T')).toRingHom with
      commutes' := fun r => by
        change (1 : T') ⊗ₜ[T] algebraMap R T' r = ι.hom (algebraMap R T r) ⊗ₜ[T] (1 : T')
        rw [← ι.hom.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := T) (A := T') (B := T')
          (algebraMap R T r)).symm }

theorem comp_inl_eq_comp_inr : ι ≫ inl ι = ι ≫ inr ι := by
  refine CommAlgCat.hom_ext (DFunLike.ext _ _ fun t => ?_)
  letI : Algebra T T' := ι.hom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := T) (A := T') (B := T') t

/-- **Effective descent of points** along a faithfully flat algebra map: a point over `T'` whose
two images over every pair of maps agreeing on `T` coincide comes from a point over `T`. -/
theorem exists_affinePointMap_eq (hι : ι.hom.toRingHom.FaithfullyFlat) (x' : G.affinePoints T')
    (hx : ∀ (Z : CommAlgCat.{u} R) (a b : T' ⟶ Z), ι ≫ a = ι ≫ b →
      G.affinePointMap a x' = G.affinePointMap b x') :
    ∃ x : G.affinePoints T, G.affinePointMap ι x = x' := by
  have := epi_left ι hι
  letI : Algebra T T' := ι.hom.toRingHom.toAlgebra
  let π : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T T'))
  have := effectiveEpi_left ι hι
  have : EffectiveEpi π := this
  have : Epi π := inferInstance
  have hsq := congrArg CommaMorphism.left (hx (square ι) (inl ι) (inr ι) (comp_inl_eq_comp_inr ι))
  rw [affinePointMap_apply, affinePointMap_apply] at hsq
  have key : pullback.fst π π ≫ x'.left = pullback.snd π π ≫ x'.left := by
    rw [← cancel_epi (pullbackSpecIso T T' T').inv]
    change (pullbackSpecIso T T' T').inv ≫ pullback.fst (Spec.map (CommRingCat.ofHom
      (algebraMap T T'))) (Spec.map (CommRingCat.ofHom (algebraMap T T'))) ≫ x'.left =
      (pullbackSpecIso T T' T').inv ≫ pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap T T'))) (Spec.map (CommRingCat.ofHom (algebraMap T T'))) ≫ x'.left
    rw [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
    exact hsq
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of T')), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ x'.left = g₂ ≫ x'.left := by
    intro Z g₁ g₂ hg
    calc g₁ ≫ x'.left = (pullback.lift g₁ g₂ hg ≫ pullback.fst π π) ≫ x'.left := by
          rw [pullback.lift_fst]
      _ = pullback.lift g₁ g₂ hg ≫ (pullback.snd π π ≫ x'.left) := by
          rw [Category.assoc, key]
      _ = g₂ ≫ x'.left := by rw [← Category.assoc, pullback.lift_snd]
  let y : Spec (CommRingCat.of T) ⟶ G.X.left := EffectiveEpi.desc π x'.left hdesc
  have hy : π ≫ y = x'.left := EffectiveEpi.fac π x'.left hdesc
  have hover : y ≫ G.X.hom = ((algSpec R).obj (op T)).hom := by
    apply (cancel_epi π).1
    rw [← Category.assoc, hy, Over.w x']
    exact (Over.w ((algSpec R).map ι.op)).symm
  refine ⟨Over.homMk y hover, ?_⟩
  rw [affinePointMap_apply]
  apply Over.OverMorphism.ext
  exact hy

end Langlands.GroupScheme.AffinePointDescent
