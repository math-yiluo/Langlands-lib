import Langlands.Geometry.Analytic.FiniteMorphismFibres
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Algebraic.Integral

/-! # Finite completed residue-field extensions -/

noncomputable section

universe u v w

open TensorProduct

namespace Langlands.Analytic

/-- A finite-dimensional subalgebra of an ultrametric normed field is closed
when the scalar field is complete, including the trivially normed case. -/
theorem isClosed_finite_subalgebra {E : Type u} {F : Type v}
    [NormedField E] [CompleteSpace E] [NormedField F] [IsUltrametricDist F]
    [NormedAlgebra E F] (S : Subalgebra E F) [Module.Finite E S] :
    IsClosed (S : Set F) := by
  by_cases hnt : ∃ c : E, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne hnt
    exact S.toSubmodule.closed_of_finiteDimensional
  · push Not at hnt
    have halg (a : F) (ha : a ∈ S) : IsAlgebraic E a := by
      exact ((Algebra.IsIntegral.isIntegral (⟨a, ha⟩ : S)).map S.val).isAlgebraic
    apply Metric.isClosed_of_pairwise_le_dist (ε := 1) zero_lt_one
    intro a ha b hb hab
    rw [dist_eq_norm]
    have hn : ‖a - b‖ = 1 := absoluteValue_eq_one_of_trivial hnt
      (pullbackAbsoluteValue (RingHom.id F))
      (fun x y => IsUltrametricDist.norm_add_le_max x y)
      (fun c => norm_algebraMap' F c) (halg (a - b) (S.sub_mem ha hb))
      (sub_ne_zero.mpr hab)
    exact hn.ge

namespace BanachSpectrum

variable {A : Type v} [NormedCommRing A]
  (K : Type u) [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

/-- A closed subalgebra of a completed residue field containing the original
residue image contains the whole completion, provided it is finite over its
scalar field. -/
theorem finite_subalgebra_eq_top_of_residueMap (x : BanachSpectrum A)
    {E : Type w} [Field E] [Algebra E (CompletedResidueField K x)]
    (S : Subalgebra E (CompletedResidueField K x)) [Module.Finite E S]
    (hclosed : IsClosed (S : Set (CompletedResidueField K x)))
    (hmap : ∀ a : A, completedResidueMap K x a ∈ S) : S = ⊤ := by
  apply top_unique
  intro z _
  refine UniformSpace.Completion.induction_on z hclosed ?_
  intro a
  obtain ⟨b, c, _hc, ha⟩ := IsFractionRing.div_surjective (ResidueDomain x) a.ofAbs
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) b
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) c
  have ha' : a = residueFieldMap K x b / residueFieldMap K x c :=
    (WithAbs.equiv (fractionAbsoluteValue K x)).injective ha.symm
  change residueCompletionMap K x a ∈ S
  rw [ha', map_div₀]
  change completedResidueMap K x b / completedResidueMap K x c ∈ S
  rw [div_eq_mul_inv]
  apply S.mul_mem (hmap b)
  have hc : IsAlgebraic E (completedResidueMap K x c) :=
    ((Algebra.IsIntegral.isIntegral
      (⟨completedResidueMap K x c, hmap c⟩ : S)).map S.val).isAlgebraic
  exact S.inv_mem_of_algebraic (x := ⟨_, hmap c⟩) hc

variable {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Finiteness over the base completed residue field through the canonical
completed-residue comap, rather than through an arbitrary field embedding. -/
def IsFiniteCompletedResidueComap (f : BoundedAlgHom K A B) (y : BanachSpectrum B) : Prop :=
  letI := (completedResidueComap K f y).toAlgHom.toRingHom.toAlgebra
  Module.Finite (CompletedResidueField K (comap f.toBoundedRingHom y))
    (CompletedResidueField K y)

/-- A finite bounded algebra map induces a finite extension of completed
residue fields, with the algebra structure given by the canonical comap. -/
theorem finite_completedResidueComap (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (y : BanachSpectrum B) :
    IsFiniteCompletedResidueComap K f y := by
  let E := CompletedResidueField K (comap f.toBoundedRingHom y)
  let F := CompletedResidueField K y
  let : Algebra E F := (completedResidueComap K f y).toAlgHom.toRingHom.toAlgebra
  change Module.Finite E F
  let : NormedAlgebra E F :=
    { norm_smul_le := fun c a => by
        rw [Algebra.smul_def, norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((isometry_completedResidueComap K f y).norm_map_of_map_zero
            (map_zero _) c).le (norm_nonneg a) }
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A E :=
    (completedResidueMap K (comap f.toBoundedRingHom y)).toAlgHom.toRingHom.toAlgebra
  let : Algebra A F :=
    ((completedResidueMap K y).toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  let : IsScalarTower A E F := IsScalarTower.of_algebraMap_eq
    (fun a => (completedResidueComap_map K f y a).symm)
  let g : B →ₐ[A] F :=
    { toRingHom := (completedResidueMap K y).toAlgHom.toRingHom
      commutes' := fun _ => rfl }
  let φ : E ⊗[A] B →ₐ[E] F := g.liftEquiv A E B F
  let S : Subalgebra E F := φ.range
  have : Module.Finite A B := hf
  have : Module.Finite E S := Module.Finite.of_surjective φ.rangeRestrict.toLinearMap
    φ.rangeRestrict_surjective
  have htop : S = ⊤ := finite_subalgebra_eq_top_of_residueMap K y S
    (isClosed_finite_subalgebra S) (fun b => by
      change ∃ z, φ z = completedResidueMap K y b
      exact ⟨1 ⊗ₜ[A] b, by simp [φ, g]⟩)
  exact Module.Finite.of_surjective S.val.toLinearMap (fun z =>
    ⟨⟨z, by rw [htop]; trivial⟩, rfl⟩)

/-- In particular, the canonical completed-residue extension of a finite
bounded algebra map is algebraic. -/
theorem algebraic_completedResidueComap (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (y : BanachSpectrum B) :
    letI := (completedResidueComap K f y).toAlgHom.toRingHom.toAlgebra
    Algebra.IsAlgebraic (CompletedResidueField K (comap f.toBoundedRingHom y))
      (CompletedResidueField K y) := by
  let := (completedResidueComap K f y).toAlgHom.toRingHom.toAlgebra
  have : Module.Finite (CompletedResidueField K (comap f.toBoundedRingHom y))
      (CompletedResidueField K y) := finite_completedResidueComap K f hf y
  infer_instance

end BanachSpectrum

end Langlands.Analytic
