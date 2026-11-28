import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Submersion for conjugation from a Lie algebra slice -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open ContinuousLinearMap Filter Function Set _root_.Topology
open scoped RightActions _root_.Topology

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  {A : Type v} [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A]

/-- Conjugation in the ambient algebra chart for the conjugator. -/
def lieConjugationMap (B : Subalgebra F A) (z : A × B) : A :=
  z.1 * z.2.val * Ring.inverse z.1

/-- Conjugation by a unit of the ambient algebra, restricted to a subset of the slice. -/
def lieConjugationOnSlice (B : Subalgebra F A) (U : Set B) (z : Aˣ × U) : A :=
  conjugationHomeomorph z.1 z.2.val.val

omit [CompleteSpace F] [FiniteDimensional F A] in
@[simp]
theorem lieConjugationMap_unit (B : Subalgebra F A) (g : Aˣ) (X : B) :
    lieConjugationMap B (g.val, X) = conjugationHomeomorph g X.val := by
  rw [lieConjugationMap, conjugationHomeomorph_apply, Ring.inverse_unit]

/-- The strict differential at conjugator `1` sends `(a,b)` to `aX + b - Xa`. -/
def lieConjugationDifferential (B : Subalgebra F A) (X : B) : A × B →L[F] A :=
  let p := fst F A B
  let q := B.val.toLinearMap.toContinuousLinearMap.comp (snd F A B)
  (mulLeftRight F A 1 X.val).comp p + q - (mulLeftRight F A X.val 1).comp p

@[simp]
theorem lieConjugationDifferential_apply (B : Subalgebra F A) (X : B) (z : A × B) :
    lieConjugationDifferential B X z = z.1 * X.val + z.2.val - X.val * z.1 := by
  simp [lieConjugationDifferential, mulLeftRight_apply]

theorem hasStrictFDerivAt_lieConjugationMap_one (B : Subalgebra F A) (X : B) :
    HasStrictFDerivAt (lieConjugationMap B) (lieConjugationDifferential B X) (1, X) := by
  let : CompleteSpace A := FiniteDimensional.complete F A
  let p := fst F A B
  let q := B.val.toLinearMap.toContinuousLinearMap.comp (snd F A B)
  have hp : HasStrictFDerivAt (fun z : A × B => z.1) p (1, X) := p.hasStrictFDerivAt
  have hq : HasStrictFDerivAt (fun z : A × B => z.2.val) q (1, X) := q.hasStrictFDerivAt
  have hinv : HasStrictFDerivAt Ring.inverse (-(ContinuousLinearMap.id F A)) (1 : A) := by
    have he : mulLeftRight F A (1 : A) 1 = ContinuousLinearMap.id F A := by
      ext a
      simp [mulLeftRight_apply]
    simpa only [Units.val_one, inv_one, he] using
      hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Aˣ)
  have hprod := (hp.mul' hq).mul' (hinv.comp ((1, X) : A × B) hp)
  change HasStrictFDerivAt (lieConjugationMap B) _ _ at hprod
  have he : (1 * X.val) •> (-ContinuousLinearMap.id F A).comp p +
      ((1 : A) •> q + p <• X.val) <• Ring.inverse (1 : A) =
        lieConjugationDifferential B X := by
    rw [Ring.inverse_one]
    apply ContinuousLinearMap.ext
    intro z
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      _root_.neg_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul, mul_one, mul_neg,
      lieConjugationDifferential_apply]
    change -(X.val * z.1) + (z.2.val + z.1 * X.val) =
      z.1 * X.val + z.2.val - X.val * z.1
    abel
  rw [← he]
  exact hprod

theorem surjective_lieConjugationDifferential (B : Subalgebra F A) (X : B)
    (hX : B.toSubmodule ⊔ LinearMap.range (adjointEndomorphism F X.val) = ⊤) :
    Surjective (lieConjugationDifferential B X) := by
  intro z
  have hz : z ∈ B.toSubmodule ⊔ LinearMap.range (adjointEndomorphism F X.val) := by
    rw [hX]
    exact Submodule.mem_top
  obtain ⟨b, hb, w, ⟨a, ha⟩, hbw⟩ := Submodule.mem_sup.mp hz
  refine ⟨(-a, ⟨b, hb⟩), ?_⟩
  rw [lieConjugationDifferential_apply, ← hbw, ← ha, adjointEndomorphism_apply, neg_mul, mul_neg]
  abel

/-- Translation in the unit coordinate carries the strict submersion at `1` to any unit. -/
theorem lieConjugationMap_submersive (B : Subalgebra F A) (g : Aˣ) (X : B)
    (hX : B.toSubmodule ⊔ LinearMap.range (adjointEndomorphism F X.val) = ⊤) :
    ∃ d : A × B →L[F] A, HasStrictFDerivAt (lieConjugationMap B) d (g.val, X) ∧ Surjective d := by
  let L : A ≃L[F] A := (Units.mulLeftLinearEquiv F A g).toContinuousLinearEquiv
  let C : A ≃L[F] A := (conjugationLinearEquiv F g).toContinuousLinearEquiv
  let E : (A × B) ≃L[F] (A × B) := L.prodCongr (ContinuousLinearEquiv.refl F B)
  have hE : E (1, X) = (g.val, X) := by ext <;> simp [E, L]
  have hMap (z : A × B) : lieConjugationMap B (E z) = C (lieConjugationMap B z) := by
    change (g.val * z.1) * z.2.val * Ring.inverse (g.val * z.1) =
      g.val * (z.1 * z.2.val * Ring.inverse z.1) * ((g⁻¹ : Aˣ) : A)
    rw [Ring.inverse_mul (.inl g.isUnit), Ring.inverse_unit]
    simp only [mul_assoc]
  let d := lieConjugationDifferential B X
  let d' := (C : A →L[F] A).comp (d.comp (E.symm : A × B →L[F] A × B))
  refine ⟨d', ?_, C.surjective.comp ((surjective_lieConjugationDifferential B X hX).comp
    E.symm.surjective)⟩
  have hE' : E.symm (g.val, X) = (1, X) := by rw [← hE, E.symm_apply_apply]
  have hd : HasStrictFDerivAt (lieConjugationMap B) d (E.symm (g.val, X)) :=
    hE'.symm ▸ hasStrictFDerivAt_lieConjugationMap_one B X
  have h := (C : A →L[F] A).hasStrictFDerivAt.comp (g.val, X)
    (hd.comp (g.val, X) (E.symm : A × B →L[F] A × B).hasStrictFDerivAt)
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    change C (lieConjugationMap B (E.symm z)) = lieConjugationMap B z
    rw [← hMap, E.apply_symm_apply]

private theorem image_mem_nhds_of_surjective_strictFDeriv {B : Subalgebra F A}
    {f : A × B → A} {d : A × B →L[F] A} {x : A × B}
    (hd : HasStrictFDerivAt f d x) (hsurj : Surjective d) {V : Set (A × B)}
    (hV : V ∈ 𝓝 x) : f '' V ∈ 𝓝 (f x) := by
  let : CompleteSpace A := FiniteDimensional.complete F A
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let i (z : A) := x + s z
  have hi : HasStrictFDerivAt i s 0 := s.hasStrictFDerivAt.const_add x
  have hi0 : i 0 = x := by simp [i]
  have hcomp : HasStrictFDerivAt (f ∘ i) (ContinuousLinearEquiv.refl F A : A →L[F] A) 0 := by
    have hd' : HasStrictFDerivAt f d (i 0) := hi0.symm ▸ hd
    change HasStrictFDerivAt (fun z => f (i z)) (ContinuousLinearMap.id F A) 0
    rw [← hs]
    exact hd'.comp 0 hi
  have hpre : i ⁻¹' V ∈ 𝓝 0 :=
    hi.continuousAt.preimage_mem_nhds (hi0.symm ▸ hV)
  have hmap : map (f ∘ i) (𝓝 0) = 𝓝 (f x) := by
    rw [hcomp.map_nhds_eq_of_equiv, Function.comp_apply, hi0]
  rw [← hmap]
  exact mem_map.mpr (mem_of_superset hpre fun z hz => ⟨i z, hz, rfl⟩)

/-- Conjugation is an open map from the units times an open slice with surjective
conjugation differential. -/
def LieConjugationSliceSubmersionStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F] (A : Type v) [NormedRing A]
    [NormedAlgebra F A] [FiniteDimensional F A] (B : Subalgebra F A) (U : Set B), IsOpen U →
    (∀ X ∈ U, B.toSubmodule ⊔ LinearMap.range (adjointEndomorphism F X.val) = ⊤) →
    IsOpenMap (lieConjugationOnSlice B U)

theorem lieConjugationSliceSubmersion : LieConjugationSliceSubmersionStatement.{u, v} := by
  intro F _ _ A _ _ _ B U hU hspan
  let : CompleteSpace A := FiniteDimensional.complete F A
  let ι : Aˣ × U → A × B := Prod.map Units.val Subtype.val
  have hι : IsOpenEmbedding ι := Units.isOpenEmbedding_val.prodMap hU.isOpenEmbedding_subtypeVal
  have hcomp : lieConjugationOnSlice B U = lieConjugationMap B ∘ ι := by
    funext z
    exact (lieConjugationMap_unit B z.1 z.2.val).symm
  intro V hV
  rw [hcomp, image_comp, isOpen_iff_mem_nhds]
  rintro _ ⟨_, ⟨⟨g, X⟩, hz, rfl⟩, rfl⟩
  obtain ⟨d, hd, hsurj⟩ := lieConjugationMap_submersive B g X.val (hspan X.val X.property)
  exact image_mem_nhds_of_surjective_strictFDeriv hd hsurj
    ((hι.isOpenMap V hV).mem_nhds (mem_image_of_mem ι hz))

/-- The saturation of an open slice satisfying the submersion criterion is open. -/
theorem isOpen_conjugationSaturation_of_slice (B : Subalgebra F A) {U : Set B}
    (hU : IsOpen U)
    (hspan : ∀ X ∈ U, B.toSubmodule ⊔ LinearMap.range (adjointEndomorphism F X.val) = ⊤) :
    IsOpen (conjugationSaturation (Subtype.val '' U : Set A)) := by
  have hEq : range (lieConjugationOnSlice B U) = conjugationSaturation (Subtype.val '' U) := by
    ext y
    constructor
    · rintro ⟨⟨g, X⟩, rfl⟩
      exact mem_conjugationSaturation_iff.mpr
        ⟨g, X.val.val, ⟨X.val, X.property, rfl⟩, rfl⟩
    · rintro hy
      obtain ⟨g, _, ⟨X, hX, rfl⟩, rfl⟩ := mem_conjugationSaturation_iff.mp hy
      exact ⟨(g, ⟨X, hX⟩), rfl⟩
  rw [← hEq]
  exact (lieConjugationSliceSubmersion F A B U hU hspan).isOpen_range

end Langlands.HarmonicAnalysis.UnitConjugation
