import Langlands.Global.AdelicProjectiveRationalImageStatement
import Langlands.Global.AdelicProjectiveRationalDensityProof
import Langlands.Global.GlobalPlaceTopologyFacts
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The rational adelic projective image in positive dimension -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem field_point_changeRing_injective (F A : Type u) [Field F] [Field A]
    [Algebra F A] (X : Over (Spec (CommRingCat.of F))) :
    Function.Injective (RingPoint.changeRing (X := X) (Algebra.ofId F A)) := by
  have hff : (algebraMap F A).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap F A))).mpr hff
  let : Flat (Spec.algebraMap F A) := h.1
  let : Surjective (Spec.algebraMap F A) := h.2
  let : Epi (Spec.algebraMap F A) := Flat.epi_of_flat_of_surjective _
  intro p q hpq
  apply RingPoint.ext
  apply (cancel_epi (Spec.algebraMap F A)).mp
  exact congrArg (fun r => r.left) hpq

private theorem projectiveAffinePoint_injective (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1)) :
    Function.Injective (projectiveAffinePoint R A n j) := by
  intro a b hab
  have h := congrArg (fun p => p.left) hab
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval a).toRingHom) ≫
      (projectiveAffineChart R n j).left =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval b).toRingHom) ≫
      (projectiveAffineChart R n j).left at h
  have he := Spec.map_injective ((cancel_mono (projectiveAffineChart R n j).left).mp h)
  funext i
  simpa using congrArg (fun f => f.hom (MvPolynomial.X i)) he

private theorem projectiveRingPoint_nontrivial (F : Type u) [Field F]
    (n : ℕ) (hn : 0 < n) :
    Nontrivial (RingPoint F (projectivePointScheme F n) F) := by
  let : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hi⟩ := exists_ne (0 : Fin (n + 1))
  let : Nonempty {i : Fin (n + 1) // i ≠ 0} := ⟨⟨i, hi⟩⟩
  exact (projectiveAffinePoint_injective F F n 0).nontrivial

private theorem not_surjective_pi_of_injective {X ι : Type*} {A : ι → Type*}
    [Nontrivial X] [Nontrivial ι] (f : X → ∀ i, A i)
    (hf : ∀ i, Function.Injective (fun x => f x i)) :
    ¬ Function.Surjective f := by
  classical
  obtain ⟨x₀, x₁, hxx⟩ := exists_pair_ne X
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let z (k : ι) := if k = i then f x₀ k else f x₁ k
  intro hs
  obtain ⟨x, hx⟩ := hs z
  have hxi : x = x₀ := hf i (by simpa [z] using congrFun hx i)
  have hxj : x = x₁ := hf j (by simpa [z, hij.symm] using congrFun hx j)
  exact hxx (hxi.symm.trans hxj)

private theorem preperfect_image_of_continuous_injective {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [PerfectSpace A]
    (f : A → X) (hc : Continuous f) (hi : Function.Injective f) :
    Preperfect (Set.range f) := by
  rw [preperfect_iff_nhds]
  rintro _ ⟨a, rfl⟩ U hU
  have hN : f ⁻¹' U ∈ 𝓝 a := hc.continuousAt hU
  obtain ⟨b, hb, hba⟩ :=
    preperfect_iff_nhds.mp (PerfectSpace.univ_preperfect (α := A)) a (Set.mem_univ _)
      (f ⁻¹' U) hN
  exact ⟨f b, ⟨hb.1, ⟨b, rfl⟩⟩, fun h => hba (hi h)⟩

private theorem perfectSpace_pi_of_factor {ι : Type*} (A : ι → Type*)
    [∀ i, TopologicalSpace (A i)] (i : ι) [PerfectSpace (A i)] :
    PerfectSpace (∀ i, A i) := by
  classical
  constructor
  intro x _
  let f : A i → ∀ j, A j := fun a => Function.update x i a
  have hc : Continuous f := continuous_const.update i continuous_id
  have hi : Function.Injective f := by
    intro a b hab
    simpa [f] using congrFun hab i
  have h := preperfect_image_of_continuous_injective f hc hi
  have hx : x ∈ Set.range f := ⟨x i, Function.update_eq_self i x⟩
  exact (h x hx).mono (Filter.principal_mono.mpr (Set.subset_univ _))

private theorem projectiveRingPoint_perfectSpace (R A : Type u)
    [CommRing R] [Field A] [Algebra R A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsOpenUnits A] [PerfectSpace A]
    (n : ℕ) (hn : 0 < n) :
    letI := schemePointTopology R (projectivePointScheme R n) A
    PerfectSpace (RingPoint R (projectivePointScheme R n) A) := by
  let := schemePointTopology R (projectivePointScheme R n) A
  let : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  constructor
  intro p _
  obtain ⟨j, a, rfl⟩ := exists_projectiveAffinePoint R A n p
  obtain ⟨i, hi⟩ := exists_ne j
  let := perfectSpace_pi_of_factor (fun _ : {i : Fin (n + 1) // i ≠ j} => A) ⟨i, hi⟩
  have h := preperfect_image_of_continuous_injective (projectiveAffinePoint R A n j)
    (isOpenEmbedding_projectiveAffinePoint R A n j).continuous
    (projectiveAffinePoint_injective R A n j)
  exact (h _ ⟨a, rfl⟩).mono (Filter.principal_mono.mpr (Set.subset_univ _))

private theorem dense_not_closed_not_discrete {X Y : Type*}
    [Nonempty X] [TopologicalSpace Y] [T1Space Y] [PerfectSpace Y]
    (f : X → Y) (hd : DenseRange f) (hs : ¬ Function.Surjective f) :
    ¬ IsClosed (Set.range f) ∧ ¬ IsDiscrete (Set.range f) := by
  constructor
  · intro hc
    apply hs
    rw [← Set.range_eq_univ, ← hc.closure_eq]
    exact hd.closure_range
  · intro hdis
    have hp : Preperfect (Set.range f) := preperfect_iff_perfect_closure.mpr
      (hd.closure_range.symm ▸ PerfectSpace.univ_perfect Y)
    obtain ⟨x⟩ := ‹Nonempty X›
    have ha := hp (f x) ⟨x, rfl⟩
    have hb := isDiscrete_iff_nhdsNE.mp hdis (f x) ⟨x, rfl⟩
    exact ha.ne hb

private theorem changeRing_twice {R A B D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D]
    {X : Over (Spec (CommRingCat.of R))} (p : RingPoint R X A)
    (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    (p.changeRing f).changeRing g = p.changeRing (g.comp f) := by
  change ringTestMap R g ≫ (ringTestMap R f ≫ p) =
    ringTestMap R (g.comp f) ≫ p
  rw [ringTestMap_comp]
  exact (Category.assoc _ _ _).symm

private theorem perfectSpace_of_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [PerfectSpace A] (e : A ≃ₜ B) :
    PerfectSpace B := by
  constructor
  simpa only [Set.range_eq_univ.mpr e.surjective] using
    preperfect_image_of_continuous_injective e e.continuous e.injective

private theorem perfectSpace_prod_right (A B : Type*)
    [TopologicalSpace A] [TopologicalSpace B] [PerfectSpace B] :
    PerfectSpace (A × B) := by
  constructor
  rintro ⟨a, b⟩ _
  have h := preperfect_image_of_continuous_injective (fun y : B => (a, y))
    (continuous_const.prodMk continuous_id) (fun _ _ he => congrArg Prod.snd he)
  exact (h (a, b) ⟨b, rfl⟩).mono (Filter.principal_mono.mpr (Set.subset_univ _))

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

private theorem curveCompletion_perfectSpace_image (v : AlgebraicCurve.Place k F) :
    PerfectSpace (curvePlaceCompletion v) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let := Valued.toNontriviallyNormedField (curvePlaceCompletion v)
    (WithZero (Multiplicative ℤ))
  infer_instance

end Curve

/-- In positive dimension, the actual rational projective image over a global
function field is proper, nonclosed and nondiscrete. -/
theorem curvePlaceProjectiveRationalImage :
    CurvePlaceProjectiveRationalImageStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S n hn
  classical
  let Y := projectivePointScheme F n
  let := curvePlaceProjectiveAdelePointTopology k F S n
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let : Infinite (AlgebraicCurve.Place k F) := functionField_places_infinite k F
  let : Nontrivial (RingPoint F Y F) := projectiveRingPoint_nontrivial F n hn
  let (v : AlgebraicCurve.Place k F) : PerfectSpace (curvePlaceCompletion v) :=
    curveCompletion_perfectSpace_image k F v
  let (v : AlgebraicCurve.Place k F) : PerfectSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    projectiveRingPoint_perfectSpace F (curvePlaceCompletion v) n hn
  let v₀ : AlgebraicCurve.Place k F := Classical.ofNonempty
  let := perfectSpace_pi_of_factor
    (fun v : AlgebraicCurve.Place k F => RingPoint F Y (curvePlaceCompletion v)) v₀
  let d : RingPoint F Y F → CurvePlaceAdelePoints k F Y :=
    fun p => p.changeRing (Algebra.ofId F (CurvePlaceAdeleRing k F))
  let e := (curvePlaceProjectiveComparison k F S n).1.homeomorph
  let : T2Space (CurvePlaceAdelePoints k F Y) :=
    (curvePlaceProjectiveComparison k F S n).2.2
  let : PerfectSpace (CurvePlaceAdelePoints k F Y) :=
    perfectSpace_of_homeomorph e.symm
  have hi (v : AlgebraicCurve.Place k F) :
      Function.Injective (fun p => e (d p) v) := by
    convert field_point_changeRing_injective F (curvePlaceCompletion v) Y using 1
    funext p
    change (p.changeRing (Algebra.ofId F (CurvePlaceAdeleRing k F))).changeRing
      (curvePlaceAdeleProjection k F v) = _
    rw [changeRing_twice, Algebra.comp_ofId]
  have hs : ¬ Function.Surjective d := by
    intro h
    exact not_surjective_pi_of_injective (e ∘ d) hi (e.surjective.comp h)
  exact ⟨hs, dense_not_closed_not_discrete d
    (curvePlaceProjectiveRationalDensity k F S n) hs⟩

section NumberField

variable (K : Type u) [Field K] [NumberField K]

private theorem finiteCompletion_perfectSpace_image (v : FinitePlace K) :
    PerfectSpace (FiniteCompletion K v) := by
  let := Valued.toNontriviallyNormedField (FiniteCompletion K v)
    (WithZero (Multiplicative ℤ))
  infer_instance

end NumberField

/-- The rational projective image over a number field is proper, nonclosed and
nondiscrete, retaining every infinite and finite local factor. -/
theorem numberFieldProjectiveRationalImage :
    NumberFieldProjectiveRationalImageStatement.{u} := by
  intro K _ _ S n hn
  classical
  let Y := projectivePointScheme K n
  let := numberFieldProjectiveAdelePointTopology K S n
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let : Infinite (FinitePlace K) := numberField_finitePlaces_infinite K
  let : Nontrivial (RingPoint K Y K) := projectiveRingPoint_nontrivial K n hn
  let (v : FinitePlace K) : PerfectSpace (FiniteCompletion K v) :=
    finiteCompletion_perfectSpace_image K v
  let (v : FinitePlace K) : PerfectSpace (RingPoint K Y (FiniteCompletion K v)) :=
    projectiveRingPoint_perfectSpace K (FiniteCompletion K v) n hn
  let v₀ : FinitePlace K := Classical.ofNonempty
  let := perfectSpace_pi_of_factor
    (fun v : FinitePlace K => RingPoint K Y (FiniteCompletion K v)) v₀
  let := perfectSpace_prod_right
    (∀ v : InfinitePlace K, RingPoint K Y (InfiniteCompletion K v))
    (∀ v : FinitePlace K, RingPoint K Y (FiniteCompletion K v))
  let d : RingPoint K Y K → NumberFieldAdelePoints K Y :=
    fun p => p.changeRing (Algebra.ofId K (Adeles K))
  let e := (numberFieldProjectiveComparison K S n).1.homeomorph
  let : T2Space (NumberFieldAdelePoints K Y) :=
    (numberFieldProjectiveComparison K S n).2.2
  let : PerfectSpace (NumberFieldAdelePoints K Y) :=
    perfectSpace_of_homeomorph e.symm
  let : Nonempty (∀ v : InfinitePlace K, RingPoint K Y (InfiniteCompletion K v)) :=
    ⟨fun v => (Classical.ofNonempty : RingPoint K Y K).changeRing
      (Algebra.ofId K (InfiniteCompletion K v))⟩
  have hi (v : FinitePlace K) :
      Function.Injective (fun p => (e (d p)).2 v) := by
    convert field_point_changeRing_injective K (FiniteCompletion K v) Y using 1
    funext p
    change (p.changeRing (Algebra.ofId K (Adeles K))).changeRing
      (numberFieldFiniteAdeleProjection K v) = _
    rw [changeRing_twice, Algebra.comp_ofId]
  have hs : ¬ Function.Surjective d := by
    intro h
    exact not_surjective_pi_of_injective (fun p => (e (d p)).2) hi
      (Prod.snd_surjective.comp (e.surjective.comp h))
  exact ⟨hs, dense_not_closed_not_discrete d
    (numberFieldProjectiveRationalDensity K S n) hs⟩

/-- The proper-subset, nonclosedness and nondiscreteness conclusions of Conrad
Example 4.3 for actual adelic projective points in both characteristics. -/
theorem adelicProjectiveRationalImage :
    AdelicProjectiveRationalImageStatement.{u} :=
  ⟨curvePlaceProjectiveRationalImage, numberFieldProjectiveRationalImage⟩

end Langlands.Global
