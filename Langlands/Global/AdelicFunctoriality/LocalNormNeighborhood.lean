import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Local norm groups are neighborhoods of one -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open Filter Topology NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField NumberField.LiesOver FiniteExtension InfiniteExtension

universe u v

/-- The image of a monoid homomorphism into the units of `F` is a neighborhood of `1`. -/
def RangeMemNhdsOne {F M : Type*} [Monoid F] [TopologicalSpace F] [Monoid M]
    (f : M →* Fˣ) : Prop :=
  Set.range f ∈ 𝓝 (1 : Fˣ)

/-- A unit-valued homomorphism from a group whose image is a neighborhood of `1` has open
image. -/
theorem RangeMemNhdsOne.isOpen_range {F M : Type*} [Monoid F] [TopologicalSpace F]
    [ContinuousMul F] [Group M] {f : M →* Fˣ} (h : RangeMemNhdsOne f) :
    IsOpen (Set.range f) := by
  unfold RangeMemNhdsOne at h
  rw [← MonoidHom.coe_range] at h ⊢
  exact f.range.isOpen_of_mem_nhds h

/-- Over a complete nontrivially normed field of characteristic zero, every unit close to `1`
is an `n`-th power of a unit. -/
theorem range_pow_mem_nhds_one {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] {n : ℕ} (hn : n ≠ 0) :
    Set.range (fun x : Fˣ => x ^ n) ∈ 𝓝 (1 : Fˣ) := by
  have hderiv : HasStrictDerivAt (fun x : F => x ^ n) ((n : F) * 1 ^ (n - 1)) 1 :=
    hasStrictDerivAt_pow n 1
  have hne : (n : F) * 1 ^ (n - 1) ≠ 0 := by simpa using hn
  have hmap : map (fun x : F => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hderiv.map_nhds_eq hne
  have himage : (fun x : F => x ^ n) '' {x : F | x ≠ 0} ∈ 𝓝 (1 : F) := by
    rw [← hmap]
    exact image_mem_map (isOpen_ne.mem_nhds one_ne_zero)
  have hpre : (Units.val : Fˣ → F) ⁻¹' ((fun x : F => x ^ n) '' {x : F | x ≠ 0}) ∈
      𝓝 (1 : Fˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by rw [Units.val_one]; exact himage)
  refine mem_of_superset hpre ?_
  rintro u ⟨x, hx, hxu⟩
  exact ⟨Units.mk0 x hx, Units.ext (by simpa using hxu)⟩

section Finite

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- At a finite place, the local norms of units form a neighborhood of `1`. -/
theorem range_finiteLocalNorm_mem_nhds (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal] :
    Set.range (Units.map (FiniteExtension.localNorm p q)) ∈ 𝓝 (1 : (p.adicCompletion K)ˣ) := by
  let _ : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField (p.adicCompletion K) (WithZero (Multiplicative ℤ))
  have : CharZero (p.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (p.adicCompletion K)).injective
  have hd : Module.finrank (p.adicCompletion K) (q.adicCompletion L) ≠ 0 :=
    Module.finrank_pos.ne'
  refine mem_of_superset (range_pow_mem_nhds_one hd) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨Units.map (FiniteExtension.completionMap p q).toMonoidHom x, Units.ext ?_⟩
  simp

/-- At a finite place, the local norm group of units is open. -/
theorem isOpen_range_finiteLocalNorm (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal] :
    IsOpen (Set.range (Units.map (FiniteExtension.localNorm p q))) :=
  RangeMemNhdsOne.isOpen_range (range_finiteLocalNorm_mem_nhds p q)

end Finite

section Infinite

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

private theorem infinitePlace_nontrivial (p : InfinitePlace K) :
    ∃ x : p.Completion, 1 < ‖x‖ := by
  refine ⟨2, ?_⟩
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding p).norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.extensionEmbedding p)) (2 : p.Completion)
  rw [← h]
  norm_num only [map_ofNat, Complex.norm_ofNat]

/-- At an infinite place, the local norms of units form a neighborhood of `1`. -/
theorem range_infiniteLocalNorm_mem_nhds [NumberField K] (p : InfinitePlace K)
    (q : InfinitePlace L) [q.LiesOver p] :
    Set.range (Units.map (InfiniteExtension.localNorm p q)) ∈ 𝓝 (1 : p.Completionˣ) := by
  let _ : NontriviallyNormedField p.Completion :=
    { (inferInstance : NormedField p.Completion) with
      non_trivial := infinitePlace_nontrivial p }
  have : CharZero p.Completion :=
    charZero_of_injective_algebraMap (algebraMap K p.Completion).injective
  have hd : Module.finrank p.Completion q.Completion ≠ 0 :=
    Module.finrank_pos.ne'
  refine mem_of_superset (range_pow_mem_nhds_one hd) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨Units.map (NumberField.LiesOver.completionMap (v := p) (w := q)).toMonoidHom x,
    Units.ext ?_⟩
  simp

/-- At an infinite place, the local norm group of units is open. -/
theorem isOpen_range_infiniteLocalNorm [NumberField K] (p : InfinitePlace K)
    (q : InfinitePlace L) [q.LiesOver p] :
    IsOpen (Set.range (Units.map (InfiniteExtension.localNorm p q))) :=
  RangeMemNhdsOne.isOpen_range (range_infiniteLocalNorm_mem_nhds p q)

end Infinite

end Langlands.Global.AdelicFunctoriality
