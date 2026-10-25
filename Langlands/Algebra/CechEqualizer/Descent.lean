import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps

universe u

open TensorProduct

namespace Langlands.Algebra.CechEqualizer

section Spectrum

/-- A prime of `S` lies in the image of `Spec (S ⊗[R] T) → Spec S` as soon as its contraction to
`R` lies in the image of `Spec T → Spec R`. -/
lemma mem_range_comap_tensorProduct {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (x : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) x ∈
      Set.range (PrimeSpectrum.comap (algebraMap R T))) :
    x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T))) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, hz, -⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
    (f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (g := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T))) x y hy.symm
  refine ⟨(AlgebraicGeometry.pullbackSpecIso R S T).hom z, ?_⟩
  rw [← hz, ← AlgebraicGeometry.pullbackSpecIso_hom_fst' R S T]
  rfl

/-- If every prime of `A` contracts into an open subset `U` of `Spec R`, then finitely many
elements of `R`, whose basic open sets lie in `U`, generate the unit ideal of `A`. -/
lemma exists_sum_eq_one_of_isOpen {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    (h : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) P ∈ U) :
    ∃ (s : Finset R) (c : R → A), (∀ x ∈ s, ∀ P : PrimeSpectrum R, x ∉ P.asIdeal → P ∈ U) ∧
      ∑ x ∈ s, c x * algebraMap R A x = 1 := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hU.isClosed_compl
  have hJU : ∀ P : PrimeSpectrum R, ¬ (J : Set R) ⊆ P.asIdeal → P ∈ U := by
    intro P hP
    by_contra hPU
    have : P ∈ PrimeSpectrum.zeroLocus (J : Set R) := hJ ▸ hPU
    exact hP ((PrimeSpectrum.mem_zeroLocus _ _).mp this)
  have htop : J.map (algebraMap R A) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hP : PrimeSpectrum.comap (algebraMap R A) ⟨M, hM.isPrime⟩ ∉ Uᶜ := fun h' =>
      h' (h ⟨M, hM.isPrime⟩)
    rw [hJ, PrimeSpectrum.mem_zeroLocus] at hP
    exact hP (Ideal.map_le_iff_le_comap.mp hle)
  have h1 : (1 : A) ∈ Submodule.span A (algebraMap R A '' (J : Set R)) := by
    change (1 : A) ∈ J.map (algebraMap R A)
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨l, hl, hsum⟩ := (Finsupp.mem_span_image_iff_linearCombination A).mp h1
  refine ⟨l.support, l, fun x hx P hxP => hJU P fun hJP => hxP (hJP (hl hx)), ?_⟩
  rw [← hsum, Finsupp.linearCombination_apply, Finsupp.sum]
  rfl

/-- Faithful flatness of a base change `A ⊗[R] B` over `A`, from finitely many elements of `R`
generating the unit ideal of `A` whose basic open sets lie in the image of `Spec B`. -/
lemma faithfullyFlat_of_sum_eq_one {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B] (s : Finset R) (c : R → A)
    (hs : ∀ x ∈ s, ∀ P : PrimeSpectrum R, x ∉ P.asIdeal →
      P ∈ Set.range (PrimeSpectrum.comap (algebraMap R B)))
    (hc : ∑ x ∈ s, c x * algebraMap R A x = 1) : Module.FaithfullyFlat A (A ⊗[R] B) := by
  refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
  obtain ⟨x, hx, hxP⟩ : ∃ x ∈ s, algebraMap R A x ∉ P.asIdeal := by
    by_contra! H
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      (hc ▸ Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ (H x hx)))
  exact mem_range_comap_tensorProduct P (hs x hx _ hxP)

end Spectrum

section Maps

variable {R A₀ A B : Type*} [CommRing R] [CommRing A₀] [CommRing A] [CommRing B]
  [Algebra R A₀] [Algebra R A] [Algebra A₀ A] [IsScalarTower R A₀ A] [Algebra R B]

/-- Base change along an injective map `A₀ → A` is injective on a flat module. -/
lemma map_ofId_injective [Module.Flat R B] (h : Function.Injective (algebraMap A₀ A)) :
    Function.Injective (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B)) := by
  have : ⇑(Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B)) =
      ⇑(LinearMap.rTensor B ((Algebra.ofId A₀ A).toLinearMap.restrictScalars R)) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [this]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ h

lemma cancelBaseChange_tmul_eq_smul (a : A) (z : A₀ ⊗[R] B) :
    Algebra.TensorProduct.cancelBaseChange R A₀ A A B (a ⊗ₜ z) =
      a • Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B) z := by
  induction z using TensorProduct.inductionOn with
  | tmul s b =>
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  | add x y hx hy => rw [tmul_add, map_add, hx, hy, map_add, smul_add]

/-- Elements of `A ⊗[R] B` whose left coefficients come from `A₀` come from `A₀ ⊗[R] B`. -/
lemma sum_tmul_mem_range (S : Finset (A × B))
    (h : ∀ i ∈ S, i.1 ∈ Set.range (algebraMap A₀ A)) :
    ∑ i ∈ S, i.1 ⊗ₜ[R] i.2 ∈
      (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B)).range :=
  Subalgebra.sum_mem _ fun i hi => by
    obtain ⟨a, ha⟩ := h i hi
    refine ⟨a ⊗ₜ i.2, ?_⟩
    change Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B) (a ⊗ₜ i.2) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.ofId_apply, ha]
    rfl

/-- An `A₀`-algebra map out of `A₀ ⊗[R] B` factors through an injective `A₀`-algebra map `ι`
as soon as it sends the elements `1 ⊗ g`, for generators `g` of `B`, into the range of `ι`. -/
lemma exists_algHom_comp_eq {D E : Type*} [CommRing D] [CommRing E] [Algebra A₀ D] [Algebra A₀ E]
    (ι : D →ₐ[A₀] E) (hι : Function.Injective ι) (Ψ : A₀ ⊗[R] B →ₐ[A₀] E) (G : Set B)
    (hG : Algebra.adjoin R G = ⊤) (hΨ : ∀ g ∈ G, Ψ (1 ⊗ₜ g) ∈ ι.range) :
    ∃ φ : A₀ ⊗[R] B →ₐ[A₀] D, ∀ x, ι (φ x) = Ψ x := by
  have h : ∀ x, Ψ x ∈ ι.range := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : a ⊗ₜ[R] b = a • ((1 : A₀) ⊗ₜ[R] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hab, map_smul]
      refine Subalgebra.smul_mem _ ?_ a
      clear hab
      have hb : b ∈ Algebra.adjoin R G := hG ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem g hg => exact hΨ g hg
      | algebraMap r =>
        have : (1 : A₀) ⊗ₜ[R] algebraMap R B r = algebraMap A₀ (A₀ ⊗[R] B) (algebraMap R A₀ r) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            Algebra.algebraMap_eq_smul_one (A := B), Algebra.algebraMap_eq_smul_one (A := A₀)]
          exact (TensorProduct.smul_tmul r (1 : A₀) (1 : B)).symm
        rw [this, AlgHom.commutes]
        exact Subalgebra.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [tmul_add, map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy =>
        rw [← mul_one (1 : A₀), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
        exact mul_mem hx hy
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  refine ⟨(AlgEquiv.ofInjective ι hι).symm.toAlgHom.comp (Ψ.codRestrict ι.range h), fun x => ?_⟩
  have := congrArg Subtype.val
    ((AlgEquiv.ofInjective ι hι).apply_symm_apply (Ψ.codRestrict ι.range h x))
  rw [AlgEquiv.ofInjective_apply] at this
  exact this

end Maps

end Langlands.Algebra.CechEqualizer
