import Langlands.AlgebraicGeometry.Picard.InfinitesimalFlatBaseChange
import Langlands.AlgebraicGeometry.Picard.InfinitesimalRingPullback
import Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Nilpotent surjections after tensor base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence

variable {k S R A B C : Type u}
  [CommRing k] [CommRing S] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k S] [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]

/-- Tensor base change preserves a surjective algebra map, without flatness. -/
lemma tensor_surjective (b : B →ₐ[k] C) (hb : Function.Surjective b) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k S) b) :=
  Algebra.TensorProduct.map_surjective (AlgHom.id k S) b Function.surjective_id hb

/-- Tensor base change preserves a nilpotent kernel of a surjective algebra map,
without flatness. -/
lemma tensor_ker_isNilpotent (b : B →ₐ[k] C) (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    IsNilpotent (RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom) := by
  change IsNilpotent (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k S) b))
  rw [Algebra.TensorProduct.lTensor_ker (A := S) b hb]
  exact hn.map (Ideal.mapHom
    (Algebra.TensorProduct.includeRight : B →ₐ[k] S ⊗[k] B))

/-- The spectrum of a surjection with nilpotent kernel is surjective on points. -/
lemma spec_surjective (p : R →+* A) (hp : Function.Surjective p)
    (hn : IsNilpotent (RingHom.ker p)) :
    Surjective (Spec.map (CommRingCat.ofHom p)) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap p)
  rw [← Set.range_eq_univ, range_comap_of_surjective A p hp]
  apply Set.eq_univ_of_forall
  intro x r hr
  obtain ⟨n, hn⟩ := hn
  have hpow := Ideal.pow_mem_pow hr n
  change (RingHom.ker p) ^ n = ⊥ at hn
  rw [hn] at hpow
  exact x.isPrime.mem_of_pow_mem n ((Ideal.mem_bot.mp hpow) ▸ x.asIdeal.zero_mem)

/-- The actual spectrum arrow of a nilpotent surjection, as a homeomorphism. -/
def specHomeomorph (p : R →+* A) (hp : Function.Surjective p)
    (hn : IsNilpotent (RingHom.ker p)) :
    Spec (CommRingCat.of A) ≃ₜ Spec (CommRingCat.of R) :=
  IsHomeomorph.homeomorph (Spec.map (CommRingCat.ofHom p))
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom p) hp).isClosedEmbedding.isEmbedding,
        (spec_surjective p hp hn).surj⟩)

@[simp]
lemma specHomeomorph_apply (p : R →+* A) (hp : Function.Surjective p)
    (hn : IsNilpotent (RingHom.ker p)) (x : Spec (CommRingCat.of A)) :
    specHomeomorph p hp hn x = Spec.map (CommRingCat.ofHom p) x := rfl

/-- The spectrum of the tensor map of a nilpotent surjection has the same topology. -/
def tensorSpecHomeomorph (b : B →ₐ[k] C) (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    Spec (CommRingCat.of (S ⊗[k] C)) ≃ₜ Spec (CommRingCat.of (S ⊗[k] B)) :=
  specHomeomorph (Algebra.TensorProduct.map (AlgHom.id k S) b).toRingHom
    (tensor_surjective b hb) (tensor_ker_isNilpotent b hb hn)

section Pullback

variable [Module.Flat k S]
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

include h

/-- The first projection of the tensor pullback remains surjective. -/
lemma tensor_fst_surjective (hb : Function.Surjective b) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k S) p) :=
  InfinitesimalRankOnePatching.fst_surjective _ _ _ _
    (InfinitesimalFlatBaseChange.isPullback_tensor p q a b h)
    (tensor_surjective b hb)

/-- The first projection of the tensor pullback has nilpotent kernel. -/
lemma tensor_fst_ker_isNilpotent (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    IsNilpotent (RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom) :=
  InfinitesimalRingPullback.ker_fst_isNilpotent _ _ _ _
    (InfinitesimalFlatBaseChange.isPullback_tensor p q a b h)
    (tensor_ker_isNilpotent b hb hn)

/-- The actual first spectrum arrow of the tensor pullback is a homeomorphism. -/
def tensorFstSpecHomeomorph (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    Spec (CommRingCat.of (S ⊗[k] A)) ≃ₜ Spec (CommRingCat.of (S ⊗[k] R)) :=
  specHomeomorph (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom
    (tensor_fst_surjective p q a b h hb) (tensor_fst_ker_isNilpotent p q a b h hb hn)

end Pullback

end Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence
