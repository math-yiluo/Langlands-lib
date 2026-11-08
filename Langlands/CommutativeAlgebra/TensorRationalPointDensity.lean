import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# Rational points avoiding the vanishing loci of tensor elements

Given rational points on every nonzero geometrically reduced finite type `k`-algebra, a nonzero
element of `K ⊗[k] B` and a nonzero element of `K' ⊗[k] B` (for field extensions `K`, `K'` of `k`
and a geometrically reduced finite type domain `B`) both stay nonzero after specializing along
some `k`-algebra map `B → k`.
-/

open TensorProduct

namespace Langlands.CommutativeAlgebra.TensorRationalPointDensity

universe u

/-- Specializing along a `k`-algebra map `g : B → k` acts on the coordinates of `K ⊗[k] B` in a
`k`-basis of `K` by applying `g`. -/
theorem equivFinsuppOfBasisLeft_map {k K B ι : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing B] [Algebra k B] [DecidableEq ι] (𝒞 : Module.Basis ι k K) (g : B →ₐ[k] k)
    (x : K ⊗[k] B) (i : ι) :
    equivFinsuppOfBasisLeft 𝒞 (Algebra.TensorProduct.map (AlgHom.id k K) g x) i =
      g (equivFinsuppOfBasisLeft 𝒞 x i) := by
  induction x with
  | tmul c b => simp
  | add x y hx hy => simp [hx, hy]

/-- For a nonzero `f ∈ K ⊗[k] B` there is a nonzero `b ∈ B` such that `f` stays nonzero after
specializing along every `k`-algebra map `g : B → k` with `g b ≠ 0`. -/
theorem exists_ne_zero_forall_map_ne_zero {k K B : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing B] [Algebra k B] (f : K ⊗[k] B) (hf : f ≠ 0) :
    ∃ b : B, b ≠ 0 ∧ ∀ g : B →ₐ[k] k, g b ≠ 0 →
      Algebra.TensorProduct.map (AlgHom.id k K) g f ≠ 0 := by
  classical
  let 𝒞 := Module.Basis.ofVectorSpace k K
  have hf' : equivFinsuppOfBasisLeft 𝒞 f ≠ 0 :=
    (map_ne_zero_iff _ (LinearEquiv.injective _)).mpr hf
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hf'
  refine ⟨_, hi, fun g hg h => hg ?_⟩
  rw [← equivFinsuppOfBasisLeft_map 𝒞 g f i, h, map_zero, Finsupp.zero_apply]

/-- If every nonzero geometrically reduced finite type `k`-algebra has a `k`-point, then for a
geometrically reduced finite type domain `B`, field extensions `K` and `K'` of `k`, and nonzero
`f ∈ K ⊗[k] B`, `f' ∈ K' ⊗[k] B`, some `k`-point `g` of `B` keeps both `f` and `f'` nonzero. -/
theorem exists_algHom_tensor_ne_zero {k : Type u} [Field k]
    (hrat : ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] [Nontrivial R]
      [Algebra.IsGeometricallyReduced k R], Nonempty (R →ₐ[k] k))
    {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsDomain B]
    [Algebra.IsGeometricallyReduced k B] {K K' : Type*} [Field K] [Algebra k K] [Field K']
    [Algebra k K'] (f : K ⊗[k] B) (hf : f ≠ 0) (f' : K' ⊗[k] B) (hf' : f' ≠ 0) :
    ∃ g : B →ₐ[k] k, Algebra.TensorProduct.map (AlgHom.id k K) g f ≠ 0 ∧
      Algebra.TensorProduct.map (AlgHom.id k K') g f' ≠ 0 := by
  obtain ⟨b, hb, H⟩ := exists_ne_zero_forall_map_ne_zero f hf
  obtain ⟨b', hb', H'⟩ := exists_ne_zero_forall_map_ne_zero f' hf'
  have hbb : b * b' ≠ 0 := mul_ne_zero hb hb'
  have : IsDomain (Localization.Away (b * b')) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hbb)
  have := Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof.isGeometricallyReduced_localization (k := k) (Submonoid.powers (b * b'))
  obtain ⟨φ⟩ := hrat (Localization.Away (b * b'))
  let g : B →ₐ[k] k := φ.comp (IsScalarTower.toAlgHom k B (Localization.Away (b * b')))
  have hg : g (b * b') ≠ 0 := by
    have hu : IsUnit (algebraMap B (Localization.Away (b * b')) (b * b')) :=
      IsLocalization.Away.algebraMap_isUnit (b * b')
    exact (hu.map φ).ne_zero
  rw [map_mul] at hg
  exact ⟨g, H g (left_ne_zero_of_mul hg), H' g (right_ne_zero_of_mul hg)⟩

end Langlands.CommutativeAlgebra.TensorRationalPointDensity
