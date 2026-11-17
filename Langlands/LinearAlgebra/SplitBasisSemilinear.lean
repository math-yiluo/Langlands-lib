import Langlands.LinearAlgebra.SplitBasisDeterminant

/-! # Semilinear matrices of bases adapted to surjections -/

noncomputable section

universe u u' v v' w w' i k

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra.SplitBasis

variable {R : Type u} {R' : Type u'} [CommRing R] [CommRing R']
    {g : R →+* R'}
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W]
    {V' : Type v'} [AddCommGroup V'] [Module R' V']
    {W' : Type w'} [AddCommGroup W'] [Module R' W']
    (f : V →ₗ[R] W) (s : W →ₗ[R] V) (hs : ∀ x, f (s x) = x)
    (f' : V' →ₗ[R'] W') (t : W' →ₗ[R'] V') (ht : ∀ x, f' (t x) = x)
    (F : V →ₛₗ[g] V') (Q : W →ₛₗ[g] W')
    (hF : ∀ x, f' (F x) = Q (f x))

/-- The map induced on actual kernels by a semilinear commutative square. -/
def semilinearKernelMap : LinearMap.ker f →ₛₗ[g] LinearMap.ker f' :=
  (F.comp (LinearMap.ker f).subtype).codRestrict _ (fun x => by
    change f' (F x.val) = 0
    rw [hF, x.property, map_zero])

variable {ι : Type i} {κ : Type k}
    (b : Module.Basis ι R W) (c : Module.Basis κ R (LinearMap.ker f))
    (b' : Module.Basis ι R' W') (c' : Module.Basis κ R' (LinearMap.ker f'))

@[simp]
theorem adaptedBasis_apply_inl (j : ι) :
    adaptedBasis f s hs b c (Sum.inl j) = s (b j) := by
  change (splitEquiv f s hs).symm ((b.prod c) (Sum.inl j)) = _
  rw [Module.Basis.prod_apply]
  change s (b j) + 0 = _
  exact add_zero _

@[simp]
theorem adaptedBasis_apply_inr (j : κ) :
    adaptedBasis f s hs b c (Sum.inr j) = (c j).val := by
  change (splitEquiv f s hs).symm ((b.prod c) (Sum.inr j)) = _
  rw [Module.Basis.prod_apply]
  change s 0 + (c j).val = _
  rw [map_zero, zero_add]

/-- A semilinear square gives a triangular adapted-basis matrix, with arbitrary
and unrelated linear sections on the source and target. -/
theorem adaptedBasis_semilinearMatrix :
    (adaptedBasis f' t ht b' c').toMatrix
        (fun j => F (adaptedBasis f s hs b c j)) =
      Matrix.fromBlocks
        (b'.toMatrix (fun j => Q (b j))) 0
        (Matrix.of (fun j i => c'.repr
          (kernelProjection f' t ht (F (s (b i)))) j))
        (c'.toMatrix (fun j => semilinearKernelMap f f' F Q hF (c j))) := by
  ext i j
  rw [Module.Basis.toMatrix_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (b'.repr (f' (F (adaptedBasis f s hs b c (Sum.inl j))))) i = _
      rw [adaptedBasis_apply_inl, hF, hs]
      rfl
    | inr j =>
      change (b'.repr (f' (F (adaptedBasis f s hs b c (Sum.inr j))))) i = 0
      rw [adaptedBasis_apply_inr, hF, (c j).property, map_zero, map_zero,
        Finsupp.zero_apply]
  | inr i =>
    cases j with
    | inl j =>
      change (c'.repr (kernelProjection f' t ht
        (F (adaptedBasis f s hs b c (Sum.inl j))))) i = _
      rw [adaptedBasis_apply_inl]
      rfl
    | inr j =>
      change (c'.repr (kernelProjection f' t ht
        (F (adaptedBasis f s hs b c (Sum.inr j))))) i = _
      rw [adaptedBasis_apply_inr]
      apply congrArg (fun x => c'.repr x i)
      apply Subtype.ext
      change F (c j).val - t (f' (F (c j).val)) = F (c j).val
      rw [hF, (c j).property, map_zero, map_zero, sub_zero]

/-- The determinant sees only the quotient and kernel maps, independently of
all off-diagonal terms caused by the two choices of splitting. -/
theorem adaptedBasis_semilinearMatrix_det
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    ((adaptedBasis f' t ht b' c').toMatrix
        (fun j => F (adaptedBasis f s hs b c j))).det =
      (b'.toMatrix (fun j => Q (b j))).det *
        (c'.toMatrix (fun j => semilinearKernelMap f f' F Q hF (c j))).det := by
  rw [adaptedBasis_semilinearMatrix f s hs f' t ht F Q hF b c b' c',
    Matrix.det_fromBlocks_zero₁₂]

end Langlands.LinearAlgebra.SplitBasis
