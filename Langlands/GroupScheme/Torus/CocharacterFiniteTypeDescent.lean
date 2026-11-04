import Langlands.GroupScheme.Commutative.Frobenius
import Langlands.GroupScheme.Torus.CocharacterInseparableDescent

/-! # Bounded purely inseparable descent of multiplicative points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CocharacterDatum

variable {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {Λ : Type u} [AddCommGroup Λ]

/-- Multiplicative group-algebra-valued points form a subgroup. -/
def multiplicativePoints (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    (S : Type u) [CommRing S] [Algebra k S] (Λ : Type u) [AddCommGroup Λ] :
    Subgroup (Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) where
  carrier := IsMult
  one_mem' := isMult_one
  mul_mem' := IsMult.mul
  inv_mem' := IsMult.inv

/-- Extension of coefficients on the subgroup of multiplicative points. -/
def multiplicativeCoeffMap {S S' : Type u} [CommRing S] [Algebra k S]
    [CommRing S'] [Algebra k S'] (f : S →ₐ[k] S') :
    multiplicativePoints Z S Λ →* multiplicativePoints Z S' Λ where
  toFun x := ⟨coeffMap f x.val, x.property.coeff_map f⟩
  map_one' := Subtype.ext (map_one (coeffMap f))
  map_mul' x y := Subtype.ext (map_mul (coeffMap f) x.val y.val)

section Descent

variable [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]
    [IsAddTorsionFree Λ]
    (p e : ℕ) [ExpChar k p]
    {F L : Type u} [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ (algebraMap F L).range)

include p e hL

/-- The two tensor-valued images of a multiplicative point agree when the
extension has bounded purely inseparable exponent. -/
theorem IsMult.coeffMap_tensor_eq
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsMult x) :
    coeffMap ((Algebra.TensorProduct.includeLeft :
        L →ₐ[F] L ⊗[F] L).restrictScalars k) x =
      coeffMap ((Algebra.TensorProduct.includeRight :
        L →ₐ[F] L ⊗[F] L).restrictScalars k) x := by
  have : ExpChar F p :=
    expChar_of_injective_algebraMap (algebraMap k F).injective p
  let i₁ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeLeft : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let i₂ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let φ : L ⊗[F] L →ₐ[k] L ⊗[F] L :=
    ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
      (Algebra.TensorProduct.lmul' F)).restrictScalars k
  let g := AddMonoidAlgebra.mapAlgHom Λ φ
  have hg : ∀ a, a ^ p ^ e = g a ^ p ^ e :=
    CocharacterDescent.pow_eq_pow_mapAlgHom_includeRight_lmul' p e
      (fun ℓ => by obtain ⟨c, hc⟩ := hL ℓ; exact ⟨c, hc⟩)
  have hφ₁ : φ.comp i₁ = i₂ := by ext ℓ; simp [φ, i₁, i₂]
  have hφ₂ : φ.comp i₂ = i₂ := by ext ℓ; simp [φ, i₂]
  have hgcomp (f : L →ₐ[k] L ⊗[F] L) :
      Lie.affineMap Z.toGrp g (coeffMap f x) = coeffMap (φ.comp f) x := by
    have h : g.comp (AddMonoidAlgebra.mapAlgHom Λ f) =
        AddMonoidAlgebra.mapAlgHom Λ (φ.comp f) := by
      apply AlgHom.ext
      intro a
      ext t
      simp [g]
    rw [coeffMap, coeffMap, ← Lie.affineMap_comp, h]
  let v := coeffMap i₁ x * (coeffMap i₂ x)⁻¹
  have hgv : Lie.affineMap Z.toGrp g v = 1 := by
    rw [map_mul, map_inv, hgcomp, hgcomp, hφ₁, hφ₂, mul_inv_cancel]
  have hvpow : v ^ p ^ e = 1 := by
    rw [CommutativeFrobenius.affinePoints_pow_eq Z p e g hg v, hgv, one_pow]
  have hmult : IsMult v := (hx.coeff_map i₁).mul (hx.coeff_map i₂).inv
  have hv : v = 1 := by
    apply expMap_nsmul_injective (Z := Z) (S := L ⊗[F] L) (Λ := Λ)
      (pow_ne_zero e (expChar_ne_zero k p))
    rw [hmult.expMap_nsmul, hvpow, map_one]
  exact mul_inv_eq_one.mp hv

/-- A multiplicative point descends as the same point, with its original
coefficients recovered after extension. -/
theorem IsMult.exists_coeffMap_eq_of_pow_mem_range
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsMult x) :
    ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ),
      IsMult y ∧ coeffMap (IsScalarTower.toAlgHom k F L) y = x := by
  let f := IsScalarTower.toAlgHom k F L
  have hf : Function.Injective f := (algebraMap F L).injective
  have hcoord := congrArg coord (hx.coeffMap_tensor_eq p e hL)
  obtain ⟨y, hy⟩ := exists_affineMap_eq
    (AddMonoidAlgebra.mapAlgHom Λ f) (mapAlgHom_injective f hf) x (fun b => by
      have hb := congrArg (fun ψ => ψ.hom b) hcoord
      simp only [coord_affineMap] at hb
      obtain ⟨z, hz⟩ :=
        CocharacterDescent.exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight
          (F := F) (L := L) (Λ := Λ) ((coord x).hom b) (by
            ext t
            simpa using congrArg (fun a => a.coeff t) hb)
      refine ⟨z, ?_⟩
      rw [← hz]
      ext t
      simp [f])
  refine ⟨y, ?_, hy⟩
  apply IsMult.of_coeff_map f hf
  change IsMult (Lie.affineMap Z.toGrp _ y)
  rwa [hy]

/-- Extension of coefficients is an equivalence on multiplicative points
through a bounded purely inseparable field extension. -/
def multiplicativePointsEquivOfPowMemRange :
    multiplicativePoints Z F Λ ≃* multiplicativePoints Z L Λ :=
  MulEquiv.ofBijective (multiplicativeCoeffMap (Z := Z) (Λ := Λ)
    (IsScalarTower.toAlgHom k F L)) ⟨by
      intro x y h
      apply Subtype.ext
      apply affineMap_injective
        (AddMonoidAlgebra.mapAlgHom Λ (IsScalarTower.toAlgHom k F L))
        (mapAlgHom_injective _ (algebraMap F L).injective)
      exact congrArg Subtype.val h, by
      intro x
      obtain ⟨y, hy, heq⟩ := x.property.exists_coeffMap_eq_of_pow_mem_range p e hL
      exact ⟨⟨y, hy⟩, Subtype.ext heq⟩⟩

/-- Cocharacter data of a finite type affine commutative group descend through
a bounded purely inseparable field extension without a separate power premise. -/
theorem IsDatum.exists_of_pow_mem_range_of_finiteType
    {χ : characterLattice Z} {m : Λ}
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsDatum χ m x) :
    ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ),
      IsDatum χ m y ∧ coeffMap (IsScalarTower.toAlgHom k F L) y = x := by
  obtain ⟨y, _, hy⟩ := hx.mult.exists_coeffMap_eq_of_pow_mem_range p e hL
  refine ⟨y, ?_, hy⟩
  apply IsDatum.of_coeff_map (IsScalarTower.toAlgHom k F L) (algebraMap F L).injective
  rwa [hy]

end Descent

end Langlands.GroupScheme.CocharacterDatum
