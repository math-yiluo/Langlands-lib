import Langlands.GroupScheme.Rational.PolynomialGaloisPermutation
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Orbit-block products and their actual coordinate pullbacks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrbitProductPullback

set_option backward.isDefEq.respectTransparency false

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (I : Type u)
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Multiply the actual polynomial-valued factors within each block, retaining
both the order of each block and the order of the blocks. -/
def blockProduct (blocks : List (List I))
    (f : I → Lie.AffinePoints G (MvPolynomial I K)) :
    Lie.AffinePoints G (MvPolynomial I K) :=
  (blocks.map (fun l => (l.map f).prod)).prod

/-- Factor transport fixes the block product when each block is preserved as
a multiset and its factors commute. No commutation between blocks is needed. -/
theorem blockProduct_fixed (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (blocks : List (List I)) (f : I → Lie.AffinePoints G (MvPolynomial I K))
    (hblocks : ∀ (σ : K ≃ₐ[k] K) l, l ∈ blocks → (l.map (ρ σ)).Perm l)
    (hcomm : ∀ l, l ∈ blocks → (l.map f).Pairwise Commute)
    (hf : ∀ (σ : K ≃ₐ[k] K) i,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) (f i) = f (ρ σ i))
    (σ : K ≃ₐ[k] K) :
    Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ)
        (blockProduct k K I G blocks f) = blockProduct k K I G blocks f := by
  unfold blockProduct
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro l hl
  dsimp only [Function.comp_def]
  rw [map_list_prod, List.map_map]
  simpa only [List.map_map, Function.comp_def, hf σ] using
    (((hblocks σ l hl).map f).symm.prod_eq' (hcomm l hl)).symm

variable [IsAffine G.X.left]

/-- Scalar extension of the actual coordinate map of a polynomial-valued point. -/
def pullbackK (x : Lie.AffinePoints G (MvPolynomial I K)) :
    K ⊗[k] (CocharacterDatum.coordAlgebra G) →ₐ[K] MvPolynomial I K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (MvPolynomial I K))
    (CocharacterDatum.coord x).hom (fun _ _ => Commute.all _ _)

/-- The same actual coordinate pullback, regarded over the ground field. -/
def pullback (x : Lie.AffinePoints G (MvPolynomial I K)) :
    K ⊗[k] (CocharacterDatum.coordAlgebra G) →ₐ[k] MvPolynomial I K :=
  (pullbackK k K I G x).restrictScalars k

@[simp]
theorem pullbackK_tmul (x : Lie.AffinePoints G (MvPolynomial I K))
    (c : K) (a : CocharacterDatum.coordAlgebra G) :
    pullbackK k K I G x (c ⊗ₜ[k] a) =
      MvPolynomial.C c * (CocharacterDatum.coord x).hom a := rfl

@[simp]
theorem pullback_tmul (x : Lie.AffinePoints G (MvPolynomial I K))
    (c : K) (a : CocharacterDatum.coordAlgebra G) :
    pullback k K I G x (c ⊗ₜ[k] a) =
      MvPolynomial.C c * (CocharacterDatum.coord x).hom a := rfl

/-- Fixedness of the actual point fixes every ground-coordinate evaluation. -/
theorem coord_fixed (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (x : Lie.AffinePoints G (MvPolynomial I K))
    (hx : ∀ σ : K ≃ₐ[k] K,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) x = x)
    (σ : K ≃ₐ[k] K) (a : CocharacterDatum.coordAlgebra G) :
    PolynomialGalois.orbitAction k K I ρ σ ((CocharacterDatum.coord x).hom a) =
      (CocharacterDatum.coord x).hom a := by
  have h := congrArg (fun y : Lie.AffinePoints G (MvPolynomial I K) =>
    (CocharacterDatum.coord y).hom a) (hx σ)
  rw [CocharacterDatum.coord_affineMap] at h
  exact h

/-- The full tensor pullback intertwines coefficient conjugation and the
combined coefficient-and-variable action. -/
theorem pullback_equivariant (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (x : Lie.AffinePoints G (MvPolynomial I K))
    (hx : ∀ σ : K ≃ₐ[k] K,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) x = x)
    (σ : K ≃ₐ[k] K) (z : K ⊗[k] (CocharacterDatum.coordAlgebra G)) :
    pullback k K I G x
        (TensorGaloisPoint.coefficientConjugate k K (CocharacterDatum.coordAlgebra G) σ z) =
      PolynomialGalois.orbitAction k K I ρ σ (pullback k K I G x z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c a =>
    simp only [TensorGaloisPoint.coefficientConjugate_tmul, pullback_tmul,
      map_mul, PolynomialGalois.orbitAction_C, coord_fixed k K I G ρ x hx]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Over any Galois extension, the kernel of the actual fixed-point pullback
is extended from its contraction to the ground coordinate algebra. -/
theorem map_groundIdeal_pullback_ker_eq [IsGalois k K]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (x : Lie.AffinePoints G (MvPolynomial I K))
    (hx : ∀ σ : K ≃ₐ[k] K,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) x = x) :
    (GaloisIdealDescent.groundIdeal k K (CocharacterDatum.coordAlgebra G)
        (RingHom.ker (pullback k K I G x).toRingHom)).map
        (Algebra.TensorProduct.includeRight :
          CocharacterDatum.coordAlgebra G →ₐ[k] K ⊗[k] (CocharacterDatum.coordAlgebra G)).toRingHom =
      RingHom.ker (pullback k K I G x).toRingHom :=
  PolynomialGalois.map_groundIdeal_ker_eq k K I (CocharacterDatum.coordAlgebra G) ρ
    (pullback k K I G x) (pullback_equivariant k K I G ρ x hx)

/-- Apply the actual coordinate-kernel descent to a block product with
transported commuting factors. -/
theorem map_groundIdeal_blockProduct_ker_eq [IsGalois k K]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (blocks : List (List I)) (f : I → Lie.AffinePoints G (MvPolynomial I K))
    (hblocks : ∀ (σ : K ≃ₐ[k] K) l, l ∈ blocks → (l.map (ρ σ)).Perm l)
    (hcomm : ∀ l, l ∈ blocks → (l.map f).Pairwise Commute)
    (hf : ∀ (σ : K ≃ₐ[k] K) i,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) (f i) = f (ρ σ i)) :
    (GaloisIdealDescent.groundIdeal k K (CocharacterDatum.coordAlgebra G)
        (RingHom.ker (pullback k K I G (blockProduct k K I G blocks f)).toRingHom)).map
        (Algebra.TensorProduct.includeRight :
          CocharacterDatum.coordAlgebra G →ₐ[k] K ⊗[k] (CocharacterDatum.coordAlgebra G)).toRingHom =
      RingHom.ker (pullback k K I G (blockProduct k K I G blocks f)).toRingHom :=
  map_groundIdeal_pullback_ker_eq k K I G ρ (blockProduct k K I G blocks f)
    (blockProduct_fixed k K I G ρ blocks f hblocks hcomm hf)

end Langlands.GroupScheme.OrbitProductPullback
