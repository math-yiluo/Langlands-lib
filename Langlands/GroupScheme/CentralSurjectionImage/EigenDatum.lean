import Langlands.GroupScheme.CentralSurjectionImage.PointWeights
import Langlands.GroupScheme.CentralSurjectionImage.EigenGrading

/-! # Cocharacter data from a single point over an algebraically closed field

Let `Z` be an affine commutative group scheme over a field `k`, `χ` a character of `Z` and `x` a
point of `Z` with values in an algebraically closed field `K`. The generalized eigenspace grading
of the coordinate algebra under right translation by `x` is a multiplicative point of `Z` over
`K[Kˣ]` on which `χ` takes the monomial value of `χ(x)`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

section Universal

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The universal point of an affine group scheme, over its coordinate algebra. -/
abbrev univ : Lie.AffinePoints G (coordAlgebra G) := (coordIso G).hom

theorem coord_univ : coord (univ G) = 𝟙 (coordAlgebra G) := by
  apply Quiver.Hom.op_inj
  apply algSpec.fullyFaithful.map_injective
  rw [← cancel_mono (coordIso G).hom, map_coord, op_id]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ (coordIso G).hom)
    ((algSpec (CommRingCat.of k)).map_id _).symm)

variable {G}

/-- Every point is the image of the universal point along its coordinate map. -/
theorem affineMap_coord_univ {S : Type u} [CommRing S] [Algebra k S] (x : Lie.AffinePoints G S) :
    Lie.affineMap G (coord x).hom (univ G) = x := by
  rw [Lie.affineMap_apply, CommAlgCat.ofHom_hom]
  exact map_coord x

end Universal

section Character

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine Z.toGrp.X.left]

/-- The coordinate function of a character: its value on the universal point. -/
def charCoord (χ : characterLattice Z) : coordAlgebra Z.toGrp :=
  (Lie.characterValue χ (univ Z.toGrp) : coordAlgebra Z.toGrp)

/-- A character evaluated on a point is its coordinate function under the coordinate map. -/
theorem characterValue_eq_coord (χ : characterLattice Z) {S : Type u} [CommRing S] [Algebra k S]
    (x : Lie.AffinePoints Z.toGrp S) :
    (Lie.characterValue χ x : S) = (coord x).hom (charCoord χ) := by
  conv_lhs => rw [← affineMap_coord_univ x]
  rw [characterValue_affineMap]
  rfl

theorem productMap_includeLeft_includeRight {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (t : A ⊗[R] A) :
    Algebra.TensorProduct.productMap Algebra.TensorProduct.includeLeft
      Algebra.TensorProduct.includeRight t = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => rw [map_add, hx, hy]

/-- The coordinate function of a character is grouplike. -/
theorem comul_charCoord (χ : characterLattice Z) :
    comul Z.toGrp (charCoord χ) = charCoord χ ⊗ₜ charCoord χ := by
  let B := coordAlgebra Z.toGrp
  let p₁ : Lie.AffinePoints Z.toGrp (B ⊗[CommRingCat.of k] B) :=
    Lie.affineMap _ Algebra.TensorProduct.includeLeft (univ _)
  let p₂ : Lie.AffinePoints Z.toGrp (B ⊗[CommRingCat.of k] B) :=
    Lie.affineMap _ Algebra.TensorProduct.includeRight (univ _)
  have h := congrArg (fun u : (B ⊗[CommRingCat.of k] B)ˣ => (u : B ⊗[CommRingCat.of k] B))
    (characterValue_mul χ p₁ p₂)
  simp only [Units.val_mul, characterValue_eq_coord] at h
  rw [coord_mul, coord_affineMap, coord_affineMap, coord_univ] at h
  simp only [Category.id_comp, CommAlgCat.hom_ofHom, AlgHom.comp_apply] at h
  rw [productMap_includeLeft_includeRight] at h
  rw [h, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem counit_charCoord (χ : characterLattice Z) : counit Z.toGrp (charCoord χ) = 1 := by
  have h := congrArg (fun u : (CommRingCat.of k)ˣ => (u : CommRingCat.of k))
    (characterValue_one (S := CommRingCat.of k) χ)
  simp only [characterValue_eq_coord, Units.val_one] at h
  rw [coord_one] at h
  simpa using h

/-- The point with a prescribed coordinate map. -/
def pointOfCoord {S : Type u} [CommRing S] [Algebra k S]
    (f : coordAlgebra Z.toGrp →ₐ[CommRingCat.of k] S) : Lie.AffinePoints Z.toGrp S :=
  (corep Z.toGrp).homEquiv (CommAlgCat.ofHom f)

theorem coord_pointOfCoord {S : Type u} [CommRing S] [Algebra k S]
    (f : coordAlgebra Z.toGrp →ₐ[CommRingCat.of k] S) : (coord (pointOfCoord f)).hom = f := by
  change ((corep Z.toGrp).homEquiv.symm ((corep Z.toGrp).homEquiv (CommAlgCat.ofHom f))).hom = f
  rw [Equiv.symm_apply_apply]
  rfl

/-- **Eigen data.** A point `x` of an affine commutative group scheme with values in an
algebraically closed field `K` gives a cocharacter datum over `K[Kˣ]` whose weight is the value
of the character at `x`. -/
theorem exists_datum_of_point {K : Type u} [Field K] [IsAlgClosed K] [Algebra k K]
    (χ : characterLattice Z) (x : Lie.AffinePoints Z.toGrp K) :
    ∃ p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra K (Additive Kˣ)),
      IsDatum χ (Additive.ofMul (Lie.characterValue χ x)) p := by
  classical
  let : Bialgebra k (coordAlgebra Z.toGrp) := AffineLinearEmbedding.bialgebra (corep Z.toGrp)
  have he' : ∀ b, Algebra.TensorProduct.productMap (coord x⁻¹).hom (coord x).hom
      (Coalgebra.comul (R := k) b) = algebraMap k K (Coalgebra.counit (R := k) b) := by
    intro b
    have h := congrArg (fun f => f b) (coord_mul x⁻¹ x)
    simp only at h
    rw [inv_mul_cancel, coord_one] at h
    exact h.symm
  obtain ⟨ψ, hψ, hg⟩ := EigenGrading.exists_grading (k := k) (B := coordAlgebra Z.toGrp) (K := K)
    (coord x).hom (coord x⁻¹).hom he'
  obtain ⟨hne, hψg⟩ := hg (charCoord χ) (comul_charCoord χ) (counit_charCoord χ)
  refine ⟨pointOfCoord ψ, ?_, ?_⟩
  · apply coord_injective
    apply CommAlgCat.hom_ext
    rw [coord_mul, coord_affineMap, coord_affineMap, coord_affineMap]
    simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
    rw [coord_pointOfCoord]
    apply AlgHom.ext
    intro b
    exact hψ b
  · apply Units.ext
    rw [characterValue_eq_coord, coord_pointOfCoord, hψg, monomial_val]
    congr 2
    apply Units.ext
    rw [Units.val_mk0, characterValue_eq_coord]

end Character

end Langlands.GroupScheme.CentralSurjectionImage
