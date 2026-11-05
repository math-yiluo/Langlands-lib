import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Left translation of covariant coordinates by a rational point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

section Translate

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Left translation of coordinates by a rational point `n`: `(L_n f)(g) = f(n g)`. -/
def leftTranslate (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    algebra G →ₐ[k] algebra G :=
  (globalAlgEquiv G).symm.toAlgHom.comp
    (pointAlgebraHom G G.X (G.constantPoint n G.X * 𝟙 G.X))

/-- Left translation evaluates at the translated point on every test scheme. -/
theorem pointAlgebraHom_leftTranslate (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (f : algebra G) :
    pointAlgebraHom G T g (leftTranslate G n f) =
      pointAlgebraHom G T (G.constantPoint n T * g) f := by
  rw [pointAlgebraHom_apply_eq, leftTranslate, AlgHom.comp_apply]
  change g.left.appTop (globalAlgEquiv G ((globalAlgEquiv G).symm _)) = _
  rw [AlgEquiv.apply_symm_apply]
  have h := pointAlgebraHom_naturality G g (G.constantPoint n G.X * 𝟙 G.X)
  rw [MonObj.comp_mul, G.constantPoint_naturality, Category.comp_id] at h
  rw [h]
  rfl

/-- Coordinates are determined by their values on all test points. -/
theorem ext_pointAlgebraHom {a b : algebra G}
    (h : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      pointAlgebraHom G T g a = pointAlgebraHom G T g b) : a = b :=
  (globalAlgHom_bijective G).1 (h G.X (𝟙 G.X))

/-- Translating by `n⁻¹` undoes translating by `n`. -/
theorem leftTranslate_inv_leftTranslate (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : algebra G) : leftTranslate G n⁻¹ (leftTranslate G n f) = f := by
  apply ext_pointAlgebraHom G
  intro T g
  rw [pointAlgebraHom_leftTranslate, pointAlgebraHom_leftTranslate, G.constantPoint_inv,
    mul_inv_cancel_left]

/-- Translating by `n` undoes translating by `n⁻¹`. -/
theorem leftTranslate_leftTranslate_inv (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : algebra G) : leftTranslate G n (leftTranslate G n⁻¹ f) = f := by
  apply ext_pointAlgebraHom G
  intro T g
  rw [pointAlgebraHom_leftTranslate, pointAlgebraHom_leftTranslate, G.constantPoint_inv,
    inv_mul_cancel_left]

end Translate

section Covariant

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance covariantConjugateInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance covariantConjugateInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- A test point of the conjugated subgroup map is the conjugated test point. -/
theorem comp_conj_hom (i : H ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    h ≫ (i ≫ (G.innerIso n).hom).hom.hom =
      G.constantPoint n T * (h ≫ i.hom.hom) * (G.constantPoint n T)⁻¹ := by
  rw [← comp_innerIso_hom]
  rfl

/-- Translation by `n` sends coordinates covariant for the `n`-conjugate of `i` to
coordinates covariant for `i`, with the same weight. -/
theorem leftTranslate_mem_leftCovariantSubspace (i : H ⟶ G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace (i ≫ (G.innerIso n).hom) χ) :
    leftTranslate G n f ∈ leftCovariantSubspace i χ := by
  rw [mem_leftCovariantSubspace_iff_points] at hf ⊢
  intro T h g
  rw [pointAlgebraHom_leftTranslate, pointAlgebraHom_leftTranslate]
  have hconj := hf T h (G.constantPoint n T * g)
  rw [comp_conj_hom] at hconj
  rw [← hconj]
  congr 1
  group

/-- Translation by `n⁻¹` sends coordinates covariant for `i` to coordinates covariant for
the `n`-conjugate of `i`, with the same weight. -/
theorem leftTranslate_inv_mem_leftCovariantSubspace (i : H ⟶ G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) :
    leftTranslate G n⁻¹ f ∈ leftCovariantSubspace (i ≫ (G.innerIso n).hom) χ := by
  rw [mem_leftCovariantSubspace_iff_points] at hf ⊢
  intro T h g
  rw [pointAlgebraHom_leftTranslate, pointAlgebraHom_leftTranslate, comp_conj_hom,
    G.constantPoint_inv]
  have hc := hf T h ((G.constantPoint n T)⁻¹ * g)
  rw [← hc]
  congr 1
  group

/-- Left translation by `n⁻¹` identifies the covariant coordinates of `i` with those of
its `n`-conjugate, for the same weight. -/
def leftCovariantConjEquiv (i : H ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (χ : algebra H) :
    leftCovariantSubspace i χ ≃ₗ[k] leftCovariantSubspace (i ≫ (G.innerIso n).hom) χ where
  toFun f := ⟨leftTranslate G n⁻¹ f, leftTranslate_inv_mem_leftCovariantSubspace i n χ f.2⟩
  invFun f := ⟨leftTranslate G n f, leftTranslate_mem_leftCovariantSubspace i n χ f.2⟩
  map_add' f f' := Subtype.ext (map_add (leftTranslate G n⁻¹) (f : algebra G) f')
  map_smul' c f := Subtype.ext ((leftTranslate G n⁻¹).map_smul_of_tower c (f : algebra G))
  left_inv f := Subtype.ext (leftTranslate_leftTranslate_inv G n f)
  right_inv f := Subtype.ext (leftTranslate_inv_leftTranslate G n f)

/-- A basis of the covariant coordinates of `i` transports to a basis, on the same index
type, of the covariant coordinates of the `n`-conjugate of `i`. -/
def leftCovariantConjBasis {I : Type*} (i : H ⟶ G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (χ : algebra H)
    (b : Module.Basis I k (leftCovariantSubspace i χ)) :
    Module.Basis I k (leftCovariantSubspace (i ≫ (G.innerIso n).hom) χ) :=
  b.map (leftCovariantConjEquiv i n χ)

end Covariant

end AffineCoordinates

end Langlands.GroupScheme
