import Langlands.GroupScheme.HomScheme.MultiplicativityDefect

/-! # Reduction of actual defects and corrected homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme

variable {S S₀ : Scheme.{u}} {H G : GroupScheme S}

/-- Actual base change of a test-valued point, as a group homomorphism. -/
def reductionPointHom (r : S₀ ⟶ S) (G : GroupScheme S) (T : Over S) :
    (T ⟶ G.X) →*
      ((Over.pullback r).obj T ⟶ ((baseChange r).obj G).X) :=
  (Over.pullback r).homMonoidHom

/-- The actual reduction kernel on every test scheme. No quasi-coherent
description of this pointwise kernel is asserted here. -/
def reductionKernel (r : S₀ ⟶ S) (G : GroupScheme S) : SubgroupFunctor G where
  carrier T := (reductionPointHom r G T).ker
  comp_mem a x hx := by
    change (Over.pullback r).map (a ≫ x) =
      (1 : (Over.pullback r).obj _ ⟶ ((baseChange r).obj G).X)
    have hh : (Over.pullback r).map x =
        (1 : (Over.pullback r).obj _ ⟶ ((baseChange r).obj G).X) := hx
    rw [Functor.map_comp, hh]
    exact MonObj.comp_one (M := ((baseChange r).obj G).X) ((Over.pullback r).map a)

@[simp]
theorem mem_reductionKernel (r : S₀ ⟶ S) (G : GroupScheme S)
    (T : Over S) (x : T ⟶ G.X) :
    x ∈ (reductionKernel r G).carrier T ↔ reductionPointHom r G T x = 1 := Iff.rfl

/-- The group-valued Yoneda reconstruction has exactly the corrected underlying
scheme morphism. -/
theorem correctedHom_hom (s b : H.X ⟶ G.X) (hb : IsDefectCorrection s b) :
    (correctedHom s b hb).hom.hom = correctedSchemeMap s b := by
  simpa only [Category.id_comp] using comp_correctedHom s b hb H.X (𝟙 H.X)

/-- If a scheme map reduces to a homomorphism, its actual multiplicativity
defect reduces to the identity point. -/
theorem multiplicationDefect_baseChange_eq_one
    (r : S₀ ⟶ S) (s : H.X ⟶ G.X)
    (f₀ : (baseChange r).obj H ⟶ (baseChange r).obj G)
    (hs : (Over.pullback r).map s = f₀.hom.hom) :
    (Over.pullback r).map (multiplicationDefect s) =
      (1 : (Over.pullback r).obj (H.X ⊗ H.X) ⟶ ((baseChange r).obj G).X) := by
  simp only [multiplicationDefect, Functor.map_mul, Functor.map_inv',
    Functor.map_comp, hs]
  let x : (Over.pullback r).obj (H.X ⊗ H.X) ⟶ ((baseChange r).obj H).X :=
    (Over.pullback r).map (fst H.X H.X)
  let y : (Over.pullback r).obj (H.X ⊗ H.X) ⟶ ((baseChange r).obj H).X :=
    (Over.pullback r).map (snd H.X H.X)
  change (x ≫ f₀.hom.hom) * (y ≫ f₀.hom.hom) * ((x * y) ≫ f₀.hom.hom)⁻¹ = 1
  rw [MonObj.mul_comp, mul_inv_cancel]

/-- A regular defect correction that is trivial after reduction gives a lift
of the prescribed reduced homomorphism. -/
theorem correctedHom_baseChange_eq
    (r : S₀ ⟶ S) (s b : H.X ⟶ G.X) (hb : IsDefectCorrection s b)
    (f₀ : (baseChange r).obj H ⟶ (baseChange r).obj G)
    (hs : (Over.pullback r).map s = f₀.hom.hom)
    (hb₀ : (Over.pullback r).map b =
      (1 : ((baseChange r).obj H).X ⟶ ((baseChange r).obj G).X)) :
    (baseChange r).map (correctedHom s b hb) = f₀ := by
  apply Grp.hom_ext
  change (Over.pullback r).map (correctedHom s b hb).hom.hom = f₀.hom.hom
  rw [correctedHom_hom, correctedSchemeMap, Functor.map_mul,
    Functor.map_inv', hb₀, hs]
  change (1 : ((baseChange r).obj H).X ⟶ ((baseChange r).obj G).X)⁻¹ *
    f₀.hom.hom = f₀.hom.hom
  rw [inv_one, one_mul]

/-- The regular difference of two homomorphisms with equal reductions takes
values in the actual reduction kernel. -/
theorem homomorphismDifference_baseChange_eq_one
    (r : S₀ ⟶ S) (f f' : H ⟶ G)
    (hf : (baseChange r).map f = (baseChange r).map f') :
    (Over.pullback r).map (homomorphismDifference f f') =
      (1 : ((baseChange r).obj H).X ⟶ ((baseChange r).obj G).X) := by
  have hh := congrArg (fun k => k.hom.hom) hf
  change (Over.pullback r).map f.hom.hom = (Over.pullback r).map f'.hom.hom at hh
  rw [homomorphismDifference, Functor.map_mul, Functor.map_inv', hh]
  change ((baseChange r).map f').hom.hom *
    (((baseChange r).map f').hom.hom)⁻¹ = 1
  exact mul_inv_cancel _

end Langlands.GroupScheme.HomScheme
