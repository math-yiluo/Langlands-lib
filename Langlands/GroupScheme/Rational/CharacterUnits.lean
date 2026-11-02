import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Rational.CharacterLatticeAlgebra

/-! # Rational characters as units of the coordinate algebra

For an affine group scheme `G` over a field `k`, a rational character `χ : G ⟶ 𝔾_m` is determined
by the unit `χ(x)` of the coordinate algebra `O(G)` at the universal point `x`. These units are
group-like for the comultiplication of `O(G)`, hence `k`-linearly independent.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CharacterUnits

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- The chosen affine coordinate algebra `O(G)` of `G`. -/
abbrev Coord : CommAlgCat (CommRingCat.of k) := Lie.coordinateAlgebra G

/-- The universal point of `G` with coefficients in its coordinate algebra. -/
def universalPoint : G.affinePoints (Coord G) := (Lie.pointCoordinates G).symm (AlgHom.id _ _)

theorem pointCoordinates_universalPoint :
    Lie.pointCoordinates G (universalPoint G) = AlgHom.id _ _ :=
  (Lie.pointCoordinates G).apply_symm_apply _

theorem universalPoint_eq : universalPoint G = (Lie.coordinateIso G).hom := by
  change (algSpec _).map (𝟙 (op (Coord G))) ≫ (Lie.coordinateIso G).hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Extending coefficients of the universal point along `φ` gives the point with coordinates
`φ`. -/
theorem affinePointMap_universalPoint_eq {B : Type u} [CommRing B] [Algebra (CommRingCat.of k) B]
    (φ : Coord G →ₐ[CommRingCat.of k] B) :
    G.affinePointMap (CommAlgCat.ofHom φ) (universalPoint G) = (Lie.pointCoordinates G).symm φ := by
  rw [GroupScheme.affinePointMap_apply, universalPoint_eq]
  rfl

theorem pointCoordinates_affinePointMap_universalPoint {B : Type u} [CommRing B]
    [Algebra (CommRingCat.of k) B] (φ : Coord G →ₐ[CommRingCat.of k] B) :
    Lie.pointCoordinates G (G.affinePointMap (CommAlgCat.ofHom φ) (universalPoint G)) = φ := by
  rw [affinePointMap_universalPoint_eq]
  exact (Lie.pointCoordinates G).apply_symm_apply φ

/-- Every coefficient point is the image of the universal point. -/
theorem affinePointMap_universalPoint {A : CommAlgCat (CommRingCat.of k)} (x : G.affinePoints A) :
    G.affinePointMap (CommAlgCat.ofHom (Lie.pointCoordinates G x)) (universalPoint G) = x := by
  rw [affinePointMap_universalPoint_eq]
  exact (Lie.pointCoordinates G).symm_apply_apply x

variable {G}

/-- The unit of `O(G)` attached to a rational character: its value at the universal point. -/
def unit (χ : rationalCharacters G) : (Coord G)ˣ :=
  Gm.affineUnitsEquiv (CommRingCat.of k) (Coord G) (universalPoint G ≫ χ.toMul.hom.hom)

/-- The value of `χ` at any coefficient point is the image of `unit χ` under the coordinates of
that point. -/
theorem affineUnitsEquiv_comp {A : CommAlgCat (CommRingCat.of k)} (χ : rationalCharacters G)
    (x : G.affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) =
      Units.map (Lie.pointCoordinates G x).toRingHom.toMonoidHom (unit χ) := by
  have h := Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
    (CommAlgCat.ofHom (Lie.pointCoordinates G x)) (universalPoint G ≫ χ.toMul.hom.hom)
  have hx : x ≫ χ.toMul.hom.hom = GroupScheme.affinePointMap _
      (CommAlgCat.ofHom (Lie.pointCoordinates G x)) (universalPoint G ≫ χ.toMul.hom.hom) := by
    rw [GroupScheme.affinePointMap_apply, ← Category.assoc, ← GroupScheme.affinePointMap_apply G,
      affinePointMap_universalPoint]
  rw [hx, h]
  rfl

theorem unit_add (χ ψ : rationalCharacters G) : unit (χ + ψ) = unit χ * unit ψ := by
  rw [unit, rationalCharacters.comp_add, map_mul]
  rfl

theorem unit_zero : unit (0 : rationalCharacters G) = 1 := by
  rw [unit, rationalCharacters.comp_zero, map_one]

/-- Rational characters as units of the coordinate algebra, written additively. -/
def unitHom : rationalCharacters G →+ Additive (Coord G)ˣ where
  toFun χ := Additive.ofMul (unit χ)
  map_zero' := congrArg Additive.ofMul unit_zero
  map_add' χ ψ := congrArg Additive.ofMul (unit_add χ ψ)

theorem unitHom_apply (χ : rationalCharacters G) : (unitHom χ).toMul = unit χ := rfl

theorem unit_injective : Function.Injective (unit (G := G)) := by
  intro χ ψ h
  have h' : universalPoint G ≫ χ.toMul.hom.hom = universalPoint G ≫ ψ.toMul.hom.hom :=
    (Gm.affineUnitsEquiv (CommRingCat.of k) (Coord G)).injective h
  have h'' : χ.toMul.hom.hom = ψ.toMul.hom.hom := by
    simpa [universalPoint_eq] using congrArg ((Lie.coordinateIso G).inv ≫ ·) h'
  have h3 : Additive.toMul χ = Additive.toMul ψ :=
    hom_ext_points fun T x => congrArg (x ≫ ·) h''
  exact Additive.toMul.injective h3

theorem unitHom_injective : Function.Injective (unitHom (G := G)) :=
  fun _ _ h => unit_injective (congrArg Additive.toMul h)

variable (G)

/-- The left inclusion `O(G) → O(G) ⊗ O(G)`. -/
abbrev inclLeft : Coord G →ₐ[CommRingCat.of k] Coord G ⊗[CommRingCat.of k] Coord G :=
  Algebra.TensorProduct.includeLeft (R := CommRingCat.of k) (S := CommRingCat.of k)

/-- The right inclusion `O(G) → O(G) ⊗ O(G)`. -/
abbrev inclRight : Coord G →ₐ[CommRingCat.of k] Coord G ⊗[CommRingCat.of k] Coord G :=
  Algebra.TensorProduct.includeRight

/-- The comultiplication of `O(G)`: the coordinates of the product of the two universal points
in `G(O(G) ⊗ O(G))`. -/
def comul : Coord G →ₐ[CommRingCat.of k] Coord G ⊗[CommRingCat.of k] Coord G :=
  Lie.pointCoordinates G
    (G.affinePointMap (CommAlgCat.ofHom (inclLeft G)) (universalPoint G) *
      G.affinePointMap (CommAlgCat.ofHom (inclRight G)) (universalPoint G))

variable {G}

/-- The unit of a rational character is group-like. -/
theorem comul_unit (χ : rationalCharacters G) :
    comul G (unit χ) = (unit χ : Coord G) ⊗ₜ (unit χ : Coord G) := by
  have h := affineUnitsEquiv_comp
    (A := CommAlgCat.of (CommRingCat.of k) (Coord G ⊗[CommRingCat.of k] Coord G)) χ
    (G.affinePointMap (CommAlgCat.ofHom (inclLeft G)) (universalPoint G) *
      G.affinePointMap (CommAlgCat.ofHom (inclRight G)) (universalPoint G))
  rw [MonObj.mul_comp, map_mul, affineUnitsEquiv_comp, affineUnitsEquiv_comp] at h
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.coe_map] at h2
  change _ = comul G (unit χ) at h2
  rw [← h2]
  change (Lie.pointCoordinates G (G.affinePointMap (CommAlgCat.ofHom (inclLeft G))
      (universalPoint G))) _ * (Lie.pointCoordinates G (G.affinePointMap
      (CommAlgCat.ofHom (inclRight G)) (universalPoint G))) _ = _
  rw [pointCoordinates_affinePointMap_universalPoint, pointCoordinates_affinePointMap_universalPoint,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem nontrivial_coord : Nontrivial (Coord G) :=
  (Lie.coordinateOrigin G).toRingHom.domain_nontrivial

/-- The units of distinct rational characters are `k`-linearly independent in `O(G)`. -/
theorem linearIndependent_unit :
    LinearIndependent (CommRingCat.of k) (fun χ : rationalCharacters G => (unit χ : Coord G)) := by
  have := nontrivial_coord (G := G)
  have hinj : Function.Injective (fun χ : rationalCharacters G => (unit χ : Coord G)) :=
    fun _ _ h => unit_injective (Units.ext h)
  rw [← linearIndepOn_id_range_iff hinj]
  refine CharacterLattice.linearIndepOn_of_comul (comul G).toLinearMap ?_ ?_
  · rintro _ ⟨χ, rfl⟩
    exact comul_unit χ
  · rintro _ ⟨χ, rfl⟩
    exact (unit χ).ne_zero

end Langlands.GroupScheme.CharacterUnits
