import Langlands.GroupScheme.HomogeneousCharacterCoordinates

/-! # Products of covariant functions and the induced regular representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace HomogeneousQuotientFromEmbedding

section Covariant

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- The product of covariant functions is covariant for the sum of their characters. -/
theorem IsRightCharacterCovariant.mul {χ ψ : rationalCharacters H} {f g : Γ(G.X.left, ⊤)}
    (hf : IsRightCharacterCovariant i χ f) (hg : IsRightCharacterCovariant i ψ g) :
    IsRightCharacterCovariant i (χ + ψ) (f * g) := by
  intro T a b
  rw [map_mul, map_mul, hf T a b, hg T a b, characterEval_add, Units.val_mul]
  ring

/-- The constant function one is covariant for the zero character. -/
theorem isRightCharacterCovariant_one :
    IsRightCharacterCovariant i (0 : rationalCharacters H) (1 : Γ(G.X.left, ⊤)) := by
  intro T a b
  rw [map_one, map_one, characterEval_zero, Units.val_one, one_mul]

/-- Powers of a covariant function are covariant for the multiples of its character. -/
theorem IsRightCharacterCovariant.pow {χ : rationalCharacters H} {f : Γ(G.X.left, ⊤)}
    (hf : IsRightCharacterCovariant i χ f) (n : ℕ) :
    IsRightCharacterCovariant i (n • χ) (f ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact isRightCharacterCovariant_one i
  | succ n ih => rw [succ_nsmul, pow_succ]; exact ih.mul i hf

end Covariant

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (D : HomogeneousQuotient i)
  [Mono i.hom.hom]

/-- Products of entire covariant function spaces land in the space of the summed character. -/
theorem mul_mem_rightCharacterCovariantSpace {χ ψ : rationalCharacters H}
    {f g : ((algΓ (CommRingCat.of k)).obj G.X).unop}
    (hf : f ∈ rightCharacterCovariantSpace i D χ) (hg : g ∈ rightCharacterCovariantSpace i D ψ) :
    f * g ∈ rightCharacterCovariantSpace i D (χ + ψ) :=
  IsRightCharacterCovariant.mul i hf hg

/-- The constant function one lies in the space of the zero character. -/
theorem one_mem_rightCharacterCovariantSpace :
    (1 : ((algΓ (CommRingCat.of k)).obj G.X).unop) ∈
      rightCharacterCovariantSpace i D (0 : rationalCharacters H) :=
  isRightCharacterCovariant_one i

/-- Powers of a covariant function lie in the space of the multiple character. -/
theorem pow_mem_rightCharacterCovariantSpace {χ : rationalCharacters H}
    {f : ((algΓ (CommRingCat.of k)).obj G.X).unop}
    (hf : f ∈ rightCharacterCovariantSpace i D χ) (n : ℕ) :
    f ^ n ∈ rightCharacterCovariantSpace i D (n • χ) :=
  IsRightCharacterCovariant.pow i hf n

/-- Multiplication of covariant functions, as a bilinear map of the entire spaces. -/
def rightCharacterCovariantMul (χ ψ : rationalCharacters H) :
    rightCharacterCovariantSpace i D χ →ₗ[k] rightCharacterCovariantSpace i D ψ →ₗ[k]
      rightCharacterCovariantSpace i D (χ + ψ) :=
  LinearMap.mk₂ k (fun f g => ⟨f.1 * g.1, mul_mem_rightCharacterCovariantSpace i D f.2 g.2⟩)
    (fun f f' g => Subtype.ext (add_mul f.1 f'.1 g.1))
    (fun r f g => Subtype.ext (smul_mul_assoc r f.1 g.1))
    (fun f g g' => Subtype.ext (mul_add f.1 g.1 g'.1))
    (fun r f g => Subtype.ext (mul_smul_comm r f.1 g.1))

@[simp] theorem rightCharacterCovariantMul_apply (χ ψ : rationalCharacters H)
    (f : rightCharacterCovariantSpace i D χ) (g : rightCharacterCovariantSpace i D ψ) :
    (rightCharacterCovariantMul i D χ ψ f g).1 = f.1 * g.1 := rfl

end HomogeneousQuotientFromEmbedding

namespace AffineCoordinates

section Character

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left]

/-- Evaluation at the identity point is the identification with global functions. -/
theorem pointAlgebraHom_id_apply (b : algebra G) :
    pointAlgebraHom G G.X (𝟙 G.X) b = globalAlgHom G b := rfl

/-- The coordinate of a sum of characters is the product of the coordinates. -/
theorem characterCoordinate_add (χ ψ : rationalCharacters G) :
    characterCoordinate G (χ + ψ) = characterCoordinate G χ * characterCoordinate G ψ := by
  apply (globalAlgHom_bijective G).1
  rw [map_mul, ← pointAlgebraHom_id_apply, ← pointAlgebraHom_id_apply,
    ← pointAlgebraHom_id_apply, pointAlgebraHom_characterCoordinate,
    pointAlgebraHom_characterCoordinate, pointAlgebraHom_characterCoordinate,
    characterEval_add, Units.val_mul]

/-- The coordinate of the zero character is one. -/
theorem characterCoordinate_zero : characterCoordinate G (0 : rationalCharacters G) = 1 := by
  apply (globalAlgHom_bijective G).1
  rw [map_one, ← pointAlgebraHom_id_apply, pointAlgebraHom_characterCoordinate,
    characterEval_zero, Units.val_one]

/-- The coordinate of a multiple of a character is the corresponding power. -/
theorem characterCoordinate_nsmul (χ : rationalCharacters G) (n : ℕ) :
    characterCoordinate G (n • χ) = characterCoordinate G χ ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, characterCoordinate_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, characterCoordinate_add, ih]

end Character

end AffineCoordinates

namespace HomogeneousQuotientFromEmbedding

open AffineCoordinates AffineLinearEmbedding

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (D : HomogeneousQuotient i)
  [Mono i.hom.hom] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsProper D.scheme.hom]

local instance homogeneousCharacterProductsInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance homogeneousCharacterProductsInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- The entire left-covariant coordinate subspace of a character coordinate. -/
abbrev inducedSpace (χ : rationalCharacters H) : Submodule k (algebra G) :=
  leftCovariantSubspace i (characterCoordinate H χ)

/-- A chosen basis of the entire finite induced space. -/
def inducedBasis (χ : rationalCharacters H) :
    Module.Basis (Fin (Module.finrank k (inducedSpace i χ))) k (inducedSpace i χ) :=
  letI := finite_leftCovariantSubspace_characterCoordinate i D χ
  Module.finBasis k (inducedSpace i χ)

/-- The induced representation of a character on a proper quotient: right translation on the
entire left-covariant coordinate subspace, in the chosen finite basis. -/
def inducedRepresentation (χ : rationalCharacters H) :
    MatrixRepresentation G (Fin (Module.finrank k (inducedSpace i χ))) :=
  Chevalley.affineRegularRepresentation G (inducedSpace i χ) (inducedBasis i D χ)
    (fun ψ _ hb => rightAct_mem_leftCovariantSubspace i _ ψ hb)

/-- The matrix of the induced representation at any test point evaluates the coordinate matrix
of the entire induced space. -/
theorem inducedRepresentation_pointMatrix (χ : rationalCharacters H)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (a b : Fin (Module.finrank k (inducedSpace i χ))) :
    letI : Coalgebra k (algebra G) :=
      (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
    (inducedRepresentation i D χ).pointMatrix T g a b =
      pointAlgebraHom G T g
        (Chevalley.subspaceMatrix (inducedSpace i χ) (inducedBasis i D χ) a b) :=
  Chevalley.affineRegularRepresentation_pointMatrix G _ _ _ T g a b

/-- Right multiplication by a test point acts on the chosen basis by the induced matrix. -/
theorem inducedRepresentation_mul_basis (χ : rationalCharacters H)
    (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X)
    (b : Fin (Module.finrank k (inducedSpace i χ))) :
    let M : Matrix (Fin (Module.finrank k (inducedSpace i χ)))
        (Fin (Module.finrank k (inducedSpace i χ))) ((algΓ (CommRingCat.of k)).obj T).unop :=
      ((inducedRepresentation i D χ).pointMatrix T h :
        Matrix (Fin (Module.finrank k (inducedSpace i χ)))
          (Fin (Module.finrank k (inducedSpace i χ))) Γ(T.left, ⊤))
    pointAlgebraHom G T (g * h) (inducedBasis i D χ b : algebra G) =
      ∑ a, pointAlgebraHom G T g (inducedBasis i D χ a : algebra G) * M a b :=
  Chevalley.affineRegularRepresentation_mul_basis G _ _ _ T g h b

end HomogeneousQuotientFromEmbedding

end Langlands.GroupScheme
