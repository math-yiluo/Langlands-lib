import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Rational.TorusCentralizer
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! # Distinct-weight centralizers in the general linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-- For distinct weights, the block Levi consists exactly of diagonal matrices. -/
theorem mem_blockLeviSubgroup_iff_isDiag_of_injective
    {A : Type*} [CommRing A] {e : n → ℤ} (he : Function.Injective e)
    {g : GL n A} :
    g ∈ blockLeviSubgroup A e ↔ (g : Matrix n n A).IsDiag := by
  constructor
  · intro hg i j hij
    exact hg i j (fun h => hij (he h))
  · intro hg i j hij
    exact hg (fun h => hij (congrArg e h))

/-- Distinct-weight block Levi points have diagonal matrices on every test scheme. -/
theorem mem_blockLevi_iff_isDiag_of_injective
    {R : CommRingCat.{u}} {e : n → ℤ} (he : Function.Injective e)
    {U : Over (Spec R)} {g : U ⟶ (groupScheme n R).X} :
    g ∈ (blockLevi n R e).carrier U ↔
      (pointsEquiv n R U g : Matrix n n Γ(U.left, ⊤)).IsDiag :=
  mem_blockLeviSubgroup_iff_isDiag_of_injective he

/-- Distinct-weight block Levi points centralize every homomorphism whose image is
diagonal over every test scheme, including after arbitrary refinements. -/
theorem blockLevi_le_torusCentralizer_of_diagonal
    {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    (i : T.toGrp ⟶ groupScheme n R) {e : n → ℤ} (he : Function.Injective e)
    (hi : ∀ (V : Over (Spec R)) (t : V ⟶ T.X),
      (pointsEquiv n R V (t ≫ i.hom.hom) : Matrix n n Γ(V.left, ⊤)).IsDiag) :
    blockLevi n R e ≤ torusCentralizer i := by
  intro U g hg V a t
  have hga := (mem_blockLevi_iff_isDiag_of_injective he).1
    ((blockLevi n R e).comp_mem a hg)
  have ht := hi V t
  change (a ≫ g) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (a ≫ g)
  apply (pointsEquiv n R V).injective
  rw [map_mul, map_mul]
  apply Units.ext
  change
    (pointsEquiv n R V (a ≫ g) : Matrix n n Γ(V.left, ⊤)) *
        (pointsEquiv n R V (t ≫ i.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
      (pointsEquiv n R V (t ≫ i.hom.hom) : Matrix n n Γ(V.left, ⊤)) *
        (pointsEquiv n R V (a ≫ g) : Matrix n n Γ(V.left, ⊤))
  simpa only [hga.diagonal_diag, ht.diagonal_diag] using
    (Matrix.commute_diagonal
      (Matrix.diag (pointsEquiv n R V (a ≫ g) : Matrix n n Γ(V.left, ⊤)))
      (Matrix.diag (pointsEquiv n R V (t ≫ i.hom.hom) : Matrix n n Γ(V.left, ⊤)))).eq

/-- Given the published dynamic block-Levi computation, a factored cocharacter
with distinct weights has exactly the centralizer of the diagonal-image torus. -/
theorem dynamicCentralizer_eq_torusCentralizer_of_injective_weights
    {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    (i : T.toGrp ⟶ groupScheme n R)
    (χ : (Gm (Spec R)).toGrp ⟶ T.toGrp) {e : n → ℤ}
    (he : Function.Injective e)
    (hi : ∀ (V : Over (Spec R)) (t : V ⟶ T.X),
      (pointsEquiv n R V (t ≫ i.hom.hom) : Matrix n n Γ(V.left, ⊤)).IsDiag)
    (hχ : χ ≫ i = diagonalCocharacter n R e)
    (hcentralizer : Dynamic.centralizer (diagonalCocharacter n R e) = blockLevi n R e) :
    Dynamic.centralizer (χ ≫ i) = torusCentralizer i := by
  apply le_antisymm
  · rw [hχ, hcentralizer]
    exact blockLevi_le_torusCentralizer_of_diagonal i he hi
  · exact torusCentralizer_le_dynamicCentralizer i χ

end Langlands.GroupScheme.GeneralLinear
