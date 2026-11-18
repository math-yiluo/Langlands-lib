import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra

/-! # Scalar commutants and full operator algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

namespace AffineCoefficientAlgebra

open AffineCoefficients

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- Every actual self-intertwiner is a scalar matrix. -/
def HasScalarIntertwiners : Prop :=
  ∀ C : Matrix n n k, Intertwines ρ ρ C → ∃ c : k, C = Matrix.scalar n c

/-- The actual scalar-commutant condition makes every operator-module
endomorphism scalar. -/
theorem endomorphism_scalar
    (hscalar : ∀ C : Matrix n n k, Intertwines ρ ρ C →
      ∃ c : k, C = Matrix.scalar n c)
    (f : Module.End (operatorAlgebra ρ) (n → k)) :
    ∃ c : k, f = c • (1 : Module.End (operatorAlgebra ρ) (n → k)) := by
  let C := LinearMap.toMatrix' (f.restrictScalars k)
  have hC : Intertwines ρ ρ C := by
    apply (intertwines_iff ρ C).mpr
    intro ℓ
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    let a : operatorAlgebra ρ :=
      ⟨(coefficientMap ρ ℓ).mulVecLin, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩
    exact f.map_smul a v
  obtain ⟨c, hc⟩ := hscalar C hC
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun M : Matrix n n k => M *ᵥ v) hc
  simpa [C, Matrix.scalar_apply, Matrix.diagonal_const_mulVec] using hh

/-- Jacobson density makes the operator algebra full when the actual
representation is irreducible and its self-intertwiners are scalar. -/
theorem operatorAlgebra_eq_top (hρ : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n k, Intertwines ρ ρ C →
      ∃ c : k, C = Matrix.scalar n c) :
    operatorAlgebra ρ = ⊤ := by
  classical
  let : IsSimpleModule (operatorAlgebra ρ) (n → k) := isSimpleModule ρ hρ
  apply top_unique
  intro f _
  let g : Module.End (Module.End (operatorAlgebra ρ) (n → k)) (n → k) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a v
        obtain ⟨c, rfl⟩ := endomorphism_scalar ρ hscalar a
        change f (c • v) = c • f v
        exact f.map_smul c v }
  let b := Module.finBasis k (n → k)
  obtain ⟨a, ha⟩ := jacobson_density (R := operatorAlgebra ρ) (M := n → k)
    g (Finset.univ.image b)
  have he : a.val = f := b.ext fun i =>
    (ha (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm
  exact he ▸ a.property

end AffineCoefficientAlgebra

end Langlands.GroupScheme.MatrixRepresentation
