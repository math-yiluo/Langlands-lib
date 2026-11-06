import Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusAlgebra
import Langlands.GroupScheme.MatrixRepresentation.AdditiveFamilyActionAlgebra
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalSpan

/-! # Coefficient fullness for supplied generating additive families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveGeneratedFullness

open AdditiveDividedPowers AdditiveRestrictedOperators AdditiveTensorAlgebra

variable {k : Type u} [Field k] {I : Type v}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The natural action of the actual family matrix coefficient algebra on its
original coordinate space. -/
def coefficientAction
    (ρs : I → MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n) :
    coefficientAlgebra ρs →ₐ[k] Module.End k (n → k) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp (coefficientAlgebra ρs).val

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n)
  (f : I → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
  (p : ℕ) [Fact p.Prime] [CharP k p]

include p

/-- Over an algebraically closed field and a reduced ambient group, a dense
generated rational-point family gives full coefficient algebra for an actual
all-test irreducible ambient representation. -/
theorem coefficientAlgebra_eq_top_of_dense [IsAlgClosed k] [IsReduced G.X.left]
    (hρ : ρ.IsIrreducible)
    (hdense : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily
      (fun g : LeviGluing.generatedRationalPoints G
        (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f => g.val)) :
    coefficientAlgebra (fun i => ρ.restrict (f i)) = ⊤ := by
  let A := coefficientAlgebra (fun i => ρ.restrict (f i))
  let a := coefficientAction (fun i => ρ.restrict (f i))
  have hle : AdditiveFamilyActionAlgebra.coefficientAlgebra ρ f p ≤ a.range := by
    apply (AdditiveFamilyActionAlgebra.coefficientAlgebra_le_iff ρ f p _).mpr
    intro i r
    refine ⟨⟨coefficientMatrix (ρ.restrict (f i)) (p ^ r),
      coefficientMatrix_mem_coefficientAlgebra _ i (p ^ r)⟩, ?_⟩
    change Matrix.toLin' (coefficientMatrix (ρ.restrict (f i)) (p ^ r)) =
      dividedPower (ρ.restrict (f i)) (p ^ r)
    exact (dividedPower_eq_toLin _ _).symm
  let Γ := LeviGluing.generatedRationalPoints G
    (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f
  have hmem (g : Γ) : (ρ.rationalMatrix g.val : Matrix n n k) ∈ A := by
    have hg : ρ.rationalAction g.val ∈
        AdditiveFamilyActionAlgebra.coefficientAlgebra ρ f p := by
      rw [AdditiveFamilyActionAlgebra.coefficientAlgebra_eq_adjoin_generatedRationalAction
        ρ f p]
      exact Algebra.subset_adjoin ⟨g, rfl⟩
    obtain ⟨N, hN⟩ := hle hg
    change Matrix.toLinAlgEquiv' (N : Matrix n n k) =
      Matrix.toLinAlgEquiv' (ρ.rationalMatrix g.val : Matrix n n k) at hN
    have he := Matrix.toLinAlgEquiv'.injective hN
    exact he ▸ N.property
  have hspan : Submodule.span k
      (Set.range fun g : Γ => (ρ.rationalMatrix g.val : Matrix n n k)) ≤ A.toSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hmem g)
  have hfull := span_rationalMatrix_comp_eq_top_of_dense ρ hρ Γ.subtype hdense
  change Submodule.span k
    (Set.range fun g : Γ => (ρ.rationalMatrix g.val : Matrix n n k)) = ⊤ at hfull
  apply top_unique
  intro M _
  apply hspan
  rw [hfull]
  trivial

/-- Geometric generation by a supplied additive family provides the density
needed for coefficient fullness of an actual irreducible representation. -/
theorem coefficientAlgebra_eq_top_of_isGeneratedByFamily [IsAlgClosed k]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsReduced G.X.left]
    (hρ : ρ.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G)) :
    coefficientAlgebra (fun i => ρ.restrict (f i)) = ⊤ :=
  coefficientAlgebra_eq_top_of_dense ρ f p hρ
    (AdditiveFamilyActionAlgebra.hasDenseRationalPointFamily_of_isGeneratedByFamily f hgen)

/-- The coefficient-algebra action is onto all endomorphisms under the same
ambient irreducibility and supplied geometric-generation hypotheses. -/
theorem coefficientAction_surjective_of_isGeneratedByFamily [IsAlgClosed k]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsReduced G.X.left]
    (hρ : ρ.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G)) :
    Function.Surjective (coefficientAction (fun i => ρ.restrict (f i))) := by
  intro T
  refine ⟨⟨Matrix.toLinAlgEquiv'.symm T, ?_⟩, ?_⟩
  · rw [coefficientAlgebra_eq_top_of_isGeneratedByFamily ρ f p hρ hgen]
    trivial
  · exact Matrix.toLinAlgEquiv'.apply_symm_apply T

/-- For a supplied generating additive family, irreducibility of the original
second factor suffices for the actual ambient Frobenius tensor criterion. -/
theorem isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily [IsAlgClosed k]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsReduced G.X.left]
    [Nonempty n] [Nonempty m]
    (σ : MatrixRepresentation G m) (hσ : σ.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G))
    (e : ℕ)
    (hfirst : truncatedCoefficientAlgebra (fun i => ρ.restrict (f i)) (p ^ e) = ⊤) :
    (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible :=
  AdditiveFrobeniusAlgebra.isIrreducible_tensor_frobeniusPower_of_perfect
    (p := p) (ρ := ρ) (σ := σ) (f := f) e hfirst
    (coefficientAlgebra_eq_top_of_isGeneratedByFamily σ f p hσ hgen)

end Langlands.GroupScheme.MatrixRepresentation.AdditiveGeneratedFullness
