import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement

/-! # Affine-chart reduction for closed-point stalk dimension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Reduce the scheme statement to maximal-ideal height in a standard-smooth field algebra.
The algebraic assertion is an explicit argument, to be supplied by the dimension proof. -/
theorem fieldSmoothClosedPointStalkDimension_of_maximalHeight
    (hRing : ∀ (k S : Type u) [Field k] [CommRing S] [Algebra k S] (n : ℕ)
      [Algebra.IsStandardSmoothOfRelativeDimension n k S] (P : Ideal S) [P.IsMaximal],
      P.height = (n : ℕ∞)) :
    FieldSmoothClosedPointStalkDimensionStatement.{u} := by
  intro k _ X f g hf x hx
  let := hf
  obtain ⟨U, hU, V, hV, hxV, e, hstandard⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := g) (f := f) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    simpa only [Scheme.Hom.mem_preimage, hy] using e hxV
  subst U
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  let := (f.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g
      Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hstandard
  let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : P.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk x)]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
    (hRing Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) g P)

end Langlands.AlgebraicGeometry
