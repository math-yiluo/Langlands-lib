import Langlands.Algebra.CoalgebraNilpotentReduction
import Langlands.Algebra.CoalgebraIdempotentBasis

/-! # Group-like bases from split reduced convolution duals over local rings -/

noncomputable section

universe u v w

open Coalgebra WithConv Module

namespace Langlands.CoalgebraLocalSplit

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]
  [Module.Free R C] [Module.Finite R C]

/-- A spanning orthogonal idempotent family in the convolution dual of a
finite free coalgebra over a local ring contains a finite basis. -/
theorem exists_orthogonalIdempotent_basis {ι : Type w}
    (e : ι → WithConv (C →ₗ[R] R)) (he : OrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    ∃ (κ : Type w) (_ : Fintype κ) (b : Basis κ R (WithConv (C →ₗ[R] R))),
      OrthogonalIdempotents b := by
  classical
  let d := WithConv.linearEquiv R (C →ₗ[R] R)
  have hspan' : Submodule.span R (Set.range (fun i => (e i).ofConv)) = ⊤ := by
    have h := congrArg (Submodule.map d.toLinearMap) hspan
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr d.surjective, ← Set.range_comp] at h
    exact h
  let : Module.FinitePresentation R (C →ₗ[R] R) :=
    Module.finitePresentation_of_projective R (C →ₗ[R] R)
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat
    (fun i => (e i).ofConv) hspan'
  let b' := b.map d.symm
  have hb' (i : κ) : b' i = e (a i) := by
    change toConv (b i) = e (a i)
    rw [hb]
  have ha : Function.Injective a := by
    intro i j hij
    apply b.injective
    rw [hb, hb, hij]
  let : Finite κ := Module.Finite.finite_basis b
  refine ⟨κ, Fintype.ofFinite κ, b', ?_⟩
  convert he.embedding ⟨a, ha⟩ using 1
  exact funext hb'

/-- A finite free coalgebra over a local ring whose convolution dual is
spanned by orthogonal idempotents has a finite group-like basis. -/
theorem exists_groupLike_basis {ι : Type w}
    (e : ι → WithConv (C →ₗ[R] R)) (he : OrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    ∃ (κ : Type w) (_ : Fintype κ) (b : Basis κ R C),
      ∀ i, IsGroupLikeElem R (b i) := by
  obtain ⟨κ, inst, b, hb⟩ := exists_orthogonalIdempotent_basis e he hspan
  exact ⟨κ, inst, CoalgebraIdempotentBasis.primalBasis b,
    CoalgebraIdempotentBasis.isGroupLike_primalBasis b hb⟩

/-- Complete orthogonal idempotents spanning the reduced convolution dual
supply a group-like basis before reduction through a nilpotent ideal. -/
theorem exists_groupLike_basis_of_nilpotent_reduction
    (I : Ideal R) (hI : IsNilpotent I) {ι : Type v} [Fintype ι]
    (e : ι → WithConv (C →ₗ[R] R ⧸ I)) (he : CompleteOrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    ∃ (κ : Type v) (_ : Fintype κ) (b : Basis κ R C),
      ∀ i, IsGroupLikeElem R (b i) := by
  obtain ⟨e', he', _, hspan'⟩ :=
    CoalgebraNilpotentReduction.exists_lift_spanning_completeOrthogonalIdempotents
      I hI e he hspan
  exact exists_groupLike_basis e' he'.toOrthogonalIdempotents hspan'

/-- The full group-like family spans once the reduced dual has a spanning
complete orthogonal family. -/
theorem span_groupLike_eq_top_of_nilpotent_reduction
    (I : Ideal R) (hI : IsNilpotent I) {ι : Type v} [Fintype ι]
    (e : ι → WithConv (C →ₗ[R] R ⧸ I)) (he : CompleteOrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R {x : C | IsGroupLikeElem R x} = ⊤ := by
  obtain ⟨κ, inst, b, hb⟩ := exists_groupLike_basis_of_nilpotent_reduction I hI e he hspan
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_mono (Set.range_subset_iff.mpr hb)

omit [Module.Free R C] in
/-- A chosen finite group-like basis of a finite flat coalgebra over a local
ring, constructed from a split quotient-valued convolution dual. -/
def groupLikeBasisOfNilpotentReduction [Module.Flat R C]
    (I : Ideal R) (hI : IsNilpotent I) {ι : Type v} [Fintype ι]
    (e : ι → WithConv (C →ₗ[R] R ⧸ I)) (he : CompleteOrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    Σ κ : Type v, Σ _ : Fintype κ, {b : Basis κ R C // ∀ i, IsGroupLikeElem R (b i)} := by
  let : Module.Free R C := Module.free_of_flat_of_isLocalRing
  have h := exists_groupLike_basis_of_nilpotent_reduction I hI e he hspan
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

end Langlands.CoalgebraLocalSplit
