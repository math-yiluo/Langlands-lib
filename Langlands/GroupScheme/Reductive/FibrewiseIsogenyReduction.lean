import Langlands.GroupScheme.Reductive.FibrewiseIsogenyStatement
import Langlands.AbelianScheme.FiberwiseIsogeny
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient

/-! # General reductions for fibrewise isogenies of smooth affine groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A homomorphism is an isogeny on every residue-field fibre of its base. -/
def IsFibrewiseIsogeny (f : G ⟶ H) : Prop :=
  ∀ s : S, IsIsogeny ((baseChange (S.fromSpecResidueField s)).map f)

/-- Fibrewise isogenies between smooth groups are flat. -/
theorem flat_of_isogeny_fibres (f : G ⟶ H)
    [Smooth G.X.hom] [Smooth H.X.hom]
    (hf : IsFibrewiseIsogeny f) :
    Flat f.hom.hom.left :=
  Langlands.AlgebraicGeometry.fiberwiseFlatness S G.X H.X f.hom.hom
    inferInstance inferInstance inferInstance fun s => (hf s).2.1

/-- Fibrewise isogenies are surjective without any smoothness hypothesis. -/
theorem surjective_of_isogeny_fibres (f : G ⟶ H)
    (hf : IsFibrewiseIsogeny f) :
    Surjective f.hom.hom.left :=
  surjective_of_fiber f.hom.hom fun s => (hf s).2.2

/-- Fibrewise isogenies with locally finite-type source are locally quasi-finite. -/
theorem locallyQuasiFinite_of_isogeny_fibres (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom]
    (hf : IsFibrewiseIsogeny f) :
    LocallyQuasiFinite f.hom.hom.left := by
  have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have := locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  exact finite_preimage_singleton_of_fiber f.hom.hom fun s y => by
    have : IsFinite ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left :=
      (hf s).1
    exact Scheme.Hom.finite_preimage_singleton _ y

/-- Under the fibrewise-isogeny hypotheses for smooth affine groups, the
remaining condition is finiteness of the actual scheme-theoretic kernel. -/
theorem isogeny_iff_finite_kernel_of_isogeny_fibres (f : G ⟶ H)
    [Smooth G.X.hom] [Smooth H.X.hom] [IsAffineHom G.X.hom]
    [IsAffineHom H.X.hom]
    (hf : IsFibrewiseIsogeny f) :
    IsIsogeny f ↔ IsFinite (kernel f).X.hom := by
  have : Flat f.hom.hom.left := flat_of_isogeny_fibres f hf
  have : Surjective f.hom.hom.left := surjective_of_isogeny_fibres f hf
  have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : QuasiCompact f.hom.hom.left :=
    QuasiCompact.of_comp _ H.X.hom
  constructor
  · intro h
    have := h.1
    exact MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  · intro h
    let := h
    exact ⟨isFinite_of_finite_kernel f, inferInstance, inferInstance⟩

end Langlands.GroupScheme
