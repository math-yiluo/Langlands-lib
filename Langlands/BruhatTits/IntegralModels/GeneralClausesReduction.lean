import Langlands.BruhatTits.IntegralModels.ModelMorphism
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # The torus clause of KP Axiom 4.1.22 follows from a unipotent kernel

For every supplied relative-component model morphism, a unipotent
scheme-theoretic kernel of the neutral special-fibre map forces every closed
torus of the source special fibre to map by a closed immersion. Hence the
general special-fibre clauses of KP Axiom 4.1.22 reduce to part (1).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

/-- A unipotent kernel of the neutral special-fibre map gives the torus
clause of the preamble of KP Axiom 4.1.22. -/
theorem preservesTori_of_isUnipotent_kernel
    (h : IsUnipotent φ.specialFibreKernel) : φ.PreservesTori := by
  intro T i hT hi
  have : IsAffineHom target.neutral.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd target.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : LocallyOfFiniteType target.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd target.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : IsAffineHom source.neutral.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd source.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : LocallyOfFiniteType source.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd source.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : LocallyOfFiniteType φ.specialFibreKernel.X.hom := by
    rw [← Over.w (kernelι φ.neutralSpecialFibreMap).hom.hom]
    infer_instance
  have : IsAffineHom φ.specialFibreKernel.X.hom := by
    rw [← Over.w (kernelι φ.neutralSpecialFibreMap).hom.hom]
    infer_instance
  exact IsUnipotent.closed_torus_quotient unipotentClosedSubgroup h hT
    (kernelι φ.neutralSpecialFibreMap) i hi φ.neutralSpecialFibreMap le_rfl

/-- The general special-fibre clauses of KP Axiom 4.1.22 are equivalent to
part (1) alone: a smooth connected unipotent kernel. -/
theorem satisfiesGeneralSpecialFibreClauses_iff :
    φ.SatisfiesGeneralSpecialFibreClauses ↔ φ.HasSmoothConnectedUnipotentKernel :=
  ⟨And.right, fun h => ⟨φ.preservesTori_of_isUnipotent_kernel h.2.2, h⟩⟩

end RelativeComponentModelHom

end Langlands.BruhatTits.IntegralModels
