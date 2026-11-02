import Langlands.AlgebraicGeometry.GroupoidCoactionFiniteEffectiveCover
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineQuotientPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Ring covering data from a finite affine scheme cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E' E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsAffine E.R]
  (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R) (h : E'.IsCartesianHom E f g)
  [IsFinite f] [Surjective f] (hQ : E'.HasAffineQuotient)

/-- An actual finite surjective cartesian affine-quotient cover gives the
ring-theoretic finite effective cover used in support induction. -/
noncomputable def finiteEffectiveCover :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    GroupoidCoaction.FiniteEffectiveCover E.t.appTop.hom := by
  classical
  apply Classical.choice
  let : IsAffine E'.U := isAffine_of_isAffineHom f
  obtain ⟨M, q, hM, hpb, hq⟩ := hQ
  have hQ : E'.HasAffineQuotient := ⟨M, q, hM, hpb, hq⟩
  let : IsAffine M := hM
  let : IsAffine E'.R := IsAffine.of_isPullback hpb
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  let : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hff, ε, hε⟩ := invariantPresentation_of_hasAffineQuotient E' hQ
  let : Module.FaithfullyFlat (GroupoidCoaction.invariantRing E'.t.appTop.hom)
    Γ(E'.U, ⊤) := hff
  let : Module.Finite Γ(E.U, ⊤) Γ(E'.U, ⊤) :=
    RingHom.finite_algebraMap.mp f.finite_appTop
  have hsurj : Function.Surjective (PrimeSpectrum.comap f.appTop.hom) := by
    have hspec : Surjective (Spec.map f.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)).mp
        inferInstance
    exact (surjective_iff (Spec.map f.appTop)).mp hspec
  exact
    ⟨{
      D := Γ(E'.U, ⊤)
      P := Γ(E'.R, ⊤)
      td := E'.t.appTop.hom
      relation := ringRelation_of_hasAffineQuotient E' hQ
      e := sourceTensorEquiv E' E f g h
      cartesian := sourceTensorEquiv_target E' E f g h
      ε := ε.symm
      ε_target := fun d => by rw [← hε d, ε.symm_apply_apply]
      comap_surjective := hsurj }⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
