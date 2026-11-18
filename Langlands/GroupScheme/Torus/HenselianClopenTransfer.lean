import Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift
import Langlands.GroupScheme.Torus.LocalClopenFibre
import Langlands.GroupScheme.HomScheme.FiniteSourceHom

/-! # Transfer of etale Hom families into a prescribed Henselian local algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.HomScheme Langlands.GroupScheme.HomScheme.FiniteSource

namespace Langlands.GroupScheme.HenselianClopenTransfer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem specMap_comp {P E B A : Type u} [CommRing P]
    [CommRing E] [Algebra P E] [CommRing B] [Algebra P B]
    [CommRing A] [Algebra P A] (f : E →ₐ[P] B) (g : B →ₐ[P] A) :
    specMap g ≫ specMap f = specMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- An etale family with a special-fibre isomorphism evaluates to a clopen
homomorphism over any prescribed Henselian local algebra with that residue point. -/
theorem exists_clopen_evaluation
    {P A K E : Type u} [CommRing P] [CommRing A] [HenselianLocalRing A]
    [Algebra P A] [Field K] [Algebra A K] [Algebra P K] [IsScalarTower P A K]
    [CommRing E] [Algebra P E] [Algebra.Etale P E] [IsNoetherianRing E]
    (C D : GroupScheme (Spec (CommRingCat.of P)))
    [IsAffine D.X.left] [LocallyOfFiniteType D.X.hom]
    (hC : RelativeMultiplicativeType.IsDiagonalizable C)
    (j : RelativeHom C D (specOver P E))
    (φ : E →ₐ[P] K) (hK : Function.Surjective (algebraMap A K))
    [IsIso (evaluate (specMap φ) j)] :
    ∃ σ : E →ₐ[P] A, ((Algebra.ofId A K).restrictScalars P).comp σ = φ ∧
      IsOpenImmersion (evaluate (specMap σ) j).hom.hom.left ∧
      IsClosedImmersion (evaluate (specMap σ) j).hom.hom.left := by
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨σ, σloc, hσ, hσloc⟩ :=
    Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift.exists_local_lift hK φ
  let B := Localization.AtPrime Q
  let l : E →ₐ[P] B := IsScalarTower.toAlgHom P E B
  let ρloc : B →ₐ[P] K := ((Algebra.ofId A K).restrictScalars P).comp σloc
  have hρcomp : ρloc.comp l = φ := by
    dsimp only [ρloc]
    rw [AlgHom.comp_assoc, hσloc, hσ]
  have hker : RingHom.ker ρloc.toRingHom = IsLocalRing.maximalIdeal B := by
    apply (IsLocalization.orderEmbedding Q.primeCompl B).injective
    change Ideal.comap (algebraMap E B) (RingHom.ker ρloc.toRingHom) =
      (IsLocalRing.maximalIdeal B).under E
    rw [RingHom.comap_ker]
    have hring : ρloc.toRingHom.comp (algebraMap E B) = φ.toRingHom :=
      congrArg AlgHom.toRingHom hρcomp
    rw [hring]
    exact (Localization.AtPrime.under_maximalIdeal (I := Q)).symm
  let : Algebra B K := ρloc.toRingHom.toAlgebra
  let jloc : RelativeHom C D (specOver P B) := evaluate (specMap l) j
  have heval : evaluate (specMap ρloc) jloc = evaluate (specMap φ) j := by
    dsimp only [jloc]
    rw [← evaluate_comp, specMap_comp, hρcomp]
  have : IsIso (evaluate (specMap ρloc) jloc) := by
    rw [heval]
    infer_instance
  have : IsIso ((baseChange (Spec.algebraMap B K)).map jloc) :=
    (LocalClopenFibre.isIso_evaluate_iff (specMap ρloc) jloc).mp inferInstance
  have : IsAffine ((baseChange (specOver P B).hom).obj D).X.left := by
    change IsAffine (CategoryTheory.Limits.pullback D.X.hom (Spec.algebraMap P B))
    infer_instance
  have : LocallyOfFiniteType ((baseChange (specOver P B).hom).obj D).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.X.hom (Spec.algebraMap P B))
    infer_instance
  obtain ⟨hop, hcl⟩ := LocalClopenFibre.clopen_of_field_fibre_isIso hker
    (hC.baseChange (specOver P B).hom) jloc
  have hσeval : evaluate (specMap σloc) jloc = evaluate (specMap σ) j := by
    dsimp only [jloc]
    rw [← evaluate_comp, specMap_comp, hσloc]
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [← hσeval]
    exact LocalClopenFibre.isOpenImmersion_evaluate (specMap σloc) jloc hop
  · rw [← hσeval]
    exact isClosedImmersion_evaluate (specMap σloc) jloc hcl

end Langlands.GroupScheme.HenselianClopenTransfer
