import Langlands.Algebra.LocalFiberwiseFlatnessStatement
import Langlands.Algebra.QuotientBaseChangeComparison
import Langlands.Algebra.IdealFiniteGenerationFromQuotientStability
import Langlands.Algebra.SurjectiveBaseChangeFlatnessTransport
import Langlands.Algebra.LocalPolynomialPresentationProof
import Langlands.Algebra.EssFinitePresentationTransportProof
import Langlands.Algebra.EssFinitePresentationFiniteQuotient
import Langlands.Algebra.LocalFiberInjectivity
import Langlands.Algebra.EssFinitePresentationFiberwiseFlatness
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.Submodule

/-! # Local fibrewise flatness for essentially finite type algebras -/

universe u v x w z

open scoped TensorProduct

namespace Langlands.Algebra

namespace LocalFiberwiseFlatnessProof

private theorem quotient_finitePresentation
    (B : Type v) [CommRing B] (I K : Ideal B) (hIK : I ≤ K) (hK : K.FG) :
    letI : Algebra (B ⧸ I) (B ⧸ K) := (Ideal.Quotient.factor hIK).toAlgebra
    Module.FinitePresentation (B ⧸ I) (B ⧸ K) := by
  let : Algebra (B ⧸ I) (B ⧸ K) := (Ideal.Quotient.factor hIK).toAlgebra
  apply Module.finitePresentation_of_surjective (Algebra.linearMap (B ⧸ I) (B ⧸ K))
    (Ideal.Quotient.factor_surjective hIK)
  change (RingHom.ker (Ideal.Quotient.factor hIK)).FG
  rw [Ideal.Quotient.factor_ker]
  exact hK.map (Ideal.Quotient.mk I)

private theorem quotient_factor_injective
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [IsLocalRing R] [Algebra R B] (I K : Ideal B) (hIK : I ≤ K)
    [IsLocalRing (B ⧸ I)] [IsLocalHom (algebraMap R (B ⧸ I))]
    (hK : K.FG) (hEFP : Langlands.Algebra.EssFinitePresentation R (B ⧸ I))
    (hflat : Module.Flat R (B ⧸ K))
    (hmap : I.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R)) =
      K.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R))) :
    Function.Injective (Ideal.Quotient.factor hIK) := by
  let : Algebra (B ⧸ I) (B ⧸ K) := (Ideal.Quotient.factorₐ R hIK).toRingHom.toAlgebra
  let : Module.FinitePresentation (B ⧸ I) (B ⧸ K) :=
    quotient_finitePresentation B I K hIK hK
  have hten := (Langlands.Algebra.quotientBaseChangeComparison R B
    (IsLocalRing.ResidueField R) I K hIK hmap).2.1
  exact (Langlands.Algebra.localFiberInjectivity.{u, v, v, v} R (B ⧸ I) (B ⧸ I) (B ⧸ K)
    (Algebra.linearMap (B ⧸ I) (B ⧸ K)) hEFP inferInstance inferInstance
    hflat hten).1

private theorem quotient_kernel_fg
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Algebra.EssFiniteType R B] (J : Ideal B) (hJ : J ≠ ⊤)
    (hEFP : ∀ I : Ideal B, I.FG → I ≤ J →
      Langlands.Algebra.EssFinitePresentation R (B ⧸ I))
    (hflat : ∀ I : Ideal B, I.FG → I ≤ J →
      I.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R)) =
        J.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R)) →
      Module.Flat R (B ⧸ I)) :
    J.FG := by
  let : IsNoetherianRing (IsLocalRing.ResidueField R ⊗[R] B) :=
    Algebra.EssFiniteType.isNoetherianRing (IsLocalRing.ResidueField R) _
  let : IsNoetherianRing (B ⊗[R] IsLocalRing.ResidueField R) :=
    isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.comm R (IsLocalRing.ResidueField R) B).toRingEquiv
  apply Langlands.Algebra.idealFiniteGenerationFromQuotientStability
    B (B ⊗[R] IsLocalRing.ResidueField R) (algebraMap B _) J
    (IsNoetherian.noetherian _)
  intro I K hI hK hIK hKJ hmapI
  have hIJ : I ≤ J := hIK.trans hKJ
  have hmapK : K.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R)) =
      J.map (algebraMap B (B ⊗[R] IsLocalRing.ResidueField R)) :=
    le_antisymm (Ideal.map_mono hKJ) (hmapI ▸ Ideal.map_mono hIK)
  let : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hJ hIJ)
  let : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R (B ⧸ I)) := by
    rw [IsScalarTower.algebraMap_eq R B (B ⧸ I)]
    infer_instance
  exact quotient_factor_injective R B I K hIK hK (hEFP I hI hIJ)
    (hflat K hK hKJ hmapK) (hmapI.trans hmapK.symm)

private theorem intermediate_flat
    (R : Type u) (A : Type v) (S : Type x) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing A] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing S] [IsLocalRing S']
    [Algebra R A] [Algebra R S] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] [IsLocalHom (algebraMap R A)]
    [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M] [IsScalarTower R S' M]
    (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (hEFP : Langlands.Algebra.EssFinitePresentation R A)
    (hS' : Langlands.Algebra.EssFinitePresentation R S')
    (hM : Module.FinitePresentation S' M) (hne : Nontrivial M)
    (hfibre : Module.Flat (S ⊗[R] IsLocalRing.ResidueField R)
      ((S ⊗[R] IsLocalRing.ResidueField R) ⊗[S] M))
    (hflat : Module.Flat R M)
    (hmap : Function.Bijective
      (Algebra.TensorProduct.map f (AlgHom.id R (IsLocalRing.ResidueField R)))) :
    Module.Flat R A := by
  let : Algebra A S := f.toRingHom.toAlgebra
  let g := (IsScalarTower.toAlgHom R S S').comp f
  let : Algebra A S' := g.toRingHom.toAlgebra
  let : Module A M := Module.compHom M (algebraMap A S')
  let : IsScalarTower A S' M := IsScalarTower.of_compHom A S' M
  let : IsScalarTower A S M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change f a • m = algebraMap S S' (f a) • m
      rw [IsScalarTower.algebraMap_smul]
  let : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change g (algebraMap R A r) • m = r • m
      rw [g.commutes, IsScalarTower.algebraMap_smul]
  let : IsLocalHom f.toRingHom := IsLocalHom.of_surjective _ hf
  let : IsLocalHom (algebraMap A S') := by
    change IsLocalHom ((algebraMap S S').comp f.toRingHom)
    infer_instance
  have htransport := Langlands.Algebra.surjectiveBaseChangeFlatnessTransport
    R A S (IsLocalRing.ResidueField R) M hf hmap hfibre
  exact (Langlands.Algebra.essFinitePresentationFiberwiseFlatness.{u, v, w, z}
    R A S' M hEFP hS' hM hne htransport hflat).1

private theorem presentation_efp
    (R : Type u) (B : Type v) (S : Type x) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing B] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing S] [IsLocalRing S']
    [Algebra R B] [Algebra R S] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] [IsLocalHom (algebraMap R B)]
    [IsLocalHom (algebraMap S S')] [Algebra.EssFiniteType R B]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M] [IsScalarTower R S' M]
    (f : B →ₐ[R] S) (hf : Function.Surjective f)
    (hEFP : ∀ I : Ideal B, I.FG → Langlands.Algebra.EssFinitePresentation R (B ⧸ I))
    (hS' : Langlands.Algebra.EssFinitePresentation R S')
    (hM : Module.FinitePresentation S' M) (hne : Nontrivial M)
    (hfibre : Module.Flat (S ⊗[R] IsLocalRing.ResidueField R)
      ((S ⊗[R] IsLocalRing.ResidueField R) ⊗[S] M))
    (hflat : Module.Flat R M) :
    Langlands.Algebra.EssFinitePresentation R S := by
  let J := RingHom.ker f
  let e : (B ⧸ J) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective hf
  have hJ : J.FG := by
    apply quotient_kernel_fg R B J
      (RingHom.ker_ne_top f) (fun I hI _ => hEFP I hI)
    intro I hI hIJ hmap
    let fI := e.toAlgHom.comp (Ideal.Quotient.factorₐ R hIJ)
    have hfI : Function.Surjective fI :=
      e.surjective.comp (Ideal.Quotient.factor_surjective hIJ)
    let : Nontrivial (B ⧸ I) := fI.toRingHom.domain_nontrivial
    let : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let : IsLocalHom (algebraMap R (B ⧸ I)) := by
      rw [IsScalarTower.algebraMap_eq R B (B ⧸ I)]
      infer_instance
    apply intermediate_flat R (B ⧸ I) S S' M fI hfI
      (hEFP I hI) hS' hM hne hfibre hflat
    have hcomp : Algebra.TensorProduct.map fI (AlgHom.id R (IsLocalRing.ResidueField R)) =
        (Algebra.TensorProduct.map e.toAlgHom
          (AlgHom.id R (IsLocalRing.ResidueField R))).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hIJ)
          (AlgHom.id R (IsLocalRing.ResidueField R))) := by
      simpa only [AlgHom.id_comp] using Algebra.TensorProduct.map_comp
        e.toAlgHom (Ideal.Quotient.factorₐ R hIJ)
        (AlgHom.id R (IsLocalRing.ResidueField R)) (AlgHom.id R (IsLocalRing.ResidueField R))
    rw [hcomp]
    exact (Algebra.TensorProduct.map_bijective e.bijective Function.bijective_id).comp
      (Langlands.Algebra.quotientBaseChangeComparison R B
        (IsLocalRing.ResidueField R) I J hIJ hmap).1
  obtain ⟨n, K, hK, U, ⟨eK⟩⟩ := hEFP J hJ
  exact ⟨n, K, hK, U, ⟨eK.trans e⟩⟩

end LocalFiberwiseFlatnessProof

/-- The local fibrewise flatness criterion, Stacks Project tag 05UV. -/
theorem localFiberwiseFlatness :
    Langlands.Algebra.LocalFiberwiseFlatnessStatement.{u, v, w, z} := by
  intro R S S' M instR instS instS' localR localS localS' algRS algSS' algRS'
    towerRSS' localRS localSS' instM modR modS modS' towerRSM towerSS'M towerRS'M
    hS' htype hM hne hfibre hflat
  obtain ⟨n, q, hq, hpres⟩ := Langlands.Algebra.localPolynomialPresentation R S htype
  let := hq
  obtain ⟨f, hf, hRB, _⟩ := hpres
  let : IsLocalHom (algebraMap R (Localization.AtPrime q)) := hRB
  have hlocalization : Langlands.Algebra.EssFinitePresentation R (Localization.AtPrime q) :=
    Langlands.Algebra.essFinitePresentation_of_isLocalization
      R (MvPolynomial (Fin n) R) (Localization.AtPrime q) q.primeCompl
  have hEFP : Langlands.Algebra.EssFinitePresentation R S :=
    LocalFiberwiseFlatnessProof.presentation_efp
      R (Localization.AtPrime q) S S' M f hf
      (fun I hI => Langlands.Algebra.essFinitePresentationFiniteQuotient
        R (Localization.AtPrime q) I hlocalization hI)
      hS' hM hne hfibre hflat
  exact ⟨hEFP, Langlands.Algebra.essFinitePresentationFiberwiseFlatness.{u, v, w, z}
    R S S' M hEFP hS' hM hne hfibre hflat⟩

end Langlands.Algebra
