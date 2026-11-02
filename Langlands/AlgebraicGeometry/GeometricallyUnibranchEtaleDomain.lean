import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain
import Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange

/-! # Etale local domains over geometrically unibranch local domains -/

universe u v w

open IsLocalRing
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace GeometricallyUnibranchEtaleDomain

lemma isLocalRing_of_residue_quotient
    {D C E : Type*} [CommRing D] [CommRing C] [CommRing E]
    [Nontrivial D] [IsLocalRing C]
    (f : D →+* E) (hf : Function.Surjective f)
    (h : C →+* E) (hh : h.IsIntegral)
    (hinj : Function.Injective (PrimeSpectrum.comap h))
    (hker : ∀ P : Ideal D, P.IsMaximal → RingHom.ker f ≤ P) :
    IsLocalRing D := by
  have huniq (P Q : Ideal D) [P.IsMaximal] [Q.IsMaximal] : P = Q := by
    have hP : RingHom.ker f ≤ P := hker P inferInstance
    have hQ : RingHom.ker f ≤ Q := hker Q inferInstance
    have : (P.map f).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le hf hP
    have : (Q.map f).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le hf hQ
    have hPc : (P.map f).comap h = maximalIdeal C :=
      eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal h hh _)
    have hQc : (Q.map f).comap h = maximalIdeal C :=
      eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal h hh _)
    have heq : P.map f = Q.map f :=
      congrArg PrimeSpectrum.asIdeal (hinj
        (a₁ := ⟨P.map f, inferInstance⟩) (a₂ := ⟨Q.map f, inferInstance⟩)
        (PrimeSpectrum.ext (hPc.trans hQc.symm)))
    have hp := P.comap_map_of_surjective f hf
    have hq := Q.comap_map_of_surjective f hf
    rw [← RingHom.ker_eq_comap_bot, sup_of_le_left hP] at hp
    rw [← RingHom.ker_eq_comap_bot, sup_of_le_left hQ] at hq
    exact hp.symm.trans ((congrArg (Ideal.comap f) heq).trans hq)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (α := D)
  exact IsLocalRing.of_unique_max_ideal
    ⟨P, hP, fun Q hQ => @huniq Q P hQ hP⟩

lemma isLocalRing_tensor_of_integral_of_pure_residue
    (R : Type u) (N : Type v) (B : Type w)
    [CommRing R] [IsLocalRing R] [CommRing N] [IsLocalRing N]
    [CommRing B] [IsLocalRing B] [Algebra R N] [Algebra R B]
    [IsLocalHom (algebraMap R N)] [IsLocalHom (algebraMap R B)]
    [Algebra.IsIntegral R N] [Nontrivial (N ⊗[R] B)]
    (hpure : IsPurelyInseparable (ResidueField R) (ResidueField N)) :
    IsLocalRing (N ⊗[R] B) := by
  let := hpure
  let : Algebra B (N ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsIntegral B (N ⊗[R] B) :=
    (Algebra.TensorProduct.commRight R B N).isIntegral_iff.mp inferInstance
  let fN : N →ₐ[R] ResidueField N := IsScalarTower.toAlgHom R N _
  let f := Algebra.TensorProduct.map fN (AlgHom.id R B)
  let hRN := IsScalarTower.toAlgHom R (ResidueField R) (ResidueField N)
  let h := Algebra.TensorProduct.map hRN (AlgHom.id R B)
  have hf : Function.Surjective f :=
    Algebra.TensorProduct.map_surjective _ _ residue_surjective Function.surjective_id
  have hh : h.toRingHom.IsIntegral := by
    let e : ResidueField N ⊗[R] B ≃ₐ[ResidueField R]
        ResidueField N ⊗[ResidueField R] (ResidueField R ⊗[R] B) :=
      (Algebra.TensorProduct.cancelBaseChange R (ResidueField R) (ResidueField R)
        (ResidueField N) B).symm
    have hcomp : h =
        (e.symm.toAlgHom.restrictScalars R).comp
          ((Algebra.TensorProduct.includeRight :
            ResidueField R ⊗[R] B →ₐ[ResidueField R]
              ResidueField N ⊗[ResidueField R] (ResidueField R ⊗[R] B)).restrictScalars R) := by
      ext
      · simp [h, hRN, e, Algebra.algebraMap_eq_smul_one]
      · simp [h, hRN, e]
    let : Algebra (ResidueField R ⊗[R] B)
        (ResidueField N ⊗[ResidueField R] (ResidueField R ⊗[R] B)) :=
      Algebra.TensorProduct.rightAlgebra
    have hi : Algebra.IsIntegral (ResidueField R ⊗[R] B)
        (ResidueField N ⊗[ResidueField R] (ResidueField R ⊗[R] B)) :=
      (Algebra.TensorProduct.commRight (ResidueField R)
        (ResidueField R ⊗[R] B) (ResidueField N)).isIntegral_iff.mp inferInstance
    rw [hcomp]
    change (e.symm.toRingHom.comp (algebraMap
      (ResidueField R ⊗[R] B)
      (ResidueField N ⊗[ResidueField R] (ResidueField R ⊗[R] B)))).IsIntegral
    exact RingHom.IsIntegral.trans _ _ (algebraMap_isIntegral_iff.mpr hi)
      (e.symm.toRingHom.isIntegral_of_surjective e.symm.surjective)
  apply isLocalRing_of_residue_quotient f.toRingHom hf h.toRingHom hh
    (PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (ResidueField R) R B (ResidueField N)).injective
  intro P hP
  let := hP
  have hPB : P.under B = maximalIdeal B := eq_maximalIdeal inferInstance
  have hPR : P.under R = maximalIdeal R := by
    rw [← Ideal.under_under (A := R) (B := B), hPB]
    exact maximalIdeal_comap (algebraMap R B)
  have hPN : P.under N = maximalIdeal N := by
    apply eq_maximalIdeal
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    simpa only [Ideal.under_under] using hPR ▸ maximalIdeal.isMaximal R
  change RingHom.ker (Algebra.TensorProduct.map fN (AlgHom.id R B)) ≤ P
  rw [Algebra.TensorProduct.rTensor_ker _ residue_surjective]
  change (RingHom.ker (residue N)).map
    (Algebra.TensorProduct.includeLeft : N →ₐ[R] N ⊗[R] B) ≤ P
  rw [ker_residue, Ideal.map_le_iff_le_comap]
  exact le_of_eq hPN.symm

lemma isDomain_of_local_localization
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [IsLocalRing C] (M : Submonoid A) [IsLocalization M C]
    (H : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q)) :
    IsDomain C := by
  let q : Ideal A := (maximalIdeal C).under A
  have : q.IsPrime := inferInstance
  have : IsLocalization.AtPrime C q := by
    apply IsLocalization.of_le M q.primeCompl
    · intro x hx
      exact notMem_maximalIdeal.mpr (IsLocalization.map_units C ⟨x, hx⟩)
    · intro x hx
      exact notMem_maximalIdeal.mp hx
  have := H q
  let e := IsLocalization.algEquiv q.primeCompl C (Localization.AtPrime q)
  exact e.toRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance

lemma isDomain_of_etale_localization
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [IsLocalHom (algebraMap R B)]
    (M : Submonoid A) [IsLocalization M B]
    (hR : GeometricallyUnibranchDomain R) :
    IsDomain B := by
  let N := integralClosure R (FractionRing R)
  have : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  obtain ⟨hN, hlocal, hpure⟩ := hR
  let : IsLocalRing N := hN
  let : IsLocalHom (algebraMap R N) := hlocal
  have hmap : ResidueField.map (algebraMap R N) =
      algebraMap (ResidueField R) (ResidueField N) := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl
  have hpure' : IsPurelyInseparable (ResidueField R) (ResidueField N) := by
    rw [← RingHom.isPurelyInseparable_algebraMap_iff, ← hmap]
    exact hpure
  have : Module.Flat A B := IsLocalization.flat B M
  have : Module.Flat R B := .trans R A B
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[R] N ⊗[R] B) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective R N)
  have : Nontrivial (N ⊗[R] B) := Function.Injective.nontrivial hinj
  have : IsLocalRing (N ⊗[R] B) :=
    isLocalRing_tensor_of_integral_of_pure_residue R N B hpure'
  let MT : Submonoid (N ⊗[R] A) :=
    M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] N ⊗[R] A)
  let f : N ⊗[R] A →ₐ[N] N ⊗[R] B :=
    Algebra.TensorProduct.map (AlgHom.id N N) (IsScalarTower.toAlgHom R A B)
  let : Algebra (N ⊗[R] A) (N ⊗[R] B) := f.toRingHom.toAlgebra
  have : IsScalarTower N (N ⊗[R] A) (N ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalization MT (N ⊗[R] B) := by
    apply IsLocalization.tensorProduct_tensorProduct_right R N M B
    ext x
    change f (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] (algebraMap A B x)
    simp [f]
  have : IsDomain (N ⊗[R] B) := by
    apply isDomain_of_local_localization (N ⊗[R] A) (N ⊗[R] B) MT
    intro q hq
    exact Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof.domain_localizations_of_etale_of_integrallyClosed
        Langlands.CommutativeAlgebra.integrallyClosedInReducedArtinianDomainLocalizations
        N (N ⊗[R] A) q
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.includeRight : B →ₐ[R] N ⊗[R] B) hinj

lemma isDomain_atPrime_of_local_base
    (R : Type u) (A : Type v)
    [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime p))]
    (hR : GeometricallyUnibranchDomain R) :
    IsDomain (Localization.AtPrime p) :=
  isDomain_of_etale_localization R A (Localization.AtPrime p) p.primeCompl hR

lemma isDomain_atPrime_of_geometricallyUnibranch
    (R : Type u) (A : Type v) (Rp : Type w)
    [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime]
    [CommRing Rp] [IsDomain Rp] [IsLocalRing Rp]
    [Algebra R Rp] [IsLocalization.AtPrime Rp (p.under R)]
    (hRp : GeometricallyUnibranchDomain Rp) :
    IsDomain (Localization.AtPrime p) := by
  let B := Localization.AtPrime p
  let e : Rp ≃ₐ[R] Localization.AtPrime (p.under R) :=
    IsLocalization.algEquiv (p.under R).primeCompl _ _
  let h : Localization.AtPrime (p.under R) →ₐ[R] B :=
    Localization.localAlgHom (p.under R) p (Algebra.ofId R A) rfl
  have : IsLocalHom h.toRingHom :=
    Localization.isLocalHom_localRingHom _ _ _ rfl
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let f : Rp →ₐ[R] B := h.comp e.toAlgHom
  let : Algebra Rp B := f.toRingHom.toAlgebra
  have : IsScalarTower R Rp B :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalHom (algebraMap Rp B) := by
    change IsLocalHom (h.toRingHom.comp e.toRingHom)
    infer_instance
  let C := Rp ⊗[R] A
  let : Algebra A C := Algebra.TensorProduct.rightAlgebra
  let g : C →ₐ[Rp] B :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp B) (IsScalarTower.toAlgHom R A B)
      (fun _ _ => mul_comm _ _)
  let : Algebra C B := g.toRingHom.toAlgebra
  have : IsScalarTower Rp C B :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : IsScalarTower A C B := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap A B x = algebraMap Rp B 1 * algebraMap A B x
    rw [map_one, one_mul]
  have hle : Algebra.algebraMapSubmonoid A (p.under R).primeCompl ≤ p.primeCompl := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have : IsLocalization
      (p.primeCompl.map (algebraMap A C)) B :=
    IsLocalization.isLocalization_of_submonoid_le C B
      (Algebra.algebraMapSubmonoid A (p.under R).primeCompl) p.primeCompl hle
  exact isDomain_of_etale_localization Rp C B
    (p.primeCompl.map (algebraMap A C)) hRp

end GeometricallyUnibranchEtaleDomain

end Langlands.AlgebraicGeometry
