import Langlands.Representation.Archimedean.ComplexUnitaryStandardConjugation
import Langlands.Representation.Archimedean.ComplexUnitaryStandardTransport
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction

/-! The intertwiner defined by a positive form and the resulting symmetry of the parameters. -/

noncomputable section

open scoped ComplexConjugate Matrix MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexDuality ComplexStandardHomTransposeProof

variable {n : ℕ}

/-- The duality integral between the series induced from the Hermitian-dual and conjugate
characters. -/
def hermitianPairing (n : ℕ) (ds : List ComplexCharacterData) :
    ComplexBlock.KFs n (ds.map hermitianData) →ₗ[ℂ] ComplexBlock.KFs n (ds.map conjugateData) →ₗ[ℂ] ℂ :=
  integralPairing n (complexPositionCharacter (ds.map hermitianData))
    (complexPositionCharacter (ds.map conjugateData))

private theorem hermitian_conjugate_mul (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ) :
    complexPositionCharacter (ds.map hermitianData) i z *
      complexPositionCharacter (ds.map conjugateData) i z = 1 := by
  rw [show ds.map hermitianData = (ds.map conjugateData).map complexCharacterDataInv by
    rw [List.map_map]
    rfl]
  exact complexPositionCharacter_map_inv_mul (ds.map conjugateData) i z

/-- A positive invariant form defines an injective intertwiner into the Hermitian-dual
principal series. Its pairing with a pointwise conjugate compact-finite vector recovers
exactly the original positive form. -/
theorem exists_hermitianIntertwiner (ds : List ComplexCharacterData)
    (b : InvariantPositiveForm (complexStandardRep n ds))
    (hb : ∀ (X : Matrix (Fin n) (Fin n) ℂ) v w,
      b.inner (complexStandardLie n ds (1 ⊗ₜ X) v) w +
        b.inner v (complexStandardLie n ds (1 ⊗ₜ X) w) = 0) :
    ∃ T : ComplexBlock.KFs n ds →ₗ[ℂ] ComplexBlock.KFs n (ds.map hermitianData),
      Function.Injective T ∧
      IsComplexStandardIntertwining n (complexStandardRep n (ds.map hermitianData))
        (complexStandardLie n (ds.map hermitianData)) ds T ∧
      ∀ v w, hermitianPairing n ds (T v) (conjugateStandard ds w) = b.inner w v := by
  let cs := ds.map conjugateData
  let hs := ds.map hermitianData
  let C := fromConjugateStandard (n := n) ds
  let Q := hermitianPairing n ds
  let : InnerProductSpace.Core ℂ (ComplexBlock.KFs n ds) := b.toInnerProductCore
  let Λ : ComplexBlock.KFs n ds →ₗ[ℂ] Module.Dual ℂ (ComplexBlock.KFs n cs) :=
    LinearMap.mk₂ ℂ (fun v f => b.inner (C f) v)
      (fun v w f => InnerProductSpace.Core.inner_add_right (C f) v w)
      (fun c v f => InnerProductSpace.Core.inner_smul_right (C f) v)
      (fun v f g => by rw [map_add, b.add_left])
      (fun c v f => by
        rw [map_smulₛₗ, b.smul_left]
        simp only [starRingEnd_apply, star_star, smul_eq_mul])
  have hΛapp (v : ComplexBlock.KFs n ds) (f : ComplexBlock.KFs n cs) : Λ v f = b.inner (C f) v := rfl
  have hΛK (k : Matrix.unitaryGroup (Fin n) ℂ) (v : ComplexBlock.KFs n ds) :
      Λ (complexStandardRep n ds k v) = (complexStandardRep n cs).dual k (Λ v) := by
    apply LinearMap.ext
    intro f
    rw [KFiniteDual.dual_apply_apply, hΛapp, hΛapp]
    have e := b.invariant k (C (complexStandardRep n cs k⁻¹ f)) v
    change b.inner (complexStandardRep n ds k
      (fromConjugateStandard ds (complexStandardRep n cs k⁻¹ f)))
      (complexStandardRep n ds k v) = _ at e
    rw [fromConjugateStandard_rep, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply] at e
    exact e
  have hQK (k : Matrix.unitaryGroup (Fin n) ℂ) (g : ComplexBlock.KFs n hs) :
      Q (complexStandardRep n hs k g) = (complexStandardRep n cs).dual k (Q g) := by
    apply LinearMap.ext
    intro f
    rw [KFiniteDual.dual_apply_apply]
    have e := integralPairing_principalSeriesRep (complexPositionCharacter hs)
      (complexPositionCharacter cs) k g (complexStandardRep n cs k⁻¹ f)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have gkds := isComplexGKModule_complexStandardModule n ds
  have gkcs := isComplexGKModule_complexStandardModule n cs
  have gkhs := isComplexGKModule_complexStandardModule n hs
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ]
      (complexStandardRep n cs).asModule :=
    KFiniteDual.isSemisimpleModule gkcs.1 gkcs.2.1
  have hblock := KFiniteDual.finiteDimensional_block gkcs.1 gkcs.2.1
    (isAdmissibleGKModule_principalSeriesRep (n := n) (complexPositionCharacter cs))
  let W : Subrepresentation (complexStandardRep n cs).dual :=
    { toSubmodule := LinearMap.range Q
      apply_mem_toSubmodule := by
        rintro k _ ⟨g, rfl⟩
        exact ⟨complexStandardRep n hs k g, hQK k g⟩ }
  have hW : ∀ w ∈ W, FiniteVectors.IsFiniteVector (complexStandardRep n cs).dual w := by
    rintro _ ⟨g, rfl⟩
    exact isFiniteVector_dual_of_equivariant Q hQK (gkhs.1 g)
  obtain ⟨sh, hh⟩ := exists_normSq_complexPositionCharacter hs
  obtain ⟨sc, hc⟩ := exists_normSq_complexPositionCharacter cs
  have hsep : ∀ f, (∀ w ∈ W, w f = 0) → f = 0 := by
    intro f hf
    by_contra hne
    obtain ⟨g, hg⟩ := exists_integralPairing_ne_zero_left (hermitian_conjugate_mul ds) hh f hne
    exact hg (hf _ ⟨g, rfl⟩)
  have hrange (v : ComplexBlock.KFs n ds) : Λ v ∈ LinearMap.range Q :=
    KFiniteDual.mem_of_separating hblock W hW hsep
      (isFiniteVector_dual_of_equivariant Λ hΛK (gkds.1 v))
  have hQinj : Function.Injective Q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    by_contra hne
    obtain ⟨f, hf⟩ := exists_integralPairing_ne_zero_right (hermitian_conjugate_mul ds) hc g hne
    exact hf (by change Q g f = 0; rw [hg, LinearMap.zero_apply])
  let T : ComplexBlock.KFs n ds →ₗ[ℂ] ComplexBlock.KFs n hs :=
    (LinearEquiv.ofInjective Q hQinj).symm.toLinearMap ∘ₗ
      Λ.codRestrict (LinearMap.range Q) hrange
  have hT (v : ComplexBlock.KFs n ds) (f : ComplexBlock.KFs n cs) : Q (T v) f = b.inner (C f) v := by
    have e := congrArg Subtype.val
      ((LinearEquiv.ofInjective Q hQinj).apply_symm_apply
        (Λ.codRestrict (LinearMap.range Q) hrange v))
    rw [LinearEquiv.ofInjective_apply] at e
    exact congrArg (fun ℓ => ℓ f) e
  have hTdiag (v w : ComplexBlock.KFs n ds) :
      Q (T v) (conjugateStandard ds w) = b.inner w v := by
    rw [hT]
    simp [C]
  refine ⟨T, ?_, isComplexStandardIntertwining_of ?_ ?_, hTdiag⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply b.definite
    rw [← hTdiag v v, hv, map_zero, LinearMap.zero_apply]
  · intro k v
    apply hQinj
    apply LinearMap.ext
    intro f
    rw [hQK, KFiniteDual.dual_apply_apply, hT, hT, ← hΛapp, ← hΛapp, hΛK,
      KFiniteDual.dual_apply_apply]
  · intro X v
    apply hQinj
    apply LinearMap.ext
    intro f
    have e := integralPairing_principalSeriesLie (hermitian_conjugate_mul ds) X (T v) f
    change Q (complexStandardLie n hs (1 ⊗ₜ X) (T v)) f +
      Q (T v) (complexStandardLie n cs (1 ⊗ₜ X) f) = 0 at e
    rw [hT, show C (complexStandardLie n cs (1 ⊗ₜ X) f) =
      complexStandardLie n ds (1 ⊗ₜ X) (C f) from fromConjugateStandard_lie ds X f] at e
    rw [hT]
    linear_combination hb X (C f) v - e

/-- An irreducible unitarizable principal series has a multiset of parameters stable under
Hermitian duality. Sorting puts the source in Langlands order and its dual in opposite order. -/
theorem perm_hermitianData_of_irreducible_unitarizable (ds : List ComplexCharacterData)
    (hn : ds.length = n)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds))
    (hU : IsComplexUnitarizableGKModule n (complexStandardRep n ds) (complexStandardLie n ds)) :
    ds.Perm (ds.map hermitianData) := by
  let es := ds.mergeSort complexLanglandsLE
  have hes : es.Perm ds := List.mergeSort_perm _ _
  have hlen : es.length = n := hes.length_eq.trans hn
  obtain ⟨S, hSbij, hS⟩ := complexStandardPermutation n ds es hn hes hirr
  obtain ⟨b, hb⟩ := isComplexUnitarizableGKModule_standard_of_injective hS hSbij.injective hU
  obtain ⟨T, hTinj, hT, _⟩ := exists_hermitianIntertwiner es b hb
  have horder : IsComplexLanglandsOrdered es := isComplexLanglandsOrdered_mergeSort ds
  have hopen : (es.map hermitianData).Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) := by
    rw [List.pairwise_map]
    exact horder.imp fun h => by simpa only [hermitianData_re, neg_le_neg_iff] using h
  have hT0 : T ≠ 0 := by
    have : Nontrivial (ComplexBlock.KFs n es) := complexStandardNontrivial n es hlen
    obtain ⟨v, hv⟩ := exists_ne (0 : ComplexBlock.KFs n es)
    exact fun h => hv (hTinj (by simp [h]))
  have hperm := complexStandardOppositeOrderHom n es (es.map hermitianData) T hlen
    (by simpa only [List.length_map] using hlen) horder hopen hT0 hT
  exact hes.symm.trans (hperm.trans (hes.map hermitianData))

end Langlands.Archimedean.ComplexUnitary
