import Langlands.LocalFactor.CommonClosureBoundedBrauer

/-!
# Unitary classes factoring through a finite Galois quotient, after transport

Let `q` be a homomorphism from the absolute Galois group of a p-adic field `K`
to a finite group. The closure `N_q` of the kernel of `q ∘ proj` in the actual
local Weil group `W_K` is an open normal subgroup of finite index, and every
continuous irreducible class factoring through `q ∘ proj` is trivial on it. For
a topological isomorphism `T : W_K ≅ W_F` with the Weil group of another p-adic
field, the exact class of every unitary virtual class of `W_K` supported on
classes factoring through `q` is the restriction along `T` of an integral
combination of inductions `Ind_{W_L}^{W_F} η` with `T(N_q) ⊆ W_L` and `η`
trivial on `T(N_q)`.
-/

noncomputable section

universe uK uF uV uQ

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {Q : Type uQ} [Group Q] [Finite Q]
  (q : Field.absoluteGaloisGroup K.Carrier →* Q)

/-- The closure in `W_K` of the kernel of `q ∘ proj`, where `proj` is the
projection of the actual local Weil group to the absolute Galois group. -/
def factoringKernelClosure : Subgroup (localWeilGroup K) :=
  (q.comp (localProjection K).toMonoidHom).ker.topologicalClosure

omit [Finite Q] in
theorem ker_le_factoringKernelClosure :
    (q.comp (localProjection K).toMonoidHom).ker ≤ factoringKernelClosure K q :=
  Subgroup.le_topologicalClosure _

instance factoringKernelClosure_normal : (factoringKernelClosure K q).Normal :=
  Subgroup.is_normal_topologicalClosure _

instance factoringKernelClosure_finiteIndex : (factoringKernelClosure K q).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ker_le_factoringKernelClosure K q)

theorem factoringKernelClosure_isOpen :
    IsOpen (factoringKernelClosure K q : Set (localWeilGroup K)) :=
  Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.isClosed_topologicalClosure _)

omit [Finite Q] in
/-- A continuous irreducible class factoring through `q ∘ proj` has a continuous
representative trivial on `factoringKernelClosure K q`; its exact class is the
realization of the basis generator. -/
theorem exists_realizeExact_generator_eq
    (b : VirtualRepresentation.Weil.IrreducibleBasis.{uK, uV} (localWeilGroup K))
    (hb : VirtualRepresentation.Weil.FactorsThrough (localWeilGroup K)
      (q.comp (localProjection K).toMonoidHom) b) :
    ∃ (B : FiniteRepresentation.{0, uK, uV} ℂ (localWeilGroup K)) (hc : B.IsContinuous),
      (∀ w ∈ factoringKernelClosure K q, B.representation w = 1) ∧
      VirtualRepresentation.Weil.realizeExact (localWeilGroup K) (generator b) =
        ExactGrothendieckGroup.ofRepresentation
          (fun A : FiniteRepresentation.{0, uK, uV} ℂ (localWeilGroup K) => A.IsContinuous)
          ⟨B, hc⟩ := by
  obtain ⟨A, hA⟩ := hb
  obtain ⟨a, ha⟩ := Quotient.exists_rep b.2.val
  refine ⟨a.val, a.property.1, ?_, ?_⟩
  · have hcl : FiniteRepresentation.classOf (FiniteRepresentation.of
        (A.representation.comp (q.comp (localProjection K).toMonoidHom))) =
        FiniteRepresentation.classOf a.val := by
      rw [hA, VirtualRepresentation.Weil.underlyingClass, ← ha]
      rfl
    obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff _ _).mp hcl
    have hker : (q.comp (localProjection K).toMonoidHom).ker ≤ a.val.representation.ker := by
      intro w hw
      rw [MonoidHom.mem_ker] at hw ⊢
      rw [← Representation.Equiv.conj_apply_self w e]
      change e.conj (A.representation ((q.comp (localProjection K).toMonoidHom) w)) = 1
      rw [hw, map_one]
      exact LinearEquiv.conj_id _
    have hcl' : factoringKernelClosure K q ≤ a.val.representation.ker :=
      Subgroup.topologicalClosure_minimal _ hker
        (FiniteRepresentation.isClosed_ker_of_isContinuous a.val a.property.1)
    exact fun w hw => (MonoidHom.mem_ker).mp (hcl' hw)
  · rw [VirtualRepresentation.Weil.realizeExact_generator]
    change ExactGrothendieckGroup.ofClass _
      (VirtualRepresentation.Weil.forgetIrreducibleClass _ b.2.val) = _
    rw [← ha]
    rfl

/-- Transport and Brauer induction: for a topological isomorphism
`T : W_K ≅ W_F`, the exact class of every unitary virtual class of `W_K`
supported on classes factoring through `q ∘ proj` is the restriction along `T`
of an element of the integral span of the inductions of characters above
`T(N_q)`, where `N_q = factoringKernelClosure K q`. -/
theorem realizeExact_includeUnitary_mem_map_span
    (F : PadicField.{uF} p) (T : localWeilGroup K ≃ₜ* localWeilGroup F)
    (x : LocalWeil.UnitaryLattice.{uK, max uF uV} K)
    (hx : x ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, max uF uV, uQ} K q) :
    LocalWeil.realizeExact K (LocalWeil.includeUnitary K x) ∈
      (Submodule.span ℤ (inducedCharacterClassesAbove.{uF, uV} F
        ((factoringKernelClosure K q).comap
          (T.symm : localWeilGroup F →* localWeilGroup K)))).map
        (ExactGrothendieckGroup.continuousRestrict (T : localWeilGroup K →ₜ* localWeilGroup F)) := by
  set N := (factoringKernelClosure K q).comap (T.symm : localWeilGroup F →* localWeilGroup K)
  have hNo : IsOpen (N : Set (localWeilGroup F)) :=
    (factoringKernelClosure_isOpen K q).preimage T.symm.continuous
  have : N.Normal := Subgroup.normal_comap _
  set V := (Submodule.span ℤ (inducedCharacterClassesAbove.{uF, uV} F N)).map
    (ExactGrothendieckGroup.continuousRestrict (T : localWeilGroup K →ₜ* localWeilGroup F))
  let Λ := (LocalWeil.realizeExact.{uK, max uF uV} K).comp (LocalWeil.includeUnitary K)
  -- Each generator lies in `V`.
  have key : ∀ b : LocalWeil.UnitaryBasis.{uK, max uF uV} K,
      VirtualRepresentation.Weil.FactorsThrough (localWeilGroup K)
        (q.comp (localProjection K).toMonoidHom) b.val →
      Λ (Finsupp.single b 1) ∈ V := by
    intro b hb
    obtain ⟨B, hc, hBN, hBeq⟩ := exists_realizeExact_generator_eq K q b.val hb
    have hΛ : Λ (Finsupp.single b 1) =
        VirtualRepresentation.Weil.realizeExact (localWeilGroup K) (generator b.val) := by
      change LocalWeil.realizeExact K (Finsupp.mapDomain Subtype.val (Finsupp.single b 1)) = _
      rw [Finsupp.mapDomain_single]
      rfl
    rw [hΛ, hBeq]
    let B' := FiniteRepresentation.restrict
      (T.symm : localWeilGroup F →ₜ* localWeilGroup K).toMonoidHom B
    have hc' : B'.IsContinuous :=
      FiniteRepresentation.isContinuous_restrict _ T.symm.continuous hc
    have hB'N : ∀ w ∈ N, B'.representation w = 1 := fun w hw => hBN _ hw
    refine ⟨ExactGrothendieckGroup.ofRepresentation _ ⟨B', hc'⟩,
      ofRepresentation_mem_span_inducedCharacterClassesAbove.{uF, uV} F N hNo B' hc' hB'N, ?_⟩
    have h1 : ExactGrothendieckGroup.continuousRestrict
        (T.symm : localWeilGroup F →ₜ* localWeilGroup K)
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hc⟩) =
        ExactGrothendieckGroup.ofRepresentation _ ⟨B', hc'⟩ :=
      ExactGrothendieckGroup.restrict_ofRepresentation _ _ _ _ _
    rw [← h1]
    exact (ExactGrothendieckGroup.continuousRestrictEquivalence T).apply_symm_apply _
  have hle : LocalWeil.unitaryFiniteFactoringSupported.{uK, max uF uV, uQ} K q ≤ V.comap Λ := by
    change Finsupp.supported ℤ ℤ _ ≤ _
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact key b hb
  exact hle hx

end Langlands.LocalFactor.CommonClosure
