import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Parabolic.NaturalInductionDualityStatement
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.CuspidalSupport.BlockPermutation

/-!
# Reversal of irreducible normalized products through contragredients

Assuming the Gelfand–Kazhdan realization of smooth contragredients and natural
normalized induction duality, an irreducible normalized product of irreducible
admissible blocks is isomorphic to the normalized product of the same blocks in
reverse order, provided that reversed product is irreducible as well. The
isomorphism is the composite of inverse-transpose transport, block
contragredients, the canonical tensor-dual map, induction duality and the
contragredient of the reversed product; Schur's lemma makes it bijective.
-/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- An irreducible representation over a field has a nontrivial carrier. -/
theorem nontrivial_of_isIrreducible {G : Type*} {k : Type*} {V : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    (h : Representation.IsIrreducible ρ) : Nontrivial V := by
  have : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  exact IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule

/-- The Gelfand–Kazhdan realization, transported to any topology on the field
equal to the canonical norm topology, in every positive rank and packaged as an
equivalence from the inverse-transpose pullback to the smooth contragredient. -/
theorem gelfandKazhdan_of_topologicalData
    (hGK : GelfandKazhdanContragredientStatement.{uF, uV}) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (N : ℕ), 0 < N → ∀ [IsTopologicalGroup (GeneralLinear N F.Carrier)]
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear N F.Carrier) V),
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      Nonempty (Representation.Equiv
        (ρ.comp (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
        (smoothContragredient ρ)) := by
  rw [T.topology_eq_canonicalNormTopology]
  intro N hN _ V _ _ ρ hadm hirr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨E, hE⟩ := hGK p inferInstance F m V ρ hadm hirr
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun v => hE g v⟩

variable (T : F.TopologicalData)

/-- Reversal of an irreducible normalized product of irreducible admissible
blocks, conditional on Gelfand–Kazhdan in the block and product carrier
universes, natural standard induction duality, and irreducibility of the
reversed product. -/
theorem normalizedProductInduced_reverse_equiv
    (hGK : GelfandKazhdanContragredientStatement.{uF, uV})
    (hGK' : GelfandKazhdanContragredientStatement.{uF, max uF uV})
    (hD : StandardNaturalInductionDualityClause.{uF, uV})
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    {V : Fin B.length → Type uV} [hadd : ∀ i, AddCommGroup (V i)] [hmod : ∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hadm : letI := T.topology
      ∀ i, IsAdmissible (π i))
    (hirr : ∀ i, Representation.IsIrreducible (π i))
    (hP : Representation.IsIrreducible (T.normalizedProductInduced B π))
    (hP' : letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
      letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
      Representation.IsIrreducible
        (T.normalizedProductInduced B.reverse (V := fun i => V i.rev) (fun i => π i.rev))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
    Nonempty (Representation.Equiv (T.normalizedProductInduced B π)
      (T.normalizedProductInduced B.reverse (V := fun i => V i.rev) (fun i => π i.rev))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
  have hTG : ∀ m : ℕ, IsTopologicalGroup (GeneralLinear m F.Carrier) :=
    fun m => T.generalLinearTopologicalGroup m
  have hGKT := gelfandKazhdan_of_topologicalData hGK T
  have hGKT' := gelfandKazhdan_of_topologicalData hGK' T
  -- Inverse-transpose transport reverses the product.
  obtain ⟨A⟩ := normalizedProductInverseTranspose T n hn B V π (fun i => (hadm i).1)
  -- Block contragredients.
  have hblock : ∀ i : Fin B.length, Nonempty (Representation.Equiv
      ((π i).comp (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)
      (smoothContragredient (π i))) := by
    intro i
    let := T.generalLinearTopologicalGroup (B.size i)
    exact hGKT _ (B.positive i) (π i) (hadm i) (hirr i)
  let e : ∀ i : Fin B.length, Representation.Equiv
      ((π i).comp (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)
      (smoothContragredient (π i)) := fun i => (hblock i).some
  let C := T.normalizedProductInducedEquiv B.reverse (V := fun i => V i.rev)
    (W := fun i => SmoothDual (π i.rev)) (fun i => e i.rev)
  -- The canonical tensor-dual map, induced.
  let πr : ∀ i : Fin B.reverse.length,
      Representation ℂ (GeneralLinear (B.reverse.size i) F.Carrier) (V i.rev) :=
    fun i => π i.rev
  have : ∀ i : Fin B.reverse.length,
      IsTopologicalGroup (GeneralLinear (B.reverse.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup _
  let IM := T.normalizedParabolicInducedMap B.reverse (FiniteTensor.smoothDualTensorIntertwiner πr)
  have hIM : Function.Injective IM :=
    T.normalizedParabolicInducedMap_injective B.reverse _
      (FiniteTensor.smoothDualTensorInjectivity (Fin B.reverse.length)
        (fun i => GeneralLinear (B.reverse.size i) F.Carrier) (fun i => V i.rev) πr)
  -- Natural induction duality for the reversed block tensor.
  obtain ⟨Dfam, -⟩ := hD p F T n B.reverse
  have hσadm : IsAdmissible (B.reverse.blockTensor πr) :=
    FiniteTensor.isAdmissible_external πr (fun i => hadm i.rev)
  let D := Dfam (Rep.of (B.reverse.blockTensor πr)) hσadm
  -- The contragredient of the reversed product.
  have hP'adm : IsAdmissible (T.normalizedProductInduced B.reverse πr) :=
    normalizedInductionAdmissibility F T B.reverse _ (B.reverse.blockTensor πr) hσadm
  obtain ⟨E'⟩ := hGKT' n hn (T.normalizedProductInduced B.reverse πr) hP'adm hP'
  -- The composite intertwines the inverse-transpose pullbacks.
  let Ψ := E'.symm.toIntertwiningMap.comp (D.symm.toIntertwiningMap.comp
    (IM.comp (C.toIntertwiningMap.comp A.toIntertwiningMap)))
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    apply A.toLinearEquiv.injective
    apply C.toLinearEquiv.injective
    apply hIM
    apply D.symm.toLinearEquiv.injective
    exact E'.symm.toLinearEquiv.injective hxy
  let Φ := LinearMap.intertwiningMap_of_isIntertwiningMap (T.normalizedProductInduced B π)
    (T.normalizedProductInduced B.reverse πr) Ψ.toLinearMap (fun g v => by
      have h := LinearMap.congr_fun (Ψ.isIntertwining' (GeneralLinear.inverseTranspose n F.Carrier g)) v
      change Ψ ((T.normalizedProductInduced B π) (GeneralLinear.inverseTranspose n F.Carrier
          (GeneralLinear.inverseTranspose n F.Carrier g)) v) =
        (T.normalizedProductInduced B.reverse πr) (GeneralLinear.inverseTranspose n F.Carrier
          (GeneralLinear.inverseTranspose n F.Carrier g)) (Ψ v) at h
      rwa [GeneralLinear.inverseTranspose_involutive] at h)
  have hΦ : Function.Injective Φ := hΨ
  have : Nontrivial (Induction.SmoothFunctions (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor π).comp (B.leviProjection F.Carrier)))) :=
    nontrivial_of_isIrreducible hP
  have hΦ0 : Φ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : Induction.SmoothFunctions (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor π).comp (B.leviProjection F.Carrier))))
    apply hx
    apply hΦ
    rw [map_zero]
    exact congrArg (fun f : Representation.IntertwiningMap _ _ => f x) h0
  have : Representation.IsIrreducible (T.normalizedProductInduced B.reverse πr) := hP'
  have hsurj := (Representation.IsIrreducible.surjective_or_eq_zero Φ).resolve_right hΦ0
  exact ⟨Φ.ofBijective ⟨hΦ, hsurj⟩⟩

/-- The reversal, with the reversed order written as the permutation of the
blocks by `Fin.revPerm`. -/
theorem normalizedProductInduced_revPerm_equiv
    (hGK : GelfandKazhdanContragredientStatement.{uF, uV})
    (hGK' : GelfandKazhdanContragredientStatement.{uF, max uF uV})
    (hD : StandardNaturalInductionDualityClause.{uF, uV})
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    {V : Fin B.length → Type uV} [hadd : ∀ i, AddCommGroup (V i)] [hmod : ∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hadm : letI := T.topology
      ∀ i, IsAdmissible (π i))
    (hirr : ∀ i, Representation.IsIrreducible (π i))
    (hP : Representation.IsIrreducible (T.normalizedProductInduced B π))
    (hP' : letI : ∀ i : Fin (B.permute Fin.revPerm).length, AddCommGroup (V (Fin.revPerm i)) :=
        fun i => hadd (Fin.revPerm i)
      letI : ∀ i : Fin (B.permute Fin.revPerm).length, Module ℂ (V (Fin.revPerm i)) :=
        fun i => hmod (Fin.revPerm i)
      Representation.IsIrreducible
        (T.normalizedProductInduced (B.permute Fin.revPerm) (V := fun i => V (Fin.revPerm i))
          (fun i => π (Fin.revPerm i)))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI : ∀ i : Fin (B.permute Fin.revPerm).length, AddCommGroup (V (Fin.revPerm i)) :=
      fun i => hadd (Fin.revPerm i)
    letI : ∀ i : Fin (B.permute Fin.revPerm).length, Module ℂ (V (Fin.revPerm i)) :=
      fun i => hmod (Fin.revPerm i)
    Nonempty (Representation.Equiv (T.normalizedProductInduced B π)
      (T.normalizedProductInduced (B.permute Fin.revPerm) (V := fun i => V (Fin.revPerm i))
        (fun i => π (Fin.revPerm i)))) :=
  normalizedProductInduced_reverse_equiv T hGK hGK' hD hn B π hadm hirr hP hP'

end Langlands.Parabolic
