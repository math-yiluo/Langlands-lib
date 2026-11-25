import Langlands.GroupScheme.Rational.TorusAnisotropicQuotient
import Langlands.GroupScheme.Rational.TorusAnisotropicPartLattice
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.CocharacterAnisotropy
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Rational.AnisotropicTorusCompactness
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints

/-! # The kernel of the split quotient determined by invariant characters -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusAnisotropicPart

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E]

omit [FiniteDimensional k E] [IsGalois k E] in
/-- Saturation of invariant characters makes the actual quotient kernel split
over the chosen splitting field. -/
theorem isSplitTorus_kernel_baseChange
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (q : T ⟶ Q)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hQ : IsSplitTorus Q.toGrp)
    (hr : (characterLattice.baseChangePullback k E q).range =
      (characterLattice.galoisRepresentation k E T).invariants) :
    IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj
        (CommGroupScheme.kernel q)).toGrp := by
  classical
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  let M := characterLattice (bc.obj T)
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT
  let := hJ
  let cT : M ≃+ (J → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso eT)).trans
      (splitTorus.characterLatticeEquiv E J)
  let : Module.Free ℤ M := Module.Free.of_equiv cT.symm.toIntLinearEquiv
  let : Module.Finite ℤ M := Module.Finite.equiv cT.symm.toIntLinearEquiv
  let N := (characterLattice.galoisRepresentation k E T).invariants
  let : Module.Free ℤ (M ⧸ N) :=
    free_quotient_invariants (characterLattice.galoisRepresentation k E T)
  let qE := bc.map q
  have hr' : (characterLattice.comapHom (CommGroupScheme.groupHom qE)).range =
      N.toAddSubgroup := by
    exact congrArg Submodule.toAddSubgroup hr
  let cΛ : Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE) ≃+ (M ⧸ N) :=
    QuotientAddGroup.quotientAddEquivOfEq hr'
  let : Module.Free ℤ (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE)) :=
    Module.Free.of_equiv cΛ.symm.toIntLinearEquiv
  let : AddGroup.FG (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE)) :=
    Diagonalizable.homKernelLattice_fg (CommGroupScheme.groupHom qE)
      ⟨J, hJ, ⟨eT⟩⟩
  let : Module.Finite ℤ (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE)) :=
    inferInstance
  let I := Module.Free.ChooseBasisIndex ℤ
    (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE))
  let b := Module.Free.chooseBasis ℤ
    (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom qE))
  let e1 := CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k E) q
  let i1 : (bc.obj (CommGroupScheme.kernel q)).toGrp ≅
      GroupScheme.kernel (CommGroupScheme.groupHom qE) :=
    ⟨CommGroupScheme.groupHom e1.hom, CommGroupScheme.groupHom e1.inv,
      congrArg CommGroupScheme.groupHom e1.hom_inv_id,
      congrArg CommGroupScheme.groupHom e1.inv_hom_id⟩
  let e : (bc.obj (CommGroupScheme.kernel q)).toGrp ≅
      splitTorus (Spec (CommRingCat.of E)) I :=
    i1 ≪≫ Diagonalizable.homKernelDiagonalizableIso
      (CommGroupScheme.groupHom qE) ⟨J, hJ, ⟨eT⟩⟩
      (hQ.baseChange (algebraBaseMap k E)) ≪≫
      Diagonalizable.splitIso (CommRingCat.of E) b.equivFun.toAddEquiv
  exact ⟨I, inferInstance, ⟨e⟩⟩

omit [IsGalois k E] in
/-- An invariant-character quotient kills no nonzero ground-field cocharacter. -/
theorem cocharacter_eq_zero_of_comp_eq_zero
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (q : T ⟶ Q)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hr : (characterLattice.baseChangePullback k E q).range =
      (characterLattice.galoisRepresentation k E T).invariants)
    (ν : cocharacterLattice T) (hν : ν ≫ q = 0) : ν = 0 := by
  classical
  let : Fintype (E ≃ₐ[k] E) := Fintype.ofFinite _
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  let νE := cocharacterLattice.baseChange (algebraBaseMap k E) T ν
  have hνE : νE ≫ bc.map q = 0 := by
    change (Gm.commBaseChangeIso (algebraBaseMap k E)).inv ≫
      bc.map ν ≫ bc.map q = 0
    rw [← Functor.map_comp, hν, Functor.map_zero, Limits.comp_zero]
  have htrace (χ : characterLattice (bc.obj T)) :
      latticePairing (bc.obj T) (CharacterAveraging.galoisOrbitSum k E T χ) νE = 0 := by
    have hmem : CharacterAveraging.galoisOrbitSum k E T χ ∈
        (characterLattice.baseChangePullback k E q).range := by
      rw [hr]
      exact CharacterAveraging.galoisOrbitSum_fixed k E T χ
    obtain ⟨ψ, hψ⟩ := hmem
    rw [← hψ]
    change gmEndEquiv E (νE ≫ bc.map q ≫ ψ) = 0
    rw [← Category.assoc, hνE, Limits.zero_comp, AddEquiv.map_zero]
  have horbit : CocharacterAveraging.galoisOrbitSum k E T νE =
      Fintype.card (E ≃ₐ[k] E) • νE := by
    simp only [CocharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum,
      νE, cocharacterLattice.galoisRepresentation_baseChange, Finset.sum_const,
      Finset.card_univ]
  have hνE0 : νE = 0 := by
    apply hT.cocharacter_eq_zero
    intro χ
    have h := htrace χ
    rw [CharacterAveraging.latticePairing_galoisOrbitSum, horbit, map_nsmul] at h
    have hn : (Fintype.card (E ≃ₐ[k] E) : ℤ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp (by simpa only [nsmul_eq_mul] using h)).resolve_left hn
  apply cocharacterLattice.algebraBaseChange_injective k E T
  simpa only [map_zero] using hνE0

omit [IsGalois k E] in
/-- The actual kernel has no nontrivial closed split subtorus. -/
theorem isAnisotropic_kernel
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (q : T ⟶ Q)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hr : (characterLattice.baseChangePullback k E q).range =
      (characterLattice.galoisRepresentation k E T).invariants) :
    IsAnisotropic (CommGroupScheme.kernel q).toGrp := by
  apply isAnisotropic_of_cocharacter_eq_zero
  intro ν
  have hz : ν ≫ CommGroupScheme.kernelι q = 0 := by
    apply cocharacter_eq_zero_of_comp_eq_zero k E q hT hr
    rw [Category.assoc, CommGroupScheme.kernelι_comp, Limits.comp_zero]
  apply CommGroupScheme.kernel_hom_ext q
  simpa only [Limits.zero_comp] using hz

omit [FiniteDimensional k E] [IsGalois k E] in
/-- A homomorphism from an anisotropic torus to a split torus is trivial. -/
theorem hom_eq_zero_of_isAnisotropic
    {C Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (hC : IsTorus C.toGrp) (hCa : IsAnisotropic C.toGrp)
    (hQ : IsSplitTorus Q.toGrp) (f : C ⟶ Q) : f = 0 := by
  have : IsAffine C.X.left := SplittingAssembly.isAffine_of_isTorus C.toGrp hC
  have : IsAffineHom C.toGrp.X.hom := inferInstance
  have : Smooth C.toGrp.X.hom := hC.smooth
  have : LocallyOfFiniteType C.toGrp.X.hom := inferInstance
  apply hQ.hom_ext_of_characters
  intro χ
  rw [Limits.zero_comp]
  exact hCa.rationalCharacter_eq_zero_of_isTorus hC (f ≫ χ)

omit [FiniteDimensional k E] [IsGalois k E] in
/-- Every anisotropic torus mapping to the source factors through this kernel. -/
theorem factors_kernel_of_isAnisotropic
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (q : T ⟶ Q)
    (hQ : IsSplitTorus Q.toGrp)
    (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ T.toGrp)
    (hC : IsTorus C.toGrp) (hCa : IsAnisotropic C.toGrp) :
    ∃ f : C.toGrp ⟶ (CommGroupScheme.kernel q).toGrp,
      f ≫ CommGroupScheme.groupHom (CommGroupScheme.kernelι q) = c := by
  let c' : C ⟶ T := Additive.ofMul c
  have hcq : c' ≫ q = 0 := hom_eq_zero_of_isAnisotropic k hC hCa hQ (c' ≫ q)
  exact ⟨CommGroupScheme.groupHom (CommGroupScheme.kernelLift q c' hcq),
    congrArg CommGroupScheme.groupHom (CommGroupScheme.kernelLift_ι q c' hcq)⟩

/-- The closed maximal anisotropic subtorus, with its actual universal property. -/
structure AnisotropicPartData
    (T : CommGroupScheme (Spec (CommRingCat.of k))) where
  part : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : part.toGrp ⟶ T.toGrp
  isClosed : IsClosedSubgroup inclusion
  isTorus : IsTorus part.toGrp
  isAnisotropic : IsAnisotropic part.toGrp
  factors : ∀ (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ T.toGrp),
    IsClosedSubgroup c → IsTorus C.toGrp → IsAnisotropic C.toGrp →
      ∃ f : C.toGrp ⟶ part.toGrp, f ≫ inclusion = c

/-- Construct the maximal anisotropic subtorus as the actual kernel of the
split quotient determined by all invariant geometric characters. -/
def anisotropicPart
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp) :
    AnisotropicPartData k T := by
  let D := splitQuotient k E T hT
  have : IsAffineHom D.quotient.toGrp.X.hom := D.isSplit.isAffineHom
  have : IsSeparated D.quotient.toGrp.X.hom := inferInstance
  refine
    { part := CommGroupScheme.kernel D.hom
      inclusion := CommGroupScheme.groupHom (CommGroupScheme.kernelι D.hom)
      isClosed := ?_
      isTorus := ?_
      isAnisotropic := isAnisotropic_kernel k E D.hom hT D.range_pullback
      factors := ?_ }
  · change IsClosedImmersion (GroupScheme.kernelι (CommGroupScheme.groupHom D.hom)).hom.hom.left
    infer_instance
  · exact ⟨E, inferInstance, inferInstance,
      isSplitTorus_kernel_baseChange k E D.hom hT D.isSplit D.range_pullback⟩
  · intro C c _ hC hCa
    exact factors_kernel_of_isAnisotropic k D.hom D.isSplit C c hC hCa

end Langlands.GroupScheme.TorusAnisotropicPart
