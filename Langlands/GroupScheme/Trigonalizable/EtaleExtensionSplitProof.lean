import Langlands.GroupScheme.Trigonalizable.EtaleExtensionDevissage
import Langlands.GroupScheme.Trigonalizable.EtaleVectorExtension
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitPerfectSmooth
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof

/-! # Splitting over a finite étale diagonalizable quotient (SGA 3 XVII 5.2.3 i) c)) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
private theorem etale_diagonalizable {k : Type u} [Field k] [PerfectField k]
    (p : ℕ) [ExpChar k p] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] [Finite Λ]
    (hcop : (Nat.card Λ).Coprime p) :
    Etale (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom := by
  let : Smooth (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom :=
    (Diagonalizable.diagonalizableSmoothConnectedCriteria k p Λ).2.1.mpr (by
      intro x hx
      have hd := Nat.dvd_gcd (addOrderOf_dvd_natCard x)
        (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hx)
      rw [show Nat.gcd (Nat.card Λ) p = 1 from hcop] at hd
      exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
  let A := AddMonoidAlgebra k Λ
  let : IsReduced A := Diagonalizable.SmoothConnectedCriteria.isReduced_of_smooth k Λ
  let : Module.Finite k A := (AddMonoidAlgebra.basis Λ k).finiteDimensional_of_finite
  let : IsArtinianRing A := isArtinian_of_tower k inferInstance
  have hfe : Algebra.FormallyEtale k A := by
    rw [Algebra.FormallyEtale.iff_of_equiv ((IsArtinianRing.equivPi A).restrictScalars k),
      Algebra.FormallyEtale.pi_iff]
    intro I
    exact Algebra.FormallyEtale.of_isSeparable k (A ⧸ I.asIdeal)
  let : Algebra.Etale k A := ⟨hfe, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- **SGA 3 XVII, Lemme 5.2.3 i) c)** for a finite étale diagonalizable quotient
and a smooth connected unipotent kernel. -/
theorem etaleDiagonalizableExtensionSplit : EtaleDiagonalizableExtensionSplitStatement.{u} := by
  intro k _ p _ G _ _ U i Λ _ _ q hperf hfin hcop hi hsm hconn hU hn hq
  let : PerfectField k := hperf
  let : Finite Λ := hfin
  rcases expChar_is_prime_or_one k p with hprime | rfl
  · let : CharP k p := (expChar_prime_iff (R := k) hprime).mp inferInstance
    let L := SeparableClosure k
    let : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
    let D := (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
    let : IsAffineHom D.X.hom := Diagonalizable.isAffineHom _ _
    let : Etale D.X.hom := etale_diagonalizable p Λ hcop
    have hD : IsMultiplicativeType D :=
      ⟨k, inferInstance, inferInstance, Λ, inferInstance, inferInstance,
        ⟨Diagonalizable.baseChangeIso _ Λ⟩⟩
    have hcard : (Nat.card (EtaleExtensionSplit.geometricTest k L ⟶ D.X)).Coprime p :=
      (EtaleMultiplicativeTypeOrder.forward k p L D hD).2
    let : IsClosedImmersion i.hom.hom.left := hi
    let : Mono i.hom.hom := Over.mono_of_mono_left _
    have hi' : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    let : QuasiCompact q.hom.hom.left := by
      have hc : QuasiCompact (q.hom.hom.left ≫ D.X.hom) := by
        rw [Over.w q.hom.hom]
        infer_instance
      let : QuasiCompact (q.hom.hom.left ≫ D.X.hom) := hc
      exact QuasiCompact.of_comp _ D.X.hom
    let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hi' hsm
    let : Surjective q.hom.hom.left := hq.2.1
    let : Smooth G.X.hom := by
      rw [← Over.w q.hom.hom]
      infer_instance
    let e := hq.kernelIso hi'
    let : ConnectedSpace (kernel q).X.left :=
      (Scheme.homeoOfIso (((Grp.forget _) ⋙ Over.forget _).mapIso e)).connectedSpace_iff.mp hconn
    exact EtaleExtensionSplit.exists_section_of_vector_splitting D
      (fun E _ f _ _ _ hv => EtaleExtensionSplit.exists_section_of_vector_kernel
        p hprime.one_lt hcard f hv) G q (IsUnipotent.of_iso e.symm hU)
  · let : CharZero k := charZero_of_expChar_one' k
    exact TrigonalizableExtensionSplit.exists_section_of_admitsTower'
      (TrigonalizableExtensionSplit.oneStepSplitting_of_charZero Λ)
      (TrigonalizableExtensionSplit.admitsTower i q hi hU hn hq)

end Langlands.GroupScheme
