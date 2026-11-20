import Langlands.CommutativeAlgebra.DiagonalCoalgebraCoefficientIdeal
import Langlands.GroupScheme.AffineHomImageHopfAdapter
import Langlands.GroupScheme.Torus.GroupLikeHopfBaseChange
import Mathlib.RingTheory.Flat.Basic

/-! # Local group-algebra images of Hopf maps -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalGroupAlgebraImage

open AddMonoidAlgebra DiagonalCoalgebraLocus
open Langlands.Algebra.HopfPointIntegralClosure

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]
  {B : Type u} [CommRing B] [HopfAlgebra R B]

/-- The standard coefficient scalar-extension isomorphism respects the bialgebra structures. -/
def scalarTensorBialgEquiv (A : Type v) [CommRing A] [Algebra R A] :
    A ⊗[R] AddMonoidAlgebra R M ≃ₐc[A] AddMonoidAlgebra A M := by
  let e := (AddMonoidAlgebra.scalarTensorEquiv R A (M := M)).symm
  have hsingle (m : M) : IsGroupLikeElem A (e (single m 1)) := by
    change IsGroupLikeElem A ((AddMonoidAlgebra.scalarTensorEquiv R A).symm (single m 1))
    rw [AddMonoidAlgebra.scalarTensorEquiv_symm_single]
    exact Langlands.GroupScheme.HopfCoordinates.isGroupLikeElem_one_tmul
      (isGroupLikeElem_single_one m)
  refine (BialgEquiv.ofAlgEquiv e ?_ ?_).symm
  · apply AddMonoidAlgebra.algHom_ext
    · intro m
      simpa using (hsingle m).counit_eq_one
    · exact Subsingleton.elim _ _
  · apply AddMonoidAlgebra.algHom_ext
    · intro m
      simpa using (hsingle m).comul_eq_tmul_self.symm
    · exact Subsingleton.elim _ _

/-- Extension of scalars with the target in standard group-algebra coordinates. -/
def scalarExtensionBialgHom (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (A : Type v) [CommRing A] [Algebra R A] : A ⊗[R] B →ₐc[A] AddMonoidAlgebra A M :=
  (scalarTensorBialgEquiv (R := R) (M := M) A).toBialgHom.comp
    (Bialgebra.TensorProduct.map (BialgHom.id A A) φ)

@[simp] theorem scalarExtensionBialgHom_toAlgHom (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (A : Type v) [CommRing A] [Algebra R A] :
    (scalarExtensionBialgHom φ A).toAlgHom = scalarExtension φ.toAlgHom A := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change scalarTensorEquiv R A (a ⊗ₜ[R] φ b) = _
  rw [scalarTensorEquiv_tmul, scalarExtension_tmul]
  rfl

/-- The degrees for which the image contains the monomial with coefficient one. -/
def monomialSubgroup (φ : B →ₐc[R] AddMonoidAlgebra R M) : AddSubgroup M where
  carrier := {m | single m 1 ∈ φ.toAlgHom.range}
  zero_mem' := by
    change single 0 1 ∈ φ.toAlgHom.range
    rw [← AddMonoidAlgebra.one_def]
    exact φ.toAlgHom.range.one_mem
  add_mem' := by
    intro m n hm hn
    change single (m + n) 1 ∈ φ.toAlgHom.range
    simpa only [single_mul_single, mul_one] using φ.toAlgHom.range.mul_mem hm hn
  neg_mem' := by
    intro m hm
    let f : CommHopfAlgCat.of R B ⟶ CommHopfAlgCat.of R (AddMonoidAlgebra R M) :=
      CommHopfAlgCat.ofHom φ
    have h := Langlands.GroupScheme.AffineHomImageHopfAdapter.antipode_mem_range
      f (single m 1) hm
    change HopfAlgebra.antipode R (single m 1 : AddMonoidAlgebra R M) ∈
      φ.toAlgHom.range at h
    change single (-m) 1 ∈ φ.toAlgHom.range
    simpa only [antipode_single, HopfAlgebra.antipode_one] using h

private theorem range_inclusion_le (φ : B →ₐc[R] AddMonoidAlgebra R M) :
    (mapDomainBialgHom R (monomialSubgroup φ).subtype).toAlgHom.range ≤ φ.toAlgHom.range := by
  rintro _ ⟨z, rfl⟩
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add]; exact add_mem hz hw
  | single m r =>
    change mapDomainBialgHom R (monomialSubgroup φ).subtype (single m r) ∈ φ.toAlgHom.range
    rw [mapDomainBialgHom_single]
    change single (m : M) r ∈ φ.toAlgHom.range
    have hm : single (m : M) 1 ∈ φ.toAlgHom.range := m.property
    simpa only [smul_single', mul_one] using φ.toAlgHom.range.smul_mem hm r

private theorem factor_of_range_le (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (h : φ.toAlgHom.range ≤
      (mapDomainBialgHom R (monomialSubgroup φ).subtype).toAlgHom.range) :
    ∃ f : B →ₐc[R] AddMonoidAlgebra R (monomialSubgroup φ),
      Function.Surjective f ∧ (mapDomainBialgHom R (monomialSubgroup φ).subtype).comp f = φ := by
  let L := monomialSubgroup φ
  let i := mapDomainBialgHom R L.subtype
  have hi : Function.Injective i := AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
  let e := AlgEquiv.ofInjective i.toAlgHom hi
  let f := e.symm.toAlgHom.comp (φ.toAlgHom.codRestrict _ fun b => h ⟨b, rfl⟩)
  have hcomp : i.toAlgHom.comp f = φ.toAlgHom := by
    apply AlgHom.ext
    intro b
    exact congrArg Subtype.val (e.apply_symm_apply (⟨φ b, h ⟨b, rfl⟩⟩ : i.toAlgHom.range))
  have hf : ∀ b, i (f b) = φ b := AlgHom.congr_fun hcomp
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨b, hb⟩ := range_inclusion_le φ (i.toAlgHom.mem_range_self a)
    exact ⟨b, hi ((hf b).trans hb)⟩
  have hcounit : (Bialgebra.counitAlgHom R (AddMonoidAlgebra R L)).comp f =
      Bialgebra.counitAlgHom R B := by
    rw [← i.counitAlgHom_comp, AlgHom.comp_assoc, hcomp, φ.counitAlgHom_comp]
  have hcomul : (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R B) =
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R L)).comp f := by
    let j := Algebra.TensorProduct.map i.toAlgHom i.toAlgHom
    have hj : Function.Injective j := by
      have : Module.Free R (AddMonoidAlgebra R L) :=
        Module.Free.of_equiv (coeffLinearEquiv (R := R) (M := L)).symm
      have : Module.Free R (AddMonoidAlgebra R M) :=
        Module.Free.of_equiv (coeffLinearEquiv (R := R) (M := M)).symm
      exact TensorProduct.map_injective_of_flat_flat i.toLinearMap i.toLinearMap hi hi
    apply AlgHom.ext
    intro b
    apply hj
    change (j.comp ((Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R B))) b =
      (j.comp ((Bialgebra.comulAlgHom R (AddMonoidAlgebra R L)).comp f)) b
    rw [← AlgHom.comp_assoc j, ← AlgHom.comp_assoc j, show j = _ from rfl,
      ← Algebra.TensorProduct.map_comp, hcomp, i.map_comp_comulAlgHom,
      AlgHom.comp_assoc, hcomp, φ.map_comp_comulAlgHom]
  refine ⟨BialgHom.ofAlgHom f hcounit hcomul, hsurj, ?_⟩
  exact BialgHom.coe_toAlgHom_injective hcomp

private theorem mem_range_inclusion_of_support_subset {L : AddSubgroup M}
    {z : AddMonoidAlgebra R M} (hz : ∀ m ∈ z.coeff.support, m ∈ L) :
    z ∈ (mapDomainBialgHom R L.subtype).toAlgHom.range := by
  rw [← sum_coeff_single z]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  exact ⟨single ⟨m, hz m hm⟩ (z.coeff m), mapDomainBialgHom_single _ _ _⟩

/-- Near each prime, the scalar extension of a finite-type Hopf map to a group
algebra factors as a surjection onto a subgroup algebra followed by its inclusion.
The basic open can be chosen to be defined by an idempotent. -/
theorem exists_away_factor [Algebra.FiniteType R B]
    (φ : B →ₐc[R] AddMonoidAlgebra R M) (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ IsIdempotentElem r ∧
      ∃ (L : AddSubgroup M) (f : Localization.Away r ⊗[R] B →ₐc[Localization.Away r]
        AddMonoidAlgebra (Localization.Away r) L),
        Function.Surjective f ∧
          (mapDomainBialgHom (Localization.Away r) L.subtype).comp f =
            scalarExtensionBialgHom φ (Localization.Away r) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B).out
  let W := s.biUnion fun b => (φ b).coeff.support
  choose e he using exists_idempotent_generator_coeffIdeal φ
  let d (m : M) := if e m ∈ p then 1 - e m else e m
  let r := ∏ m ∈ W, d m
  have hd (m : M) : d m ∉ p := by
    by_cases hm : e m ∈ p
    · simpa only [d, ite_eq_left hm] using fun h =>
        (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_iff_one _ |>.mpr
          (show (1 : R) ∈ p by simpa using p.add_mem h hm))
    · simpa only [d, ite_eq_right hm] using hm
  have hr : r ∉ p := by
    intro h
    obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hd m hm
  have hdidem (m : M) : IsIdempotentElem (d m) := by
    by_cases hm : e m ∈ p
    · simpa only [d, ite_eq_left hm] using (he m).1.one_sub
    · simpa only [d, ite_eq_right hm] using (he m).1
  have hri : IsIdempotentElem r := by
    change (∏ m ∈ W, d m) * (∏ m ∈ W, d m) = ∏ m ∈ W, d m
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun m _ => (hdidem m).eq
  let A := Localization.Away r
  let ψ := scalarExtensionBialgHom φ A
  let L := monomialSubgroup ψ
  let i := mapDomainBialgHom A L.subtype
  have hunit (m : M) (hm : m ∈ W) : IsUnit (algebraMap R A (d m)) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := A) r
    change IsUnit (algebraMap R A (∏ m ∈ W, d m)) at h
    rw [map_prod] at h
    exact IsUnit.prod_iff.mp h m hm
  have hideal (m : M) : algebraCoefficientIdeal ψ.toAlgHom m =
      Ideal.span {algebraMap R A (e m)} := by
    rw [scalarExtensionBialgHom_toAlgHom, algebraCoefficientIdeal_scalarExtension,
      show algebraCoefficientIdeal φ.toAlgHom m = coeffIdeal φ m from rfl,
      (he m).2, Ideal.map_span, Set.image_singleton]
  have htop (m : M) (hm : m ∈ W) (hmp : e m ∉ p) : m ∈ L := by
    have hi : algebraCoefficientIdeal ψ.toAlgHom m = ⊤ := by
      rw [hideal, Ideal.span_singleton_eq_top]
      simpa only [d, ite_eq_right hmp] using hunit m hm
    have hone : (1 : A) ∈ algebraCoefficientIdeal ψ.toAlgHom m := by simp [hi]
    obtain ⟨b, hb⟩ := (mem_algebraCoefficientIdeal ψ.toAlgHom m 1).mp hone
    change (ψ b).coeff m = 1 at hb
    change single m 1 ∈ ψ.toAlgHom.range
    simpa only [hb] using DiagonalCoalgebraImage.single_coefficient_mem_range ψ b m
  have hbot (m : M) (hm : m ∈ W) (hmp : e m ∈ p) :
      algebraMap R A (e m) = 0 := by
    have hu : IsUnit (algebraMap R A (1 - e m)) := by
      simpa only [d, ite_eq_left hmp] using hunit m hm
    apply hu.mul_right_injective
    change algebraMap R A (1 - e m) * algebraMap R A (e m) = algebraMap R A (1 - e m) * 0
    rw [← map_mul, (he m).1.one_sub_mul_self, map_zero, mul_zero]
  let α := AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)
  have hgenerators : φ.toAlgHom.range ≤ (i.toAlgHom.range.restrictScalars R).comap α := by
    rw [← Algebra.map_top φ.toAlgHom, ← hs, ← Algebra.adjoin_image]
    apply Algebra.adjoin_le
    rintro _ ⟨b, hb, rfl⟩
    apply mem_range_inclusion_of_support_subset
    intro m hm
    have hval : algebraMap R A ((φ b).coeff m) ≠ 0 := by
      have hc : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)
          (φ.toAlgHom b)).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
      rw [AddMonoidAlgebra.coeff_mapAlgHom] at hc
      exact hc
    have hmW : m ∈ W := Finset.mem_biUnion.mpr ⟨b, hb, Finsupp.mem_support_iff.mpr
      (fun h => hval (by rw [h, map_zero]))⟩
    apply htop m hmW
    intro hmp
    apply hval
    have hmem : (ψ (1 ⊗ₜ[R] b)).coeff m ∈ algebraCoefficientIdeal ψ.toAlgHom m :=
      ⟨1 ⊗ₜ[R] b, rfl⟩
    rw [hideal, hbot m hmW hmp, Ideal.span_singleton_zero, Ideal.mem_bot] at hmem
    change (ψ.toAlgHom (1 ⊗ₜ[R] b)).coeff m = 0 at hmem
    rw [show ψ.toAlgHom = scalarExtension φ.toAlgHom A from
      scalarExtensionBialgHom_toAlgHom φ A, coeff_scalarExtension_tmul, one_mul] at hmem
    exact hmem
  have hψ : ψ.toAlgHom.range ≤ i.toAlgHom.range := by
    rintro _ ⟨a, rfl⟩
    rw [scalarExtensionBialgHom_toAlgHom]
    induction a with
    | tmul c b =>
      change scalarExtension φ.toAlgHom A (c ⊗ₜ[R] b) ∈ i.toAlgHom.range
      rw [scalarExtension_tmul]
      exact i.toAlgHom.range.smul_mem (hgenerators (φ.toAlgHom.mem_range_self b)) c
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  obtain ⟨f, hf, hfac⟩ := factor_of_range_le ψ hψ
  exact ⟨r, hr, hri, L, f, hf, hfac⟩

end Langlands.CommutativeAlgebra.DiagonalGroupAlgebraImage
