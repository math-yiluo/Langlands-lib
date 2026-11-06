import Langlands.CommutativeAlgebra.DiagonalGroupLikeCoefficients
import Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Principal isomorphism certificates for diagonal bialgebra morphisms -/

noncomputable section

universe u v w x y

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalIsomorphismLocus

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}

section Monoids

variable [AddCommMonoid M] [AddCommMonoid N]

/-- Ring scalar extension preserves group-like elements of a diagonal algebra. -/
theorem isGroupLike_map {z : AddMonoidAlgebra R M} (hz : IsGroupLikeElem R z)
    (A : Type x) [CommRing A] [Algebra R A] :
    IsGroupLikeElem A (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A) z) where
  counit_eq_one := by
    have h := RingHom.congr_fun
      (AddMonoidAlgebra.counitAlgHom_comp_mapRingHom (M := M) (algebraMap R A)) z
    simpa [AddMonoidAlgebra.mapAlgHom, hz.counit_eq_one] using h
  comul_eq_tmul_self := by
    have h := RingHom.congr_fun
      (AddMonoidAlgebra.comulAlgHom_comp_mapRingHom (M := M) (algebraMap R A)) z
    simpa [AddMonoidAlgebra.mapAlgHom, hz.comul_eq_tmul_self] using h

/-- Scalar extension with both monoid algebras in their canonical coordinates. -/
def scalarExtensionAlgHom (f : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    AddMonoidAlgebra A N →ₐ[A] AddMonoidAlgebra A M :=
  (DiagonalCoalgebraLocus.scalarExtension f A).comp
    (AddMonoidAlgebra.scalarTensorEquiv R A (M := N)).symm.toAlgHom

@[simp] theorem scalarExtensionAlgHom_single
    (f : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (n : N) (a : A) :
    scalarExtensionAlgHom f A (AddMonoidAlgebra.single n a) =
      a • AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)
        (f (AddMonoidAlgebra.single n 1)) := by
  simp [scalarExtensionAlgHom]

/-- The canonical coordinate scalar extension is a bialgebra morphism. -/
def scalarExtension (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    AddMonoidAlgebra A N →ₐc[A] AddMonoidAlgebra A M :=
  .ofAlgHom (scalarExtensionAlgHom f.toAlgHom A)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro n
        have h := isGroupLike_map ((AddMonoidAlgebra.isGroupLikeElem_single_one n).map f) A
        simpa using h.counit_eq_one
      · ext)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro n
        have h := isGroupLike_map ((AddMonoidAlgebra.isGroupLikeElem_single_one n).map f) A
        simpa using h.comul_eq_tmul_self.symm
      · ext)

@[simp] theorem scalarExtension_single
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (n : N) (a : A) :
    scalarExtension f A (AddMonoidAlgebra.single n a) =
      a • AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)
        (f (AddMonoidAlgebra.single n 1)) :=
  scalarExtensionAlgHom_single f.toAlgHom A n a

/-- Agreement on monoid generators determines a monoid-algebra morphism. -/
theorem algHom_eq_mapDomain_of_generators
    {A : Type x} [CommRing A]
    (f : AddMonoidAlgebra A N →ₐ[A] AddMonoidAlgebra A M) (g : N →+ M)
    (s : Set N) (hs : AddSubmonoid.closure s = ⊤)
    (hf : ∀ n ∈ s, f (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single (g n) 1) :
    f = AddMonoidAlgebra.mapDomainAlgHom A A g := by
  let D : AddSubmonoid N :=
    { carrier := {n | f (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single (g n) 1}
      zero_mem' := by
        simp [← AddMonoidAlgebra.one_def]
      add_mem' := by
        intro n n' hn hn'
        change f (AddMonoidAlgebra.single (n + n') 1) = _
        rw [← one_mul (1 : A), ← AddMonoidAlgebra.single_mul_single, map_mul, hn, hn']
        simp }
  have hD : D = ⊤ := top_unique <| hs ▸ AddSubmonoid.closure_le.mpr hf
  apply AddMonoidAlgebra.algHom_ext
  · intro n
    have hn : n ∈ D := hD ▸ AddSubmonoid.mem_top n
    change f (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single (g n) 1 at hn
    simpa using hn
  · ext

/-- The finite product selecting a prescribed character map on generators. -/
def generatorCoefficientProduct
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (g : N →+ M) (s : Finset N) : R :=
  ∏ n ∈ s, (f (AddMonoidAlgebra.single n 1)).coeff (g n)

/-- Inverting the generator coefficient product makes the scalar extension
equal to the selected character-map morphism. -/
theorem scalarExtension_eq_mapDomain_of_isUnit
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (g : N →+ M) (s : Finset N) (hs : AddSubmonoid.closure (s : Set N) = ⊤)
    (A : Type x) [CommRing A] [Algebra R A]
    (hr : IsUnit (algebraMap R A (generatorCoefficientProduct f g s))) :
    (scalarExtension f A).toAlgHom = AddMonoidAlgebra.mapDomainAlgHom A A g := by
  classical
  have hr' : IsUnit (∏ n ∈ s,
      algebraMap R A ((f (AddMonoidAlgebra.single n 1)).coeff (g n))) := by
    simpa [generatorCoefficientProduct] using hr
  apply algHom_eq_mapDomain_of_generators _ g (s : Set N) hs
  intro n hn
  change scalarExtension f A (AddMonoidAlgebra.single n 1) = _
  rw [scalarExtension_single, one_smul]
  exact DiagonalGroupLikeCoefficients.map_eq_single_of_isUnit_coeff
    ((AddMonoidAlgebra.isGroupLikeElem_single_one n).map f) A (g n)
    (IsUnit.prod_iff.mp hr' n hn)

end Monoids

section Groups

variable [AddCommGroup M] [AddCommGroup N]

/-- A bialgebra equivalence over a field induces an actual character-group
equivalence. -/
def characterEquiv {K : Type x} [Field K]
    (e : AddMonoidAlgebra K N ≃ₐc[K] AddMonoidAlgebra K M) : N ≃+ M where
  toFun := AddMonoidAlgebra.mapDomainOfBialgHom e.toBialgHom
  invFun := AddMonoidAlgebra.mapDomainOfBialgHom e.symm.toBialgHom
  left_inv n := by
    apply AddMonoidAlgebra.single_left_injective (R := K) one_ne_zero
    change AddMonoidAlgebra.single
      (AddMonoidAlgebra.mapDomainOfBialgHom e.symm.toBialgHom
        (AddMonoidAlgebra.mapDomainOfBialgHom e.toBialgHom n)) (1 : K) =
      AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.single_mapDomainOfBialgHom,
      AddMonoidAlgebra.single_mapDomainOfBialgHom]
    exact e.symm_apply_apply _
  right_inv m := by
    apply AddMonoidAlgebra.single_left_injective (R := K) one_ne_zero
    change AddMonoidAlgebra.single
      (AddMonoidAlgebra.mapDomainOfBialgHom e.toBialgHom
        (AddMonoidAlgebra.mapDomainOfBialgHom e.symm.toBialgHom m)) (1 : K) =
      AddMonoidAlgebra.single m 1
    rw [AddMonoidAlgebra.single_mapDomainOfBialgHom,
      AddMonoidAlgebra.single_mapDomainOfBialgHom]
    exact e.apply_symm_apply _
  map_add' := map_add _

/-- The coefficient in the field-selected character degree specializes to one. -/
theorem field_character_coefficient
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (K : Type x) [Field K] [Algebra R K] (n : N) :
    algebraMap R K ((f (AddMonoidAlgebra.single n 1)).coeff
      (AddMonoidAlgebra.mapDomainOfBialgHom (scalarExtension f K) n)) = 1 := by
  have h := congrArg (fun z : AddMonoidAlgebra K M =>
    z.coeff (AddMonoidAlgebra.mapDomainOfBialgHom (scalarExtension f K) n))
    (AddMonoidAlgebra.single_mapDomainOfBialgHom (scalarExtension f K) n (1 : K))
  simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    scalarExtension_single, one_smul,
    AddMonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply] using h.symm

/-- A field isomorphism admits a finite coefficient certificate that forces
isomorphisms after every scalar extension in which the certificate is a unit. -/
theorem exists_principal_isomorphism_certificate [AddMonoid.FG N]
    (f : AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)
    (K : Type x) [Field K] [Algebra R K]
    (hf : Function.Bijective (scalarExtension f K)) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧
      ∀ (A : Type y) [CommRing A] [Algebra R A],
        IsUnit (algebraMap R A r) → Function.Bijective (scalarExtension f A) := by
  classical
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := N)
  let e := BialgEquiv.ofBijective (scalarExtension f K) hf
  let g : N ≃+ M := characterEquiv e
  have he : e.toBialgHom = scalarExtension f K := by
    ext z
    rfl
  have hg (n : N) : g n = AddMonoidAlgebra.mapDomainOfBialgHom (scalarExtension f K) n := by
    change AddMonoidAlgebra.mapDomainOfBialgHom e.toBialgHom n = _
    rw [he]
  refine ⟨generatorCoefficientProduct f g.toAddMonoidHom s, ?_, ?_⟩
  · have hr : algebraMap R K (generatorCoefficientProduct f g.toAddMonoidHom s) = 1 := by
      simp only [generatorCoefficientProduct, map_prod]
      apply Finset.prod_eq_one
      intro n _
      change algebraMap R K ((f (AddMonoidAlgebra.single n 1)).coeff (g n)) = 1
      rw [hg]
      exact field_character_coefficient f K n
    rw [hr]
    exact one_ne_zero
  · intro A _ _ hr
    have h := scalarExtension_eq_mapDomain_of_isUnit f g.toAddMonoidHom s hs A hr
    have h' : (scalarExtension f A : AddMonoidAlgebra A N → AddMonoidAlgebra A M) =
        AddMonoidAlgebra.domCongr A A g := by
      exact congrArg DFunLike.coe h
    rw [h']
    exact (AddMonoidAlgebra.domCongr A A g).bijective

end Groups

end Langlands.CommutativeAlgebra.DiagonalIsomorphismLocus
