import Langlands.AlgebraicGeometry.ReducedPrincipalDivisorConnectedness
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Connectedness of the generic fibre with reduced special fibre -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- The actual coefficient algebra on global sections of a scheme over an affine base. -/
@[instance_reducible]
def globalSectionAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop).hom.toAlgebra

/-- On an affine source the section algebra recovers the original morphism. -/
theorem globalSectionAlgebra_specMap {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of R)) :
    letI := globalSectionAlgebra p
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = X.isoSpec.inv ≫ p := by
  let := globalSectionAlgebra p
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) = _
  apply (cancel_mono (Spec (CommRingCat.of R)).toSpecΓ).mp
  rw [Spec.map_comp, Category.assoc, SpecMap_ΓSpecIso_inv_toSpecΓ, Category.comp_id,
    Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
    Scheme.isoSpec_inv_toSpecΓ, Category.id_comp]

/-- Flatness gives flatness of the actual global section algebra on an affine source. -/
theorem flat_globalSectionAlgebra {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] :
    letI := globalSectionAlgebra p
    Module.Flat R Γ(X, ⊤) := by
  let := globalSectionAlgebra p
  apply RingHom.flat_algebraMap_iff.mp
  apply Flat.SpecMap_iff.mp
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))))
  rw [globalSectionAlgebra_specMap p]
  infer_instance

/-- An open subscheme has a reduced base change whenever the original base change is reduced. -/
theorem isReduced_pullback_comp_of_isOpenImmersion
    {U X S T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (p : X ⟶ S) (b : T ⟶ S) [AlgebraicGeometry.IsReduced (pullback p b)] :
    AlgebraicGeometry.IsReduced (pullback (j ≫ p) b) := by
  let m := pullback.map (j ≫ p) b p b j (𝟙 T) (𝟙 S) (by simp) (by simp)
  have hm : IsOpenImmersion m :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (by infer_instance)
      (by infer_instance) rfl (by simp)
  exact isReduced_of_isOpenImmersion m

/-- Reducedness also restricts along an open immersion on the base-change leg. -/
theorem isReduced_pullback_comp_right_of_isOpenImmersion
    {X S T U : Scheme.{u}} (p : X ⟶ S) (b : T ⟶ S)
    (j : U ⟶ T) [IsOpenImmersion j]
    [AlgebraicGeometry.IsReduced (pullback p b)] :
    AlgebraicGeometry.IsReduced (pullback p (j ≫ b)) := by
  let m := pullback.map p (j ≫ b) p b (𝟙 X) j (𝟙 S) (by simp) (by simp)
  have hm : IsOpenImmersion m :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (by infer_instance)
      (by infer_instance) rfl (by simp)
  exact isReduced_of_isOpenImmersion m

/-- At a maximal ideal the actual residue fibre and the quotient base change have
the same reducedness, in the direction needed below. -/
theorem isReduced_pullback_quotient_of_reduced_fiber
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) [I.IsMaximal]
    [hred : AlgebraicGeometry.IsReduced
      (p.fiber (⟨I, inferInstance⟩ : PrimeSpectrum R))] :
    AlgebraicGeometry.IsReduced
      (pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let x : PrimeSpectrum R := ⟨I, inferInstance⟩
  let : AlgebraicGeometry.IsReduced
      (pullback p ((Spec (CommRingCat.of R)).fromSpecResidueField x)) := hred
  let e : CommRingCat.of (R ⧸ I) ≅ CommRingCat.of I.ResidueField :=
    (RingEquiv.ofBijective (algebraMap (R ⧸ I) I.ResidueField)
      I.bijective_algebraMap_quotient_residueField).toCommRingCatIso
  let j : Spec (CommRingCat.of (R ⧸ I)) ⟶
      Spec ((Spec (CommRingCat.of R)).residueField x) :=
    Spec.map e.inv ≫ Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) x).hom
  have : IsIso j := by dsimp only [j]; infer_instance
  have hcomp : j ≫ (Spec (CommRingCat.of R)).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    calc
      _ = Spec.map e.inv ≫
          Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)) := by
        rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
        dsimp only [j]
        rw [Category.assoc, ← Category.assoc (Spec.map
          (Scheme.Spec.residueFieldIso (CommRingCat.of R) x).hom),
          ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
      _ = _ := by
        rw [← Spec.map_comp]
        congr 1
        apply (cancel_mono e.hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        ext r
        exact (I.algebraMap_quotient_residueField_mk r).symm
  have h := isReduced_pullback_comp_right_of_isOpenImmersion p
    ((Spec (CommRingCat.of R)).fromSpecResidueField x) j
  rwa [hcomp] at h

/-- Reducedness of a quotient base change is reducedness of the corresponding quotient
of the actual affine section algebra. -/
theorem isReduced_quotient_globalSectionAlgebra
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    [AlgebraicGeometry.IsReduced
      (pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    letI := globalSectionAlgebra p
    _root_.IsReduced (Γ(X, ⊤) ⧸ I.map (algebraMap R Γ(X, ⊤))) := by
  let := globalSectionAlgebra p
  let A := Γ(X, ⊤)
  let b := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : AlgebraicGeometry.IsReduced (pullback (X.isoSpec.inv ≫ p) b) :=
    isReduced_pullback_comp_of_isOpenImmersion X.isoSpec.inv p b
  have : AlgebraicGeometry.IsReduced
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) b) := by
    rwa [globalSectionAlgebra_specMap p]
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (A ⊗[R] (R ⧸ I)))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso R A (R ⧸ I)).inv
  have : _root_.IsReduced (A ⊗[R] (R ⧸ I)) :=
    (affine_isReduced_iff (CommRingCat.of (A ⊗[R] (R ⧸ I)))).mp inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).injective

/-- A regular base scalar remains regular in flat actual affine section algebras. -/
theorem scalar_mem_nonZeroDivisors_of_flat
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p]
    {r : R} (hr : r ∈ nonZeroDivisors R) :
    p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) ∈
      nonZeroDivisors Γ(X, ⊤) := by
  let := globalSectionAlgebra p
  let : Module.Flat R Γ(X, ⊤) := flat_globalSectionAlgebra p
  apply mem_nonZeroDivisors_iff_left.mpr
  intro a ha
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors hr (a₁ := a) (a₂ := 0)
  change algebraMap R Γ(X, ⊤) r * a = 0 at ha
  simpa only [Algebra.smul_def, map_zero, mul_zero] using ha

/-- A reduced quotient base change makes the corresponding actual scalar divisor radical. -/
theorem scalar_span_isRadical_of_reduced_quotient
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of R)) (r : R)
    [AlgebraicGeometry.IsReduced
      (pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))))] :
    (Ideal.span {p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)}).IsRadical := by
  let := globalSectionAlgebra p
  have := isReduced_quotient_globalSectionAlgebra p (Ideal.span {r})
  have hmap : (Ideal.span {r}).map (algebraMap R Γ(X, ⊤)) =
      Ideal.span {p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  rwa [← hmap]

/-- Flatness and a reduced quotient base change supply the local hypotheses for
clopen globalization of the actual scalar principal open. -/
theorem preconnectedSpace_basicOpen_of_flat_reduced_quotient
    {R : Type u} [CommRing R] {X : Scheme.{u}} [PreconnectedSpace X]
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [UniversallyOpen p]
    (r : R) (hr : r ∈ nonZeroDivisors R)
    (hDense : Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)))
    [AlgebraicGeometry.IsReduced
      (pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))))] :
    PreconnectedSpace
      (X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) := by
  let t := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  have hD : (X.basicOpen t : Set X) =
      p ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    dsimp only [t]
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    rfl
  apply preconnectedSpace_basicOpen_of_locally_radical X t
  · rw [hD]
    exact hDense.preimage p.isOpenMap
  · intro U hU
    let : IsAffine U := hU
    simpa only [t, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      scalar_mem_nonZeroDivisors_of_flat (U.ι ≫ p) hr
  · intro U hU
    let : IsAffine U := hU
    let : AlgebraicGeometry.IsReduced
        (pullback (U.ι ≫ p)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))))) :=
      isReduced_pullback_comp_of_isOpenImmersion U.ι p _
    simpa only [t, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      scalar_span_isRadical_of_reduced_quotient (U.ι ≫ p) r

namespace FlatReducedDvrConnectedness

lemma point_eq_generic_or_closed (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (p : PrimeSpectrum R) :
    p = ⟨⊥, inferInstance⟩ ∨ p = IsLocalRing.closedPoint R := by
  by_cases hp : p.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hp)
  · right
    obtain ⟨P, hP, huniq⟩ :=
      ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance).2
    exact PrimeSpectrum.ext ((huniq p.asIdeal ⟨hp, p.isPrime⟩).trans
      (huniq (IsLocalRing.maximalIdeal R)
        ⟨IsDiscreteValuationRing.not_a_field R, inferInstance⟩).symm)

lemma basicOpen_eq_generic (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) = {⟨⊥, inferInstance⟩} := by
  ext p
  rcases point_eq_generic_or_closed R p with rfl | rfl
  · simp [hπ.ne_zero]
  · have hmem : π ∈ IsLocalRing.maximalIdeal R := by
      rw [hπ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton π)
    have hne : IsLocalRing.closedPoint R ≠ (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
      intro heq
      exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal heq)
    simpa [PrimeSpectrum.mem_basicOpen, IsLocalRing.closedPoint, hmem] using hne

/-- The generic fibre is preconnected when the closed quotient fibre is reduced. -/
theorem preconnectedSpace_genericFiber_of_reduced_quotient
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) [PreconnectedSpace X]
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [LocallyOfFinitePresentation p]
    {π : R} (hπ : Irreducible π)
    [AlgebraicGeometry.IsReduced
      (pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π})))))] :
    PreconnectedSpace (p.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let t := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  have hDense : Dense (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) := by
    apply (PrimeSpectrum.basicOpen π).isOpen.dense
    refine ⟨η, ?_⟩
    change π ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hπ.ne_zero
  have : PreconnectedSpace ↥(X.basicOpen t : Set X) :=
    preconnectedSpace_basicOpen_of_flat_reduced_quotient p π
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero) hDense
  have hD : (X.basicOpen t : Set X) = p ⁻¹' {η} := by
    dsimp only [t]
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact congrArg (fun Z : Set (PrimeSpectrum R) => p ⁻¹' Z)
      (basicOpen_eq_generic R hπ)
  let e := (p.fiberHomeo η).trans (Homeomorph.setCongr hD).symm
  exact e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous

/-- A flat family locally of finite presentation over a DVR has preconnected
generic fibre if its total space is preconnected and its actual special fibre is reduced. -/
theorem preconnectedSpace_genericFiber_of_reduced_specialFiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) [PreconnectedSpace X]
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [LocallyOfFinitePresentation p]
    [hred : AlgebraicGeometry.IsReduced (p.fiber (IsLocalRing.closedPoint R))] :
    PreconnectedSpace (p.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : AlgebraicGeometry.IsReduced
      (p.fiber (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)) := hred
  have : AlgebraicGeometry.IsReduced
      (pullback p (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))) :=
    isReduced_pullback_quotient_of_reduced_fiber p (IsLocalRing.maximalIdeal R)
  have : AlgebraicGeometry.IsReduced
      (pullback p (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π}))))) := by
    rwa [hπ.maximalIdeal_eq] at this
  exact preconnectedSpace_genericFiber_of_reduced_quotient R X p hπ

/-- With nonempty connected total space, the same generic fibre is connected. -/
theorem connectedSpace_genericFiber_of_reduced_specialFiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) [ConnectedSpace X]
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [LocallyOfFinitePresentation p]
    [AlgebraicGeometry.IsReduced (p.fiber (IsLocalRing.closedPoint R))] :
    ConnectedSpace (p.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have : PreconnectedSpace (p.fiber η) :=
    preconnectedSpace_genericFiber_of_reduced_specialFiber R X p
  have hDense : Dense ({η} : Set (PrimeSpectrum R)) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [← basicOpen_eq_generic R hπ]
    apply (PrimeSpectrum.basicOpen π).isOpen.dense
    refine ⟨η, ?_⟩
    change π ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hπ.ne_zero
  have hne : (p ⁻¹' {η}).Nonempty := (hDense.preimage p.isOpenMap).nonempty
  exact { toNonempty := hne.to_subtype.map (p.fiberHomeo η).symm }

end FlatReducedDvrConnectedness

end Langlands.AlgebraicGeometry
