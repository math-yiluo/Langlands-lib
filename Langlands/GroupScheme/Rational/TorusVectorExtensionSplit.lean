import Langlands.Algebra.CentralTorusVectorExtensionHopf
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # Retractions of central split-torus extensions with vector quotient -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralExtensionHopfSpec

open RelativeRoot

variable {K : Type u} [Field K] {A B : CommHopfAlgCat.{u} (CommRingCat.of K)}

/-- Central extension data with an arbitrary affine Hopf-algebra quotient. -/
theorem isCentralTorusExtension {J : Type u}
    (φ : B ⟶ A) (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ))
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hc : IsCentral ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    CentralTorusVectorExtensionHopf.IsCentralExtension (K := K) (A := A) φ.hom π.hom where
  injective := (faithfullyFlat_of_isFppfQuotient φ hq).injective
  surjective := surjective_of_isClosedSubgroup π hz
  comp_eq b := by
    have h := congrArg (fun f => f b) (comp_eq_of_range_kernelι φ π hq.2.2.2)
    simpa using h
  isCentral := rTensor_comul_eq_of_isCentral π hc
  invariants a ha := by
    have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
    refine exists_eq_of_lTensor_comul_eq φ π (Over.mono_of_mono_left _) hq a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K (J → ℤ)).lTensor A (comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

/-- A polynomial quotient algebra satisfies the two algebraic splitting hypotheses. -/
theorem exists_section_of_polynomial {I : Type} {J : Type u} [Finite J]
    (φ : B ⟶ A) (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ))
    (h : CentralTorusVectorExtensionHopf.IsCentralExtension (K := K) (A := A) φ.hom π.hom)
    (e : MvPolynomial I K ≃ₐ[K] B) :
    ∃ s : Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ) ⟶ A, s ≫ π = 𝟙 _ := by
  have : IsDomain B := e.symm.injective.isDomain e.symm.toRingHom
  have : UniqueFactorizationMonoid B := e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have : Subsingleton (CommRing.Pic B) := inferInstance
  have hs : ∀ f : B ⊗[K] B, IsUnit f → ∃ d : K, f = d • 1 := by
    intro f hf
    let ee := Algebra.TensorProduct.congr e.symm e.symm
    obtain ⟨d, hd⟩ := PolynomialTensorUnits.exists_eq_smul_one K I (ee f) (hf.map ee.toRingHom)
    refine ⟨d, ee.injective ?_⟩
    simpa only [map_smul, map_one] using hd
  let s : Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ) ⟶ A :=
    CommHopfAlgCat.ofHom (CentralTorusVectorExtensionHopf.sectionMap h hs)
  refine ⟨s, ?_⟩
  apply CommHopfAlgCat.hom_ext
  exact CentralTorusVectorExtensionHopf.comp_sectionMap h hs

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A central split torus with vector quotient admits an actual group-scheme retraction. -/
theorem exists_retraction_of_split_vector_quotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] {J : Type u} [Finite J] {n : ℕ}
    (eZ0 : Z ≅ splitTorus (Spec (CommRingCat.of K)) J)
    (eQ0 : Q ≅ VectorGroup.groupScheme (CommRingCat.of K) n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    ∃ r : E ⟶ Z, z ≫ r = 𝟙 Z := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let R := CommRingCat.of K
  have : IsAffine Q.X.left := by
    have hQ : IsAffineHom Q.X.hom :=
      (RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso.mpr ⟨eQ0⟩).isAffineHom
    exact isAffine_of_isAffineHom Q.X.hom
  let A := AffineCoordinates.hopfAlgebra E
  let B := AffineCoordinates.hopfAlgebra Q
  let eE := AffineCoordinates.hopfSpecIso E
  let eQ := AffineCoordinates.hopfSpecIso Q
  let eZ : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R (J → ℤ))) ≅ Z :=
    Diagonalizable.hopfSpecIso R (J → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ)) ≪≫ eZ0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R (J → ℤ) :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ z ≫ eE.symm.hom)).unop
  let φ : B ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eE.symm.inv ≫ p ≫ eQ.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eZ.hom ≫ z ≫ eE.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eE.symm.inv ≫ p ≫ eQ.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hz' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hz.comp_iso eE.symm)
  have hc' : IsCentral ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact (hc.comp_iso eE.symm).comp eZ.hom
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eE.symm).comp_iso eQ.symm
  let ePoly : MvPolynomial (Fin n) K ≃ₐ[K] B :=
    CommAlgCat.algEquivOfIso
      (algSpec.fullyFaithful.preimageIso
        (AffineCoordinates.coordinateSchemeIso Q ≪≫
          (Grp.forget _).mapIso eQ0)).unop
  obtain ⟨s, hs⟩ := exists_section_of_polynomial φ π
    (isCentralTorusExtension φ π hz' hc' hq') ePoly
  refine ⟨eE.inv ≫ (hopfSpec R).map s.op ≫ eZ.hom, ?_⟩
  have hh := congrArg (fun f => (hopfSpec R).map f.op) hs
  simp only [op_comp, Functor.map_comp, op_id] at hh
  rw [CategoryTheory.Functor.map_id] at hh
  calc
    z ≫ (eE.inv ≫ (hopfSpec R).map s.op ≫ eZ.hom) =
        eZ.inv ≫ ((hopfSpec R).map π.op ≫ (hopfSpec R).map s.op) ≫ eZ.hom := by
      rw [hπ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.symm_hom]
    _ = 𝟙 Z := by
      rw [hh, Category.id_comp]
      exact eZ.inv_hom_id

/-- A chosen group-scheme retraction of the specified central split torus. -/
def retractionOfSplitVectorQuotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] {J : Type u} [Finite J] {n : ℕ}
    (eZ0 : Z ≅ splitTorus (Spec (CommRingCat.of K)) J)
    (eQ0 : Q ≅ VectorGroup.groupScheme (CommRingCat.of K) n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) : E ⟶ Z :=
  Classical.choose (exists_retraction_of_split_vector_quotient eZ0 eQ0 z hz hc p hq)

@[reassoc]
theorem comp_retractionOfSplitVectorQuotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] {J : Type u} [Finite J] {n : ℕ}
    (eZ0 : Z ≅ splitTorus (Spec (CommRingCat.of K)) J)
    (eQ0 : Q ≅ VectorGroup.groupScheme (CommRingCat.of K) n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    z ≫ retractionOfSplitVectorQuotient eZ0 eQ0 z hz hc p hq = 𝟙 Z :=
  Classical.choose_spec (exists_retraction_of_split_vector_quotient eZ0 eQ0 z hz hc p hq)

end Langlands.GroupScheme.CentralExtensionHopfSpec
