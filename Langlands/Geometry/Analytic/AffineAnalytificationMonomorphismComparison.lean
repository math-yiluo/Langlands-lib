import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductProof
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleChartReflection
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof
import Langlands.Geometry.Analytic.AffineAnalytificationMaximalCenters
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Monomorphisms of affine analytifications and ring epimorphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory SaturatedAtlasPresentation
open scoped TensorProduct

namespace MonomorphismComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type v} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

section Tower

variable [Algebra A B] [IsScalarTower K A B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The self tensor product `B ⊗[A] B` of a finite type algebra is of finite type. -/
theorem finiteType_tensor (Q : FinitePolynomialPresentation K B) :
    Algebra.FiniteType K (B ⊗[A] B) := by
  have : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  have : Algebra.FiniteType B (B ⊗[A] B) := Algebra.FiniteType.baseChange B
  exact Algebra.FiniteType.trans (S := B) inferInstance inferInstance

/-- A chosen finite polynomial presentation of `B ⊗[A] B`. -/
def tensorPresentation (Q : FinitePolynomialPresentation K B) :
    FinitePolynomialPresentation K (B ⊗[A] B) :=
  haveI := finiteType_tensor (A := A) Q
  FinitePolynomialPresentation.ofFiniteType K (B ⊗[A] B)

/-- The left inclusion `b ↦ b ⊗ 1`. -/
abbrev inclLeft : B →ₐ[K] B ⊗[A] B := Algebra.TensorProduct.includeLeft

/-- The right inclusion `b ↦ 1 ⊗ b`. -/
abbrev inclRight : B →ₐ[K] B ⊗[A] B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).restrictScalars K

/-- The multiplication map `b ⊗ b' ↦ b b'`. -/
abbrev mult : B ⊗[A] B →ₐ[K] B := (Algebra.TensorProduct.lmul' A (S := B)).restrictScalars K

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem mult_comp_inclLeft : (mult (K := K) (A := A) (B := B)).comp inclLeft = AlgHom.id K B := by
  ext b
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem mult_comp_inclRight :
    (mult (K := K) (A := A) (B := B)).comp inclRight = AlgHom.id K B := by
  ext b
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem mult_surjective : Function.Surjective (mult (K := K) (A := A) (B := B)) := fun b =>
  ⟨b ⊗ₜ 1, by simp⟩

variable (T : FinitePolynomialPresentation K (B ⊗[A] B))

/-- The analytified fibre square of `A → B` with itself. -/
theorem isPullback_square :
    IsPullback (localizedHom K Q T inclLeft) (localizedHom K Q T inclRight)
      (localizedHom K P Q (IsScalarTower.toAlgHom K A B))
      (localizedHom K P Q (IsScalarTower.toAlgHom K A B)) :=
  affineAnalytificationFibreProduct K A B B P Q Q T

theorem mult_comp_left :
    localizedHom K T Q mult ≫ localizedHom K Q T inclLeft = 𝟙 _ := by
  rw [← (affineAnalytificationLocalizedFunctoriality K B (B ⊗[A] B) B Q Q T Q inclLeft
    mult).2.2.2.1, mult_comp_inclLeft]
  exact (affineAnalytificationLocalizedFunctoriality K B B B Q Q Q Q (AlgHom.id K B)
    (AlgHom.id K B)).2.2.1

theorem mult_comp_right :
    localizedHom K T Q mult ≫ localizedHom K Q T inclRight = 𝟙 _ := by
  rw [← (affineAnalytificationLocalizedFunctoriality K B (B ⊗[A] B) B Q Q T Q inclRight
    mult).2.2.2.1, mult_comp_inclRight]
  exact (affineAnalytificationLocalizedFunctoriality K B B B Q Q Q Q (AlgHom.id K B)
    (AlgHom.id K B)).2.2.1

/-- If the analytified map is monic, the analytified multiplication map is an
isomorphism. -/
theorem isIso_mult_of_mono [Mono (localizedHom K P Q (IsScalarTower.toAlgHom K A B))] :
    IsIso (localizedHom K T Q mult) := by
  have hpb := isPullback_square P Q T
  have hlr : localizedHom K Q T inclLeft = localizedHom K Q T inclRight :=
    (cancel_mono (localizedHom K P Q (IsScalarTower.toAlgHom K A B))).1 hpb.w
  refine ⟨⟨localizedHom K Q T inclLeft, mult_comp_left Q T, ?_⟩⟩
  apply hpb.hom_ext
  · rw [Category.assoc, mult_comp_left, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, mult_comp_right, Category.comp_id, Category.id_comp, hlr]

/-- A monomorphism of analytifications comes from a ring epimorphism. -/
theorem isEpi_of_mono [Mono (localizedHom K P Q (IsScalarTower.toAlgHom K A B))] :
    Algebra.IsEpi A B := by
  let T := tensorPresentation (A := A) Q
  have hiso := isIso_mult_of_mono P Q T
  have he : etale (localizedHom K T Q mult) := etale_of_isIso _
  have hetale : (mult (K := K) (A := A) (B := B)).toRingHom.Etale :=
    (affineAnalytificationEtale K (B ⊗[A] B) B T Q mult).2.2.mpr
      (isEtale_of_localizedHom_etale T Q mult he)
  have hflat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hetale).1
  have hbase : Function.Surjective (baseMap K T Q mult) := by
    have hb : Function.Bijective (localizedSpaceFunctor.map (localizedHom K T Q mult)) :=
      ConcreteCategory.bijective_of_isIso _
    rw [localizedSpaceFunctor_map_localizedHom] at hb
    exact hb.2
  have hbij := bijective_of_surjective_of_flat_of_baseMap_surjective K T Q mult
    mult_surjective hflat hbase
  refine (Algebra.isEpi_iff_forall_one_tmul_eq (R := A) (A := B)).mpr fun b => hbij.1 ?_
  simp

/-- A ring epimorphism induces a monomorphism of analytifications. -/
theorem mono_of_isEpi [Algebra.IsEpi A B] :
    Mono (localizedHom K P Q (IsScalarTower.toAlgHom K A B)) := by
  have hpb := isPullback_square P Q (tensorPresentation (A := A) Q)
  have hlr : (inclLeft : B →ₐ[K] B ⊗[A] B) = inclRight := by
    ext b
    exact ((Algebra.isEpi_iff_forall_one_tmul_eq (R := A) (A := B)).mp inferInstance b).symm
  refine ⟨fun {Z} g h hgh => ?_⟩
  have h1 := hpb.lift_fst g h hgh
  have h2 := hpb.lift_snd g h hgh
  have hι : localizedHom K Q (tensorPresentation (A := A) Q) inclLeft =
      localizedHom K Q (tensorPresentation (A := A) Q) inclRight := by rw [hlr]
  exact h1.symm.trans ((congrArg (hpb.lift g h hgh ≫ ·) hι).trans h2)

end Tower

end MonomorphismComparison

open MonomorphismComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type v} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- A monomorphism of affine analytifications is induced by an epimorphism of
commutative rings. -/
theorem epi_of_mono_localizedHom [Mono (localizedHom K P Q f)] :
    Epi (CommRingCat.ofHom f.toRingHom) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun k => (f.commutes k).symm
  have hf : IsScalarTower.toAlgHom K A B = f := AlgHom.ext fun _ => rfl
  have : Mono (localizedHom K P Q (IsScalarTower.toAlgHom K A B)) := by
    rw [hf]
    infer_instance
  have := isEpi_of_mono P Q
  exact CommRingCat.epi_iff_epi.mpr inferInstance

/-- An epimorphism of commutative rings induces a monomorphism of affine
analytifications. -/
theorem mono_localizedHom_of_epi [Epi (CommRingCat.ofHom f.toRingHom)] :
    Mono (localizedHom K P Q f) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun k => (f.commutes k).symm
  have hf : IsScalarTower.toAlgHom K A B = f := AlgHom.ext fun _ => rfl
  have : Algebra.IsEpi A B := CommRingCat.epi_iff_epi.mp (inferInstanceAs
    (Epi (CommRingCat.ofHom f.toRingHom)))
  rw [← hf]
  exact mono_of_isEpi P Q

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The spectrum of a ring epimorphism is a monomorphism of schemes. -/
theorem mono_specMap_of_epi {R S : CommRingCat.{v}} (φ : R ⟶ S) [Epi φ] :
    Mono (_root_.AlgebraicGeometry.Spec.map φ) :=
  Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts.mono_specMap_of_epi φ

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A ring map whose spectrum is a monomorphism of schemes is an epimorphism. -/
theorem epi_of_mono_specMap {R S : CommRingCat.{v}} (φ : R ⟶ S)
    [Mono (_root_.AlgebraicGeometry.Spec.map φ)] : Epi φ := by
  have : Mono (_root_.AlgebraicGeometry.Scheme.Spec.map φ.op) :=
    inferInstanceAs (Mono (_root_.AlgebraicGeometry.Spec.map φ))
  have : Mono φ.op := _root_.AlgebraicGeometry.Scheme.Spec.mono_of_mono_map this
  exact unop_epi_of_mono φ.op

end Langlands.Analytic.AffineAnalytification
