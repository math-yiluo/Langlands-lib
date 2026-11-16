import Langlands.GroupScheme.AffineGmAction
import Langlands.CommutativeAlgebra.FixedQuotientFinitePresentation
import Langlands.AlgebraicGeometry.Morphisms.OpenCoverLift
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual fixed schemes of multiplicative-group actions on affine schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineSchemeCoordinates

variable {R : CommRingCat.{u}} (X : Over (Spec R)) [IsAffine X.left]

/-- A quotient of the chosen coordinate algebra. -/
abbrev quotientAlgebra (I : Ideal (algebra X)) : CommAlgCat.{u} R :=
  CommAlgCat.of R (algebra X ⧸ I)

/-- The actual coordinate quotient map. -/
abbrev quotientMap (I : Ideal (algebra X)) : algebra X ⟶ quotientAlgebra X I :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)

/-- The closed affine subscheme cut out by an ideal in the chosen coordinates. -/
abbrev quotientScheme (I : Ideal (algebra X)) : Over (Spec R) :=
  (algSpec R).obj (op (quotientAlgebra X I))

/-- The closed inclusion into the supplied affine scheme. -/
def quotientHom (I : Ideal (algebra X)) : quotientScheme X I ⟶ X :=
  pointEquiv X (quotientAlgebra X I) (quotientMap X I)

instance isClosedImmersion_quotientHom (I : Ideal (algebra X)) :
    IsClosedImmersion (quotientHom X I).left := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (schemeIso X).hom.left)
  infer_instance

instance mono_quotientHom (I : Ideal (algebra X)) : Mono (quotientHom X I) :=
  Over.mono_of_mono_left _

/-- Affine-test factorization through a quotient is vanishing of its ideal. -/
theorem exists_quotient_factor_iff {C : CommAlgCat.{u} R}
    (I : Ideal (algebra X)) (x : algebra X ⟶ C) :
    (∃ y : (algSpec R).obj (op C) ⟶ quotientScheme X I,
      y ≫ quotientHom X I = pointEquiv X C x) ↔ I ≤ RingHom.ker x.hom.toRingHom := by
  constructor
  · rintro ⟨y, hy⟩
    let ψ : quotientAlgebra X I ⟶ C := (algSpec.fullyFaithful.preimage y).unop
    have hψ : (algSpec R).map ψ.op = y := algSpec.fullyFaithful.map_preimage y
    have he : quotientMap X I ≫ ψ = x := by
      apply (pointEquiv X C).injective
      rw [pointEquiv_comp, hψ]
      exact hy
    intro b hb
    change x.hom b = 0
    rw [← he]
    change ψ.hom (Ideal.Quotient.mk I b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  · intro hx
    let ψ : quotientAlgebra X I ⟶ C :=
      CommAlgCat.ofHom (Ideal.Quotient.liftₐ I x.hom hx)
    have hψ : quotientMap X I ≫ ψ = x := by
      apply CommAlgCat.hom_ext
      exact Ideal.Quotient.liftₐ_comp _ _ _
    refine ⟨(algSpec R).map ψ.op, ?_⟩
    change (algSpec R).map ψ.op ≫ pointEquiv X _ (quotientMap X I) = _
    rw [← pointEquiv_comp, hψ]

/-- Smoothness of an affine scheme supplies smoothness of its chosen coordinates. -/
theorem smooth_algebra (hX : Smooth X.hom) : Algebra.Smooth R (algebra X) := by
  let : IsIso (schemeIso X).hom.left :=
    ((Over.forget (Spec R)).mapIso (schemeIso X)).isIso_hom
  have : Smooth (((algSpec R).obj (op (algebra X))).hom) := by
    rw [← (schemeIso X).hom.w]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this |>
    RingHom.smooth_algebraMap.mp

end AffineSchemeCoordinates

namespace GmCoordinateAction

variable {R : CommRingCat.{u}} {X : Over (Spec R)} [IsAffine X.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)

/-- The algebra cut out by every actual fixed coefficient equation. -/
abbrev schemeActionFixedAlgebra : CommAlgCat.{u} R :=
  AffineSchemeCoordinates.quotientAlgebra X (schemeActionFixedIdeal s)

/-- The actual fixed scheme, with its structure morphism to the base. -/
abbrev schemeActionFixedScheme : Over (Spec R) :=
  AffineSchemeCoordinates.quotientScheme X (schemeActionFixedIdeal s)

/-- Its closed inclusion into the original affine scheme. -/
abbrev schemeActionFixedHom : schemeActionFixedScheme s ⟶ X :=
  AffineSchemeCoordinates.quotientHom X (schemeActionFixedIdeal s)

/-- The fixed-scheme inclusion is itself fixed after every scheme refinement. -/
theorem schemeActionFixedHom_isFixed : s.IsFixed (schemeActionFixedHom s) := by
  apply (schemeActionFixedIdeal_le_ker_iff s
    (AffineSchemeCoordinates.quotientMap X (schemeActionFixedIdeal s))).mp
  change schemeActionFixedIdeal s ≤
    RingHom.ker (Ideal.Quotient.mk (schemeActionFixedIdeal s))
  rw [Ideal.mk_ker]

/-- The inclusion represents the full fixedness condition on affine spectra. -/
theorem exists_schemeActionFixed_factor_iff {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ X) :
    (∃ y : (algSpec R).obj (op C) ⟶ schemeActionFixedScheme s,
      y ≫ schemeActionFixedHom s = x) ↔ s.IsFixed x := by
  let φ := (AffineSchemeCoordinates.pointEquiv X C).symm x
  have hφ : AffineSchemeCoordinates.pointEquiv X C φ = x :=
    Equiv.apply_symm_apply _ _
  rw [← hφ, AffineSchemeCoordinates.exists_quotient_factor_iff,
    schemeActionFixedIdeal_le_ker_iff]

/-- The same factorization criterion on any affine relative scheme. -/
theorem exists_schemeActionFixed_factor_iff_of_affine
    {T : Over (Spec R)} [IsAffine T.left] (x : T ⟶ X) :
    (∃ y : T ⟶ schemeActionFixedScheme s, y ≫ schemeActionFixedHom s = x) ↔
      s.IsFixed x := by
  constructor
  · rintro ⟨y, rfl⟩ V b h
    simpa only [Category.assoc] using schemeActionFixedHom_isFixed s V (b ≫ y) h
  · intro hx
    let e := AffineSchemeCoordinates.schemeIso T
    have he : s.IsFixed (e.hom ≫ x) := by
      intro V b h
      simpa only [Category.assoc] using hx V (b ≫ e.hom) h
    obtain ⟨y, hy⟩ := (exists_schemeActionFixed_factor_iff s (e.hom ≫ x)).mpr he
    exact ⟨e.inv ≫ y, by simp only [Category.assoc, hy, e.inv_hom_id_assoc]⟩

/-- The actual closed fixed scheme represents fixedness on every relative test. -/
theorem exists_schemeActionFixed_factor_iff_all
    {T : Over (Spec R)} (x : T ⟶ X) :
    (∃ y : T ⟶ schemeActionFixedScheme s, y ≫ schemeActionFixedHom s = x) ↔
      s.IsFixed x := by
  constructor
  · rintro ⟨y, rfl⟩ V b h
    simpa only [Category.assoc] using schemeActionFixedHom_isFixed s V (b ≫ y) h
  · intro hx
    obtain ⟨y, hy⟩ := Langlands.AlgebraicGeometry.exists_lift_of_openCover
      (schemeActionFixedHom s).left x.left T.left.affineCover (fun i => by
        let U : Over (Spec R) := Over.mk (T.left.affineCover.f i ≫ T.hom)
        let b : U ⟶ T := Over.homMk (T.left.affineCover.f i)
        have : IsAffine U.left := by
          change IsAffine (T.left.affineCover.X i)
          infer_instance
        have hfix : s.IsFixed (b ≫ x) := by
          intro V c h
          simpa only [Category.assoc] using hx V (c ≫ b) h
        obtain ⟨z, hz⟩ :=
          (exists_schemeActionFixed_factor_iff_of_affine s (b ≫ x)).mpr hfix
        exact ⟨z.left, congrArg (fun f => f.left) hz⟩)
    refine ⟨Over.homMk y ?_, ?_⟩
    · rw [← (schemeActionFixedHom s).w, ← Category.assoc, hy, x.w]
    · apply Over.OverMorphism.ext
      exact hy

/-- Fixed coordinates of a smooth affine scheme are smooth over any base ring. -/
theorem smooth_schemeActionFixedAlgebra
    [Algebra.Smooth R (AffineSchemeCoordinates.algebra X)] :
    Algebra.Smooth R (schemeActionFixedAlgebra s) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.smooth_fixedQuotient
    (coaction (ofPointwiseSchemeAction s)).hom
    (coaction_coefficient_homogeneous (ofPointwiseSchemeAction s))

/-- The constructed actual fixed scheme is smooth when the original scheme is smooth. -/
theorem smooth_schemeActionFixedScheme (hX : Smooth X.hom) :
    Smooth (schemeActionFixedScheme s).hom := by
  let := AffineSchemeCoordinates.smooth_algebra X hX
  let := smooth_schemeActionFixedAlgebra s
  have h : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap R (schemeActionFixedAlgebra s)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact h

end GmCoordinateAction

end Langlands.GroupScheme
