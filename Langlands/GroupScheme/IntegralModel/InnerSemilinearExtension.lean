import Langlands.GroupScheme.IntegralModel.SemilinearExtension
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.HomConjugacy

/-! # Integral extension of inner-twisted coefficient transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]
  (k : Type u) [Field k] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (P : IntegralModel R L (baseChanged k L G))
  (σ : L ≃ₐ[k] L) (z : rationalPoints (baseChanged k L G))

/-- The canonical coefficient comparison followed by actual inner conjugation. -/
def innerGaloisDescentIso :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (baseChanged k L G) ≅
      baseChanged k L G :=
  galoisDescentIso k L G σ ≪≫ (baseChanged k L G).innerIso z

private theorem map_innerIso (g : rationalPoints (baseChanged k L G)) :
    rationalPoints.map ((baseChanged k L G).innerIso z).hom g =
      z * g * z⁻¹ := by
  change g ≫ ((baseChanged k L G).innerIso z).hom.hom.hom = _
  rw [comp_innerIso_hom, constantPoint_self]

variable (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (hσ : galoisBaseMap k L σ ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)

/-- The actual generic transport of a pulled-back integral section has the
inner-twisted coefficient formula. -/
theorem twist_integralPointMap_innerGalois (x : P.integralSections) :
    rationalPoints.map (innerGaloisDescentIso k G σ z).hom
        ((P.twist a (galoisBaseMap k L σ) hσ).integralPointMap
          (baseChangeSectionHom a P.group x)) =
      z * rationalConjugate k L G σ (P.integralPointMap x) * z⁻¹ := by
  have hm (g : rationalPoints ((GroupScheme.baseChange (galoisBaseMap k L σ)).obj
      (baseChanged k L G))) :
      rationalPoints.map (innerGaloisDescentIso k G σ z).hom g =
        rationalPoints.map ((baseChanged k L G).innerIso z).hom
          (rationalPoints.map (galoisDescentIso k L G σ).hom g) := by
    simp only [innerGaloisDescentIso, Iso.trans_hom, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc]
  rw [hm, map_innerIso, twist_integralPointMap_galoisIso]

/-- Integral-point stability under the inner-twisted coefficient map and its
inverse extends the generic comparison to an actual integral-model isomorphism. -/
def innerGaloisTwistIso [IsIso a]
    (hext : HasSmoothHomExtension (R := R) (L := L)) (hP : P.IsSmooth)
    (hstable : ∀ g ∈ P.integralPoints,
      z * rationalConjugate k L G σ g * z⁻¹ ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm (z⁻¹ * g * z) ∈ P.integralPoints) :
    (P.twist a (galoisBaseMap k L σ) hσ).Iso P
      (innerGaloisDescentIso k G σ z) :=
  isoOfSectionTransport P (P.twist a (galoisBaseMap k L σ) hσ)
    (innerGaloisDescentIso k G σ z) (baseChangeSectionHom a P.group)
    (fun g => z * rationalConjugate k L G σ g * z⁻¹)
    (fun g => rationalConjugate k L G σ.symm (z⁻¹ * g * z))
    hext hP (P.isSmooth_twist a (galoisBaseMap k L σ) hσ hP)
    (baseChangeSectionHom_surjective a P.group)
    (twist_integralPointMap_innerGalois k G P σ z a hσ)
    (fun g => by
      rw [rationalConjugate_symm_apply]
      simp [mul_assoc])
    hstable hstable'

/-- Applying the integral isomorphism to the coefficient pullback of a section
has exactly the specified inner-twisted value in the original generic group. -/
theorem innerGaloisTwistIso_integralPointMap [IsIso a]
    (hext : HasSmoothHomExtension (R := R) (L := L)) (hP : P.IsSmooth)
    (hstable : ∀ g ∈ P.integralPoints,
      z * rationalConjugate k L G σ g * z⁻¹ ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm (z⁻¹ * g * z) ∈ P.integralPoints)
    (x : P.integralSections) :
    P.integralPointMap
        ((innerGaloisTwistIso k G P σ z a hσ hext hP hstable hstable').integralSectionsEquiv
          (baseChangeSectionHom a P.group x)) =
      z * rationalConjugate k L G σ (P.integralPointMap x) * z⁻¹ :=
  ((innerGaloisTwistIso k G P σ z a hσ hext hP hstable hstable').integralPointMap_naturality
    (baseChangeSectionHom a P.group x)).trans
      (twist_integralPointMap_innerGalois k G P σ z a hσ x)

/-- The extension retains the full generic semilinear compatibility square. -/
theorem innerGaloisTwistIso_generic_comm [IsIso a]
    (hext : HasSmoothHomExtension (R := R) (L := L)) (hP : P.IsSmooth)
    (hstable : ∀ g ∈ P.integralPoints,
      z * rationalConjugate k L G σ g * z⁻¹ ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm (z⁻¹ * g * z) ∈ P.integralPoints) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map P.genericIso.hom ≫
        (innerGaloisDescentIso k G σ z).hom =
      (Descent.squareComparison (Spec.algebraMap R L) (galoisBaseMap k L σ) a
        (Spec.algebraMap R L) hσ P.group).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R L)).map
          (innerGaloisTwistIso k G P σ z a hσ hext hP hstable hstable').iso.hom ≫
            P.genericIso.hom :=
  Hom.twist_generic_comm P a (galoisBaseMap k L σ) hσ
    (innerGaloisTwistIso k G P σ z a hσ hext hP hstable hstable').toHom

end Langlands.GroupScheme.IntegralModel
