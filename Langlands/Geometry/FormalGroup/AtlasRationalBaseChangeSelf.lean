import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasBaseChangeSelf

/-! # Naturality of the actual identity coefficient comparison -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Equal original covers give equal covers over the supplied target scalar structure. -/
theorem baseAlongMapOpens_eq {S : Type v} [CommRing S] [Algebra O S]
    (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) (f : R →ₐ[O] S)
    (h : X.opens = Y.opens) :
    (X.baseChangeAlong f).opens = (Y.baseChangeAlong f).opens :=
  baseOpens_eq (coefficientTest f) h

namespace Hom

/-- The actual identity-extension comparison is natural in integral formal maps. -/
theorem baseId_natural (f : Hom X Y h) :
    Y.baseIdHom.comp (h := baseAlongMapOpens_eq X Y (AlgHom.id O R) h)
        (f.baseChangeAlong (AlgHom.id O R)) =
      f.comp X.baseIdHom := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
    (((f.baseChange (coefficientTest (AlgHom.id O R))).reAlgebra _
      (coefficientAlgebraAlong_eq (AlgHom.id O R))).hom A
        (sourceChart Y.baseIdOpens_eq b) hb).toHom.toCoordinateMap =
    (f.hom A b hb).toHom.toCoordinateMap.comp CoordinateMap.id
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]
  refine ((f.baseChange (coefficientTest (AlgHom.id O R))).reAlgebra_coordinates _
    (coefficientAlgebraAlong_eq (AlgHom.id O R)) A
      (show Y.baseOpens (coefficientTest (AlgHom.id O R)) from
        sourceChart (X := Y.baseChangeAlong (AlgHom.id O R)) (Y := Y)
          Y.baseIdOpens_eq b) hb).trans ?_
  refine (f.baseChange_coordinates (coefficientTest (AlgHom.id O R)) A
    (show Y.baseOpens (coefficientTest (AlgHom.id O R)) from
      sourceChart (X := Y.baseChangeAlong (AlgHom.id O R)) (Y := Y)
        Y.baseIdOpens_eq b) hb).trans ?_
  have hn := f.natural (identityTestHom (O := O) A) (Y.baseIdSource b)
    (Y.baseSource_unit (coefficientTest (AlgHom.id O R)) A _ hb)
    (Y.baseIdSource_unit A b hb)
  change (f.hom (restrictCoefficientAlgebra (AlgHom.id O R) A)
    (Y.baseIdSource b) _).toHom.toCoordinateMap.map (RingHom.id A) = _ at hn
  exact (CoordinateMap.map_ringHom_id _).symm.trans
    (hn.trans (f.hom_coordinates_eq A _ b _ hb (Y.baseIdSource_eq b)))

/-- The inverse identity-extension comparison is natural in the same integral map. -/
theorem baseId_inv_natural (f : Hom X Y h) :
    (f.baseChangeAlong (AlgHom.id O R)).comp
        (k := baseAlongMapOpens_eq X Y (AlgHom.id O R) h) X.baseIdInv =
      Y.baseIdInv.comp f := by
  calc
    (f.baseChangeAlong (AlgHom.id O R)).comp
        (k := baseAlongMapOpens_eq X Y (AlgHom.id O R) h) X.baseIdInv =
        (Y.baseIdIso.inv.comp Y.baseIdIso.hom).comp
          ((f.baseChangeAlong (AlgHom.id O R)).comp
            (k := baseAlongMapOpens_eq X Y (AlgHom.id O R) h) X.baseIdInv) := by
      rw [Y.baseIdIso.inv_hom, id_comp]
    _ = Y.baseIdIso.inv.comp
        ((Y.baseIdHom.comp (h := baseAlongMapOpens_eq X Y (AlgHom.id O R) h)
          (f.baseChangeAlong (AlgHom.id O R))).comp X.baseIdInv) := by
      exact (comp_assoc _ _ _).trans (congrArg (fun z => Y.baseIdIso.inv.comp z)
        (comp_assoc Y.baseIdHom (f.baseChangeAlong (AlgHom.id O R)) X.baseIdInv).symm)
    _ = Y.baseIdInv.comp f := by
      rw [f.baseId_natural, comp_assoc]
      exact (congrArg (fun z => Y.baseIdInv.comp (f.comp z))
        X.baseIdIso.hom_inv).trans (congrArg (fun z => Y.baseIdInv.comp z) (comp_id f))

end Hom

namespace RationalHom

/-- Rational maps commute with the rationalization of the actual identity comparison. -/
theorem baseId_natural (f : RationalHom F X Y h) :
    comp (h := baseAlongMapOpens_eq X Y (AlgHom.id O R) h)
      (ofHom (F := F) Y.baseIdHom)
      (baseChangeAlong (X := X) (Y := Y) (h := h) (AlgHom.id O R) f) =
      comp f (ofHom X.baseIdHom) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, comp_add, add_comp, hf, hg]
  | tmul a f =>
    have ht : (a ⊗ₜ[O] f : RationalHom F X Y h) = a • ofHom f := by
      simp only [ofHom_apply, smul_tmul', smul_eq_mul, mul_one]
    rw [ht, _root_.map_smul, baseChangeAlong_ofHom, comp_smul, smul_comp,
      ← ofHom_comp, ← ofHom_comp, Hom.baseId_natural]

/-- Both rational maps commute with the inverse identity comparison as well. -/
theorem baseId_inv_natural (f : RationalHom F X Y h) :
    comp (k := baseAlongMapOpens_eq X Y (AlgHom.id O R) h)
      (baseChangeAlong (X := X) (Y := Y) (h := h) (AlgHom.id O R) f)
      (ofHom (F := F) X.baseIdInv) =
      comp (ofHom Y.baseIdInv) f := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, comp_add, add_comp, hf, hg]
  | tmul a f =>
    have ht : (a ⊗ₜ[O] f : RationalHom F X Y h) = a • ofHom f := by
      simp only [ofHom_apply, smul_tmul', smul_eq_mul, mul_one]
    rw [ht, _root_.map_smul, baseChangeAlong_ofHom, comp_smul, smul_comp,
      ← ofHom_comp, ← ofHom_comp, Hom.baseId_inv_natural]

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both maps of the actual identity coefficient comparison. -/
def baseIdQuasiIsogeny (X : BasicAtlas O R σ) :
    QuasiIsogeny F (X.baseChangeAlong (AlgHom.id O R)) X X.baseIdOpens_eq :=
  QuasiIsogeny.ofIso X.baseIdIso

@[simp]
theorem baseIdQuasiIsogeny_hom (X : BasicAtlas O R σ) :
    (X.baseIdQuasiIsogeny (F := F)).hom = RationalHom.ofHom X.baseIdHom := rfl

@[simp]
theorem baseIdQuasiIsogeny_inv (X : BasicAtlas O R σ) :
    (X.baseIdQuasiIsogeny (F := F)).inv = RationalHom.ofHom X.baseIdInv := rfl

namespace QuasiIsogeny

/-- Identity extension of a quasi-isogeny commutes with the actual comparison. -/
theorem baseId_natural (f : QuasiIsogeny F X Y h) :
    (f.baseChangeAlong (AlgHom.id O R)).trans
        (h := baseAlongMapOpens_eq X Y (AlgHom.id O R) h) Y.baseIdQuasiIsogeny =
      X.baseIdQuasiIsogeny.trans f := by
  apply ext_hom
  exact RationalHom.baseId_natural f.hom

/-- The inverse identity comparison gives the reverse quasi-isogeny square. -/
theorem baseId_inv_natural (f : QuasiIsogeny F X Y h) :
    X.baseIdQuasiIsogeny.symm.trans
        (k := baseAlongMapOpens_eq X Y (AlgHom.id O R) h)
        (f.baseChangeAlong (AlgHom.id O R)) =
      f.trans Y.baseIdQuasiIsogeny.symm := by
  apply ext_hom
  exact RationalHom.baseId_inv_natural f.hom

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
