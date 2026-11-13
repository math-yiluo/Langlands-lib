import Langlands.Geometry.FormalGroup.ModuleBaseChange

/-! # Coherence of formal-module coefficient extension -/

noncomputable section

universe u v w x y

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {T : Type x} [CommRing T] [Algebra O T]
variable {U : Type y} [CommRing U] [Algebra O U]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace Iso

/-- Equality of integral isomorphisms is detected by their forward maps. -/
@[ext]
theorem ext_hom {f g : Iso M N} (h : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := by
    calc
      f.inv = f.inv.comp (Hom.id N) := (Hom.comp_id _).symm
      _ = f.inv.comp (g.hom.comp g.inv) := by rw [g.hom_inv]
      _ = (f.inv.comp f.hom).comp g.inv := by rw [h, Hom.comp_assoc]
      _ = g.inv := by rw [f.inv_hom, Hom.id_comp]
  cases f
  cases g
  cases h
  cases hi
  rfl

end Iso

/-- The identity-coefficient comparison is natural in integral formal maps. -/
theorem mapIdIso_natural (f : Hom M N) :
    f.comp (mapIdIso M).hom = (mapIdIso N).hom.comp (f.map (AlgHom.id O R)) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  change f.toHom.toCoordinateMap.comp CoordinateMap.id =
    CoordinateMap.id.comp (f.toHom.toCoordinateMap.map (RingHom.id R))
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp, CoordinateMap.map_ringHom_id]

/-- The composite-coefficient comparison is natural in integral formal maps. -/
theorem mapCompIso_natural (f : Hom M N) (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T) :
    (f.map (ψ.comp φ)).comp (mapCompIso M φ ψ).hom =
      (mapCompIso N φ ψ).hom.comp ((f.map φ).map ψ) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  change (f.toHom.toCoordinateMap.map (ψ.comp φ).toRingHom).comp CoordinateMap.id =
    CoordinateMap.id.comp ((f.toHom.toCoordinateMap.map φ.toRingHom).map ψ.toRingHom)
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp, CoordinateMap.map_ringHom_comp]
  rfl

/-- Inserting an identity coefficient map on the source gives the unit comparison. -/
theorem mapCompIso_id_left (M : ModuleLaw O R σ) (φ : R →ₐ[O] S) :
    mapCompIso M (AlgHom.id O R) φ = (mapIdIso M).map φ := by
  apply Iso.ext_hom
  apply Hom.ext
  apply CommLaw.Hom.ext
  exact (CoordinateMap.map_id φ.toRingHom).symm

/-- Inserting an identity coefficient map on the target gives the unit comparison. -/
theorem mapCompIso_id_right (M : ModuleLaw O R σ) (φ : R →ₐ[O] S) :
    mapCompIso M φ (AlgHom.id O S) = mapIdIso (M.map φ) := by
  apply Iso.ext_hom
  apply Hom.ext
  apply CommLaw.Hom.ext
  rfl

/-- The two comparisons for three successive coefficient maps agree. -/
theorem mapCompIso_assoc (M : ModuleLaw O R σ) (φ : R →ₐ[O] S)
    (ψ : S →ₐ[O] T) (χ : T →ₐ[O] U) :
    ((mapCompIso M φ ψ).map χ).trans (mapCompIso M (ψ.comp φ) χ) =
      (mapCompIso (M.map φ) ψ χ).trans (mapCompIso M φ (χ.comp ψ)) := by
  apply Iso.ext_hom
  apply Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp (CoordinateMap.id.map χ.toRingHom) =
    CoordinateMap.id.comp CoordinateMap.id
  rw [CoordinateMap.map_id]

/-- A commutative square of coefficient maps identifies its two base changes. -/
def mapSquareIso (M : ModuleLaw O R σ) (φ : R →ₐ[O] S) (ψ : S →ₐ[O] U)
    (η : R →ₐ[O] T) (θ : T →ₐ[O] U) (h : ψ.comp φ = θ.comp η) :
    Iso ((M.map φ).map ψ) ((M.map η).map θ) :=
  Iso.ofIdenticalCoordinates
    (by
      change (M.groupLaw.addition.map φ.toRingHom).map ψ.toRingHom =
        (M.groupLaw.addition.map η.toRingHom).map θ.toRingHom
      rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
      exact congrArg (fun f => M.groupLaw.addition.map f.toRingHom) h)
    (fun a => by
      change ((M.action a).toCoordinateMap.map φ.toRingHom).map ψ.toRingHom =
        ((M.action a).toCoordinateMap.map η.toRingHom).map θ.toRingHom
      rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
      exact congrArg (fun f => (M.action a).toCoordinateMap.map f.toRingHom) h)

/-- The square comparison is natural in integral formal-module maps. -/
theorem mapSquareIso_natural (f : Hom M N) (φ : R →ₐ[O] S) (ψ : S →ₐ[O] U)
    (η : R →ₐ[O] T) (θ : T →ₐ[O] U) (h : ψ.comp φ = θ.comp η) :
    ((f.map η).map θ).comp (mapSquareIso M φ ψ η θ h).hom =
      (mapSquareIso N φ ψ η θ h).hom.comp ((f.map φ).map ψ) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  change ((f.toHom.toCoordinateMap.map η.toRingHom).map θ.toRingHom).comp
      CoordinateMap.id =
    CoordinateMap.id.comp ((f.toHom.toCoordinateMap.map φ.toRingHom).map ψ.toRingHom)
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp,
    CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
  exact congrArg (fun g => f.toHom.toCoordinateMap.map g.toRingHom) h.symm

namespace RationalHom

variable {F : Type*} [Field F] [Algebra O F]

/-- Rational coefficient extension respects the identity comparison. -/
theorem mapIdIso_natural (f : RationalHom F M N) :
    comp f (ofHom (mapIdIso M).hom) =
      comp (ofHom (mapIdIso N).hom) (map (AlgHom.id O R) f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [add_comp, comp_add, _root_.map_add, hf, hg]
  | tmul a f =>
    simp only [ofHom_apply, map_tmul, comp_tmul, mul_one, one_mul]
    rw [ModuleLaw.mapIdIso_natural]

/-- Rational coefficient extension respects the composite comparison. -/
theorem mapCompIso_natural (f : RationalHom F M N) (φ : R →ₐ[O] S)
    (ψ : S →ₐ[O] T) :
    comp (map (ψ.comp φ) f) (ofHom (mapCompIso M φ ψ).hom) =
      comp (ofHom (mapCompIso N φ ψ).hom) (map ψ (map φ f)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [add_comp, comp_add, _root_.map_add, hf, hg]
  | tmul a f =>
    simp only [ofHom_apply, map_tmul, comp_tmul, mul_one, one_mul]
    rw [ModuleLaw.mapCompIso_natural]

/-- The square comparison is natural on tensor-product rational Hom. -/
theorem mapSquareIso_natural (f : RationalHom F M N) (φ : R →ₐ[O] S)
    (ψ : S →ₐ[O] U) (η : R →ₐ[O] T) (θ : T →ₐ[O] U)
    (h : ψ.comp φ = θ.comp η) :
    comp (map θ (map η f)) (ofHom (mapSquareIso M φ ψ η θ h).hom) =
      comp (ofHom (mapSquareIso N φ ψ η θ h).hom) (map ψ (map φ f)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [add_comp, comp_add, _root_.map_add, hf, hg]
  | tmul a f =>
    simp only [ofHom_apply, map_tmul, comp_tmul, mul_one, one_mul]
    rw [ModuleLaw.mapSquareIso_natural]

end RationalHom

namespace QuasiIsogeny

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Identity coefficient comparisons commute with quasi-isogenies. -/
theorem mapIdIso_natural (f : QuasiIsogeny F M N) :
    (ofIso (mapIdIso M)).trans f =
      (f.map (AlgHom.id O R)).trans (ofIso (mapIdIso N)) := by
  apply ext_hom
  exact RationalHom.mapIdIso_natural f.hom

/-- Composite coefficient comparisons commute with quasi-isogenies. -/
theorem mapCompIso_natural (f : QuasiIsogeny F M N) (φ : R →ₐ[O] S)
    (ψ : S →ₐ[O] T) :
    (ofIso (mapCompIso M φ ψ)).trans (f.map (ψ.comp φ)) =
      ((f.map φ).map ψ).trans (ofIso (mapCompIso N φ ψ)) := by
  apply ext_hom
  exact RationalHom.mapCompIso_natural f.hom φ ψ

/-- The square comparison commutes with quasi-isogenies. -/
theorem mapSquareIso_natural (f : QuasiIsogeny F M N) (φ : R →ₐ[O] S)
    (ψ : S →ₐ[O] U) (η : R →ₐ[O] T) (θ : T →ₐ[O] U)
    (h : ψ.comp φ = θ.comp η) :
    (ofIso (mapSquareIso M φ ψ η θ h)).trans ((f.map η).map θ) =
      ((f.map φ).map ψ).trans (ofIso (mapSquareIso N φ ψ η θ h)) := by
  apply ext_hom
  exact RationalHom.mapSquareIso_natural f.hom φ ψ η θ h

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
