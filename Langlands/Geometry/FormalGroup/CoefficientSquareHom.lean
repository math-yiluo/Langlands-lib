import Langlands.Geometry.FormalGroup.AlgebraHomFunctor

/-! # Actual formal Hom along a commutative coefficient square -/

noncomputable section
universe u v w x y

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {A : Type x} [CommRing A] [Algebra O A]
variable {B : Type y} [CommRing B] [Algebra O B]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Hom

/-- Extend an actual map along a coefficient square, using its canonical
identity-coordinate comparisons at both ends. -/
def mapSquareLinear (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ) :
    Hom (M.map α) (N.map α) →ₗ[O]
      Hom ((M.map φ).map δ) ((N.map φ).map δ) where
  toFun f := (mapSquareIso N α β φ δ h).hom.comp
    ((f.map β).comp (mapSquareIso M α β φ δ h).inv)
  map_add' f g := by
    simp only [show (f + g).map β = f.map β + g.map β from
      (mapLinear β).map_add f g, add_comp, comp_add]
  map_smul' a f := by
    simp only [show (a • f).map β = a • f.map β from
      (mapLinear β).map_smul a f, smul_comp, comp_smul, RingHom.id_apply]

@[simp]
theorem mapSquareLinear_coordinates (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (f : Hom (M.map α) (N.map α)) :
    (mapSquareLinear α β φ δ h f).toHom.toCoordinateMap =
      f.toHom.toCoordinateMap.map β.toRingHom := by
  change CoordinateMap.id.comp
    ((f.toHom.toCoordinateMap.map β.toRingHom).comp CoordinateMap.id) = _
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp]

@[simp]
theorem mapSquareLinear_hom_id (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ) :
    mapSquareLinear α β φ δ h (id (M.map α)) = id ((M.map φ).map δ) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [mapSquareLinear_coordinates]
  exact CoordinateMap.map_id _

@[simp]
theorem mapSquareLinear_hom_comp (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (g : Hom (N.map α) (P.map α)) (f : Hom (M.map α) (N.map α)) :
    mapSquareLinear α β φ δ h (g.comp f) =
      (mapSquareLinear α β φ δ h g).comp (mapSquareLinear α β φ δ h f) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [mapSquareLinear_coordinates]
  change (g.toHom.toCoordinateMap.comp f.toHom.toCoordinateMap).map β.toRingHom = _
  rw [CoordinateMap.map_comp]
  rw [← mapSquareLinear_coordinates α β φ δ h,
    ← mapSquareLinear_coordinates α β φ δ h]
  rfl

/-- A global integral map has the same extension along either side of the square. -/
@[simp]
theorem mapSquareLinear_map (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (f : Hom M N) :
    mapSquareLinear α β φ δ h (f.map α) = (f.map φ).map δ := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [mapSquareLinear_coordinates]
  change (f.toHom.toCoordinateMap.map α.toRingHom).map β.toRingHom =
    (f.toHom.toCoordinateMap.map φ.toRingHom).map δ.toRingHom
  rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
  exact congrArg (fun k => f.toHom.toCoordinateMap.map k.toRingHom) h

end Hom

namespace RationalHom

variable {F : Type*} [Field F] [Algebra O F]

/-- Tensor extension of actual formal Hom along the commutative coefficient square. -/
def mapSquareLinear (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ) :
    RationalHom F (M.map α) (N.map α) →ₗ[F]
      RationalHom F ((M.map φ).map δ) ((N.map φ).map δ) :=
  (Hom.mapSquareLinear α β φ δ h).baseChange F

@[simp]
theorem mapSquareLinear_tmul (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (a : F) (f : Hom (M.map α) (N.map α)) :
    mapSquareLinear α β φ δ h (a ⊗ₜ[O] f) =
      a ⊗ₜ[O] Hom.mapSquareLinear α β φ δ h f :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem mapSquareLinear_ofHom (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (f : Hom (M.map α) (N.map α)) :
    mapSquareLinear α β φ δ h (ofHom (F := F) f) =
      ofHom (Hom.mapSquareLinear α β φ δ h f) :=
  mapSquareLinear_tmul α β φ δ h 1 f

@[simp]
theorem mapSquareLinear_hom_id (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ) :
    mapSquareLinear α β φ δ h (id (F := F) (M.map α)) =
      id ((M.map φ).map δ) := by
  simp only [id, mapSquareLinear_ofHom, Hom.mapSquareLinear_hom_id]

@[simp]
theorem mapSquareLinear_hom_comp (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (g : RationalHom F (N.map α) (P.map α))
    (f : RationalHom F (M.map α) (N.map α)) :
    mapSquareLinear α β φ δ h (comp g f) =
      comp (mapSquareLinear α β φ δ h g) (mapSquareLinear α β φ δ h f) := by
  induction g using TensorProduct.inductionOn with
  | add g k hg hk => simp only [add_comp, _root_.map_add, hg, hk]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f k hf hk => simp only [comp_add, _root_.map_add, hf, hk]
    | tmul b f =>
      simp only [comp_tmul, mapSquareLinear_tmul, Hom.mapSquareLinear_hom_comp]

@[simp]
theorem mapSquareLinear_map (α : R →ₐ[O] A) (β : A →ₐ[O] B)
    (φ : R →ₐ[O] S) (δ : S →ₐ[O] B) (h : β.comp α = δ.comp φ)
    (z : RationalHom F M N) :
    mapSquareLinear α β φ δ h (map α z) = map δ (map φ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a f => simp only [map_tmul, mapSquareLinear_tmul, Hom.mapSquareLinear_map]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]

end RationalHom
end Langlands.FormalGroup.ModuleLaw
