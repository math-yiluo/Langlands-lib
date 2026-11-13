import Langlands.Geometry.FormalGroup.RationalMorphism

/-! # Base change of formal O-module isomorphisms and quasi-isogenies -/

noncomputable section

universe u v w x

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {T : Type x} [CommRing T] [Algebra O T]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Hom

@[simp]
theorem map_id (φ : R →ₐ[O] S) : (id M).map φ = id (M.map φ) := by
  apply Hom.ext
  exact CommLaw.Hom.map_id φ.toRingHom

@[simp]
theorem map_comp (φ : R →ₐ[O] S) (g : Hom N P) (f : Hom M N) :
    (g.comp f).map φ = (g.map φ).comp (f.map φ) := by
  apply Hom.ext
  exact CommLaw.Hom.map_comp φ.toRingHom g.toHom f.toHom

/-- The identity coordinate map is O-linear when the formal laws coincide. -/
def ofIdenticalCoordinates {N : ModuleLaw O R σ}
    (hadd : M.groupLaw.addition = N.groupLaw.addition)
    (haction : ∀ a, (M.action a).toCoordinateMap = (N.action a).toCoordinateMap) :
    Hom M N where
  toHom := {
    toCoordinateMap := CoordinateMap.id
    map_add := by
      simpa only [CoordinateMap.id_comp, CoordinateMap.pair_fst_snd,
        CoordinateMap.comp_id] using hadd }
  commutes a := by
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp (M.action a).toCoordinateMap =
      (N.action a).toCoordinateMap.comp CoordinateMap.id
    simpa only [CoordinateMap.id_comp, CoordinateMap.comp_id] using haction a

end Hom

namespace Iso

/-- Identity formal O-module isomorphism. -/
def refl (M : ModuleLaw O R σ) : Iso M M where
  hom := Hom.id M
  inv := Hom.id M
  inv_hom := Hom.id_comp _
  hom_inv := Hom.id_comp _

/-- Invert a formal O-module isomorphism. -/
def symm (f : Iso M N) : Iso N M where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose formal O-module isomorphisms. -/
def trans (f : Iso M N) (g : Iso N P) : Iso M P where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc g.inv, g.inv_hom, Hom.id_comp, f.inv_hom]
  hom_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc f.hom, f.hom_inv, Hom.id_comp, g.hom_inv]

/-- Coefficient extension preserves integral formal O-module isomorphisms. -/
def map (f : Iso M N) (φ : R →ₐ[O] S) : Iso (M.map φ) (N.map φ) where
  hom := f.hom.map φ
  inv := f.inv.map φ
  inv_hom := by rw [← Hom.map_comp, f.inv_hom, Hom.map_id]
  hom_inv := by rw [← Hom.map_comp, f.hom_inv, Hom.map_id]

/-- The identity coordinate map identifies equal coordinate presentations. -/
def ofIdenticalCoordinates {N : ModuleLaw O R σ}
    (hadd : M.groupLaw.addition = N.groupLaw.addition)
    (haction : ∀ a, (M.action a).toCoordinateMap = (N.action a).toCoordinateMap) :
    Iso M N where
  hom := Hom.ofIdenticalCoordinates hadd haction
  inv := Hom.ofIdenticalCoordinates hadd.symm (fun a => (haction a).symm)
  inv_hom := by
    apply Hom.ext
    apply CommLaw.Hom.ext
    exact CoordinateMap.id_comp _
  hom_inv := by
    apply Hom.ext
    apply CommLaw.Hom.ext
    exact CoordinateMap.id_comp _

end Iso

/-- Identity coefficient extension is canonically isomorphic to the original law. -/
def mapIdIso (M : ModuleLaw O R σ) : Iso (M.map (AlgHom.id O R)) M :=
  Iso.ofIdenticalCoordinates
    (CoordinateMap.map_ringHom_id M.groupLaw.addition)
    (fun a => CoordinateMap.map_ringHom_id (M.action a).toCoordinateMap)

/-- Successive coefficient extension agrees with extension along the composite. -/
def mapCompIso (M : ModuleLaw O R σ) (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T) :
    Iso ((M.map φ).map ψ) (M.map (ψ.comp φ)) :=
  Iso.ofIdenticalCoordinates
    (CoordinateMap.map_ringHom_comp φ.toRingHom ψ.toRingHom M.groupLaw.addition)
    (fun a => CoordinateMap.map_ringHom_comp φ.toRingHom ψ.toRingHom
      (M.action a).toCoordinateMap)

namespace RationalHom

variable {F : Type*} [Field F] [Algebra O F]

@[simp]
theorem map_tmul (φ : R →ₐ[O] S) (a : F) (f : Hom M N) :
    map φ (a ⊗ₜ[O] f) = a ⊗ₜ[O] f.map φ :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem map_ofHom (φ : R →ₐ[O] S) (f : Hom M N) :
    map φ (ofHom (F := F) f) = ofHom (f.map φ) := map_tmul φ 1 f

@[simp]
theorem map_id (φ : R →ₐ[O] S) :
    map φ (id (F := F) M) = id (M.map φ) := by
  simp only [id, map_ofHom, Hom.map_id]

@[simp]
theorem map_comp (φ : R →ₐ[O] S) (g : RationalHom F N P)
    (f : RationalHom F M N) : map φ (comp g f) = comp (map φ g) (map φ f) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [add_comp, _root_.map_add, hg₁, hg₂]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [comp_add, _root_.map_add, hf₁, hf₂]
    | tmul b f => simp only [comp_tmul, map_tmul, Hom.map_comp]

end RationalHom

namespace QuasiIsogeny

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Equality of quasi-isogenies is detected by their rational homomorphisms. -/
@[ext]
theorem ext_hom {f g : QuasiIsogeny F M N} (h : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := g.inv_unique f.inv (by rw [← h]; exact f.inv_hom)
  cases f
  cases g
  cases h
  cases hi
  rfl

/-- Extend coefficients in both a rational homomorphism and its inverse. -/
def map (f : QuasiIsogeny F M N) (φ : R →ₐ[O] S) :
    QuasiIsogeny F (M.map φ) (N.map φ) where
  hom := RationalHom.map φ f.hom
  inv := RationalHom.map φ f.inv
  inv_hom := by rw [← RationalHom.map_comp, f.inv_hom, RationalHom.map_id]
  hom_inv := by rw [← RationalHom.map_comp, f.hom_inv, RationalHom.map_id]

@[simp]
theorem map_refl (φ : R →ₐ[O] S) :
    (refl (F := F) M).map φ = refl (M.map φ) := by
  apply ext_hom
  exact RationalHom.map_id φ

@[simp]
theorem map_symm (f : QuasiIsogeny F M N) (φ : R →ₐ[O] S) :
    f.symm.map φ = (f.map φ).symm := rfl

@[simp]
theorem map_trans (f : QuasiIsogeny F M N) (g : QuasiIsogeny F N P)
    (φ : R →ₐ[O] S) : (f.trans g).map φ = (f.map φ).trans (g.map φ) := by
  apply ext_hom
  exact RationalHom.map_comp φ g.hom f.hom

@[simp]
theorem map_ofIso (f : Iso M N) (φ : R →ₐ[O] S) :
    (ofIso (F := F) f).map φ = ofIso (f.map φ) := by
  apply ext_hom
  exact RationalHom.map_ofHom φ f.hom

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
