import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyIsoTransport

/-! # Coherence for successive coefficient changes of rational sections -/

noncomputable section
universe u v
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem eq_of_local_lifts {X : TopCat.{v}}
    {A B : TopCat.Presheaf (Type v) X} (e : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (H : TopCat.Sheaf (Type v) X) {U : Opens X} (b : B.obj (op U))
    (s t : H.obj.obj (op U))
    (h : ∀ (V : Opens X) (i : V ⟶ U) (a : A.obj (op V)),
      e.app (op V) a = B.map i.op b → H.obj.map i.op s = H.obj.map i.op t) : s = t := by
  have hs : Presieve.IsSheaf (Opens.grothendieckTopology X) H.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  exact (hs.isSeparated _ (Presheaf.imageSieve_mem _ e b)).ext
    (fun V i hi => h V i hi.choose hi.choose_spec)

variable {O : Type u} [CommRing O]
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O T]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- The inverse-image open for the identity coefficient map is the original open. -/
@[simp]
theorem coefficientOpenMap_id_obj (U : Opens (PrimeSpectrum R)) :
    (coefficientOpenMap (AlgHom.id O R)).obj U = U := rfl

/-- Successive inverse images are the inverse image under the composite coefficient map. -/
@[simp]
theorem coefficientOpenMap_comp_obj (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (U : Opens (PrimeSpectrum R)) :
    (coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U) =
      (coefficientOpenMap (ψ.comp φ)).obj U := rfl

/-- Identity coefficient pullback is the actual identity on the structure-section ring. -/
@[simp]
theorem coefficientSectionMap_id (U : Opens (PrimeSpectrum R)) :
    coefficientSectionMap (AlgHom.id O R) U =
      AlgHom.id O ((coefficientStructurePresheaf R).obj (op U)) := by
  ext s
  exact congrArg (fun f => f s) (StructureSheaf.comap_id' U)

/-- The two actual structure-section maps compose as the underlying coefficient maps do. -/
theorem coefficientSectionMap_comp (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (U : Opens (PrimeSpectrum R)) :
    coefficientSectionMap (ψ.comp φ) U =
      (coefficientSectionMap ψ ((coefficientOpenMap φ).obj U)).comp (coefficientSectionMap φ U) := by
  ext s
  exact congrArg (fun f => f s)
    (StructureSheaf.comap_comp φ.toRingHom ψ.toRingHom U
      ((coefficientOpenMap φ).obj U)
      ((coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U))
      (fun _ h => h) (fun _ h => h))

namespace Hom

/-- Integral-isomorphism transport is an actual O-linear map on formal Hom. -/
def transportIsoLinear {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') : Hom M N →ₗ[O] Hom M' N' where
  toFun f := b.hom.comp (f.comp a.inv)
  map_add' f g := by rw [add_comp, comp_add]
  map_smul' c f := by rw [smul_comp, comp_smul, RingHom.id_apply]

@[simp]
theorem transportIsoLinear_coordinates {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') (f : Hom M N) :
    (transportIsoLinear a b f).toHom.toCoordinateMap =
      b.hom.toHom.toCoordinateMap.comp (f.toHom.toCoordinateMap.comp a.inv.toHom.toCoordinateMap) := rfl

end Hom

namespace RationalHom

/-- Tensor extension of actual integral-isomorphism transport. -/
def transportIsoLinear {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') : RationalHom F M N →ₗ[F] RationalHom F M' N' :=
  (Hom.transportIsoLinear a b).baseChange F

@[simp]
theorem transportIsoLinear_tmul {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') (c : F) (f : Hom M N) :
    transportIsoLinear a b (c ⊗ₜ[O] f) = c ⊗ₜ[O] Hom.transportIsoLinear a b f :=
  LinearMap.baseChange_tmul _ _ _

/-- Tensor transport agrees with actual rational composition by the two isomorphisms. -/
theorem transportIsoLinear_eq_comp {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') (z : RationalHom F M N) :
    transportIsoLinear a b z = comp (ofHom b.hom) (comp z (ofHom a.inv)) := by
  induction z using TensorProduct.inductionOn with
  | tmul c f =>
    simp only [transportIsoLinear_tmul, ofHom_apply, comp_tmul, one_mul, mul_one]
    rfl
  | add z w hz hw => simp only [map_add, add_comp, comp_add, hz, hw]

end RationalHom

namespace RationalSection

/-- Integral-isomorphism transport on actual tensor representatives. -/
theorem transportIso_ofRational {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
    (a : Iso M M') (b : Iso N N') (U : Opens (PrimeSpectrum R))
    (z : (rationalHomPresheaf F M N).obj (op U)) :
    transportIso a b U (ofRational U z) =
      ofRational U (RationalHom.transportIsoLinear
        (a.map (IsScalarTower.toAlgHom O R _)) (b.map (IsScalarTower.toAlgHom O R _)) z) := by
  rw [RationalHom.transportIsoLinear_eq_comp]
  change comp (ofRational U (RationalHom.ofHom _))
    (comp (ofRational U z) (ofRational U (RationalHom.ofHom _))) = _
  erw [comp_ofRational, comp_ofRational]
  rfl

end RationalSection

namespace RationalHom

private theorem openBaseChange_identity_transport (U : Opens (PrimeSpectrum R))
    (z : (rationalHomPresheaf F M N).obj (op U)) :
    transportIsoLinear
      ((mapIdIso M).map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      ((mapIdIso N).map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      (openBaseChange (M := M) (N := N) (AlgHom.id O R) U z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a f =>
    change a ⊗ₜ[O] Hom.transportIsoLinear
      ((mapIdIso M).map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      ((mapIdIso N).map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      (Hom.openBaseChange (M := M) (N := N) (AlgHom.id O R) U f) = a ⊗ₜ[O] f
    apply congrArg (fun k => a ⊗ₜ[O] k)
    apply Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.map _).comp
      ((Hom.openBaseChange (M := M) (N := N) (AlgHom.id O R) U f).toHom.toCoordinateMap.comp
        (CoordinateMap.id.map _)) = f.toHom.toCoordinateMap
    rw [CoordinateMap.map_id, CoordinateMap.map_id, CoordinateMap.id_comp,
      CoordinateMap.comp_id, Hom.openBaseChange_coordinates, coefficientSectionMap_id]
    exact CoordinateMap.map_ringHom_id _
  | add z w hz hw =>
    erw [LinearMap.map_add, LinearMap.map_add]
    exact congrArg₂ (fun a b => a + b) hz hw

private theorem openBaseChange_composite_transport (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (U : Opens (PrimeSpectrum R)) (z : (rationalHomPresheaf F M N).obj (op U)) :
    transportIsoLinear
      ((mapCompIso M φ ψ).map (IsScalarTower.toAlgHom O T
        ((coefficientStructurePresheaf T).obj
          (op ((coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U))))))
      ((mapCompIso N φ ψ).map (IsScalarTower.toAlgHom O T
        ((coefficientStructurePresheaf T).obj
          (op ((coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U))))))
      (openBaseChange (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
        (openBaseChange (M := M) (N := N) φ U z)) =
      (rationalHomPresheaf F (M.map (ψ.comp φ)) (N.map (ψ.comp φ))).map
        (eqToHom (coefficientOpenMap_comp_obj φ ψ U)).op
        (openBaseChange (M := M) (N := N) (ψ.comp φ) U z) := by
  let D := (coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U)
  let C := (coefficientOpenMap (ψ.comp φ)).obj U
  let j : D ⟶ C := eqToHom (coefficientOpenMap_comp_obj φ ψ U)
  let A := openBaseChange (M := M) (N := N) (F := F) φ U
  let B := openBaseChange (M := M.map φ) (N := N.map φ) (F := F) ψ
    ((coefficientOpenMap φ).obj U)
  let K := transportIsoLinear (F := F)
    ((mapCompIso M φ ψ).map (IsScalarTower.toAlgHom O T ((coefficientStructurePresheaf T).obj (op D))))
    ((mapCompIso N φ ψ).map (IsScalarTower.toAlgHom O T ((coefficientStructurePresheaf T).obj (op D))))
  let H := openBaseChange (M := M) (N := N) (F := F) (ψ.comp φ) U
  let E := ((rationalHomPresheaf F (M.map (ψ.comp φ)) (N.map (ψ.comp φ))).map j.op).hom
  change K (B (A z)) = E (H z)
  induction z using TensorProduct.inductionOn with
  | tmul a f =>
    change a ⊗ₜ[O] Hom.transportIsoLinear
      ((mapCompIso M φ ψ).map (IsScalarTower.toAlgHom O T ((coefficientStructurePresheaf T).obj (op D))))
      ((mapCompIso N φ ψ).map (IsScalarTower.toAlgHom O T ((coefficientStructurePresheaf T).obj (op D))))
      (Hom.openBaseChange (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
        (Hom.openBaseChange (M := M) (N := N) φ U f)) =
      a ⊗ₜ[O] Hom.algebraMapLinear ((coefficientStructurePresheaf T).map j.op)
        (Hom.openBaseChange (M := M) (N := N) (ψ.comp φ) U f)
    apply congrArg (fun k => a ⊗ₜ[O] k)
    apply Hom.ext
    apply CommLaw.Hom.ext
    rw [Hom.transportIsoLinear_coordinates, Hom.algebraMapLinear_coordinates]
    change (CoordinateMap.id.map _).comp
      ((Hom.openBaseChange (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
        (Hom.openBaseChange (M := M) (N := N) φ U f)).toHom.toCoordinateMap.comp
        (CoordinateMap.id.map _)) =
      ((Hom.openBaseChange (M := M) (N := N) (ψ.comp φ) U f).toHom.toCoordinateMap).map _
    rw [CoordinateMap.map_id, CoordinateMap.map_id, CoordinateMap.id_comp,
      CoordinateMap.comp_id, Hom.openBaseChange_coordinates, Hom.openBaseChange_coordinates,
      Hom.openBaseChange_coordinates, CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
    have hres : (coefficientAlgHom ((coefficientStructurePresheaf T).map j.op)).comp
        (coefficientSectionMap (ψ.comp φ) U) =
        (coefficientSectionMap ψ ((coefficientOpenMap φ).obj U)).comp (coefficientSectionMap φ U) := by
      change (coefficientAlgHom ((coefficientStructurePresheaf T).map (𝟙 (op C)))).comp _ = _
      erw [CategoryTheory.Functor.map_id]
      exact coefficientSectionMap_comp φ ψ U
    exact congrArg (fun k => f.toHom.toCoordinateMap.map k.toRingHom) hres.symm
  | add z w hz hw =>
    rw [A.map_add, B.map_add, K.map_add, H.map_add, E.map_add]
    exact congrArg₂ (fun a b => a + b) hz hw

end RationalHom

namespace RationalSection

/-- Identity coefficient change agrees with the original section after the
actual canonical identity-coefficient comparisons. -/
theorem baseChange_identity_transport (U : Opens (PrimeSpectrum R))
    (z : RationalSection F M N U) :
    transportIso (mapIdIso M) (mapIdIso N) U (baseChange (AlgHom.id O R) U z) = z := by
  apply eq_of_local_lifts (rationalHomTypeUnit F M N) (rationalHomTypeSheaf F M N) z
  intro V i z' hz
  change ofRational V z' = restrict i z at hz
  change restrict i (transportIso (mapIdIso M) (mapIdIso N) U
    (baseChange (AlgHom.id O R) U z)) = restrict i z
  erw [restrict_transportIso, restrict_baseChange, ← hz]
  erw [baseChange_ofRational, transportIso_ofRational]
  erw [RationalHom.openBaseChange_identity_transport]

private theorem baseChange_composite_representative (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (U : Opens (PrimeSpectrum R)) (z : (rationalHomPresheaf F M N).obj (op U)) :
    transportIso (F := F) (M := (M.map φ).map ψ) (N := (N.map φ).map ψ)
      (M' := M.map (ψ.comp φ)) (N' := N.map (ψ.comp φ))
      (mapCompIso M φ ψ) (mapCompIso N φ ψ)
        ((coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U))
        (baseChange (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
          (baseChange (M := M) (N := N) φ U (ofRational U z))) =
      restrict (eqToHom (coefficientOpenMap_comp_obj φ ψ U))
        (baseChange (M := M) (N := N) (F := F) (ψ.comp φ) U (ofRational U z)) := by
  erw [baseChange_ofRational (M := M) (N := N) φ U z,
    baseChange_ofRational (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
      (RationalHom.openBaseChange (M := M) (N := N) φ U z),
    baseChange_ofRational (M := M) (N := N) (ψ.comp φ) U z]
  erw [transportIso_ofRational, restrict_ofRational]
  exact congrArg (ofRational _) (RationalHom.openBaseChange_composite_transport φ ψ U z)

/-- Successive coefficient changes agree with the composite change after the
actual module comparisons and restriction along the canonical equality of opens. -/
theorem baseChange_composite_transport (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (U : Opens (PrimeSpectrum R)) (z : RationalSection F M N U) :
    transportIso (F := F) (M := (M.map φ).map ψ) (N := (N.map φ).map ψ)
      (M' := M.map (ψ.comp φ)) (N' := N.map (ψ.comp φ))
      (mapCompIso M φ ψ) (mapCompIso N φ ψ)
        ((coefficientOpenMap ψ).obj ((coefficientOpenMap φ).obj U))
        (baseChange (M := M.map φ) (N := N.map φ) ψ ((coefficientOpenMap φ).obj U)
          (baseChange (M := M) (N := N) φ U z)) =
      restrict (eqToHom (coefficientOpenMap_comp_obj φ ψ U))
        (baseChange (M := M) (N := N) (F := F) (ψ.comp φ) U z) := by
  apply eq_of_local_lifts (rationalHomTypeUnit F M N)
    ((TopCat.Sheaf.pushforward (Type v) (coefficientSpectrumMap φ)).obj
      ((TopCat.Sheaf.pushforward (Type v) (coefficientSpectrumMap ψ)).obj
        (rationalHomTypeSheaf F (M.map (ψ.comp φ)) (N.map (ψ.comp φ))))) z
  intro V i z' hz
  change ofRational V z' = restrict i z at hz
  let k := (coefficientOpenMap ψ).map ((coefficientOpenMap φ).map i)
  let eU := eqToHom (coefficientOpenMap_comp_obj φ ψ U)
  let eV := eqToHom (coefficientOpenMap_comp_obj φ ψ V)
  let l := (coefficientOpenMap (ψ.comp φ)).map i
  change restrict k (transportIso (F := F) (M := (M.map φ).map ψ) (N := (N.map φ).map ψ)
      (M' := M.map (ψ.comp φ)) (N' := N.map (ψ.comp φ))
      (mapCompIso M φ ψ) (mapCompIso N φ ψ) _
      (baseChange (M := M.map φ) (N := N.map φ) (F := F) ψ ((coefficientOpenMap φ).obj U) (baseChange (M := M) (N := N) (F := F) φ U z))) = restrict k (restrict eU (baseChange (M := M) (N := N) (F := F) (ψ.comp φ) U z))
  rw [restrict_transportIso, restrict_baseChange, restrict_baseChange]
  have hi : k ≫ eU = eV ≫ l := Subsingleton.elim _ _
  rw [← restrict_comp, hi, restrict_comp, restrict_baseChange, ← hz]
  exact baseChange_composite_representative φ ψ V z'

end RationalSection
end Langlands.FormalGroup.ModuleLaw
