import Langlands.Geometry.FormalGroup.CoefficientCoherence
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Zariski gluing of actual formal homomorphisms -/

noncomputable section

universe u v

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type v} [CommRing R]
variable {σ τ : Type}

namespace CoordinateMap

/-- Matching coordinate maps on the intersections D(a) ∩ D(b) = D(ab). -/
def BasicCompatible (s : Set R) (f : ∀ a : s, CoordinateMap (Localization.Away a.1) σ τ) :
    Prop :=
  ∀ a b : s,
    (f a).map (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away a.1) (P := Localization.Away (a.1 * b.1)) a.1 b.1) =
    (f b).map (IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away b.1) (P := Localization.Away (a.1 * b.1)) b.1 a.1)

/-- Coordinate equality can be checked on any basic-open cover of Spec R. -/
theorem ext_basic (s : Set R) (hs : Ideal.span s = ⊤) {f g : CoordinateMap R σ τ}
    (h : ∀ a : s, f.map (algebraMap R (Localization.Away a.1)) =
      g.map (algebraMap R (Localization.Away a.1))) : f = g := by
  apply CoordinateMap.ext
  funext i
  apply MvPowerSeries.ext
  intro d
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext a
  exact congrArg (fun k => coeff d (k.series i)) (h a)

/-- Glue one actual coefficient of a compatible family of coordinate maps. -/
def glueBasicCoefficient (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, CoordinateMap (Localization.Away a.1) σ τ)
    (hf : BasicCompatible s f) (i : τ) (d : σ →₀ ℕ) : R :=
  Classical.choose (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
    (fun a => coeff d ((f a).series i))
    (fun a b => congrArg (fun k => coeff d (k.series i)) (hf a b)))

/-- The glued coefficient restricts to each prescribed local coefficient. -/
theorem glueBasicCoefficient_spec (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, CoordinateMap (Localization.Away a.1) σ τ)
    (hf : BasicCompatible s f) (i : τ) (d : σ →₀ ℕ) (a : s) :
    algebraMap R (Localization.Away a.1) (glueBasicCoefficient s hs f hf i d) =
      coeff d ((f a).series i) :=
  (Classical.choose_spec
    (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
      (fun a => coeff d ((f a).series i))
      (fun a b => congrArg (fun k => coeff d (k.series i)) (hf a b)))).1 a

/-- Glue actual pointed power series coefficient by coefficient. -/
def glueBasic (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, CoordinateMap (Localization.Away a.1) σ τ)
    (hf : BasicCompatible s f) : CoordinateMap R σ τ where
  series i d := glueBasicCoefficient s hs f hf i d
  constantCoeff_eq_zero i := by
    apply Localization.algebraMap_injective_of_span_eq_top s hs
    funext a
    change algebraMap R (Localization.Away a.1) (glueBasicCoefficient s hs f hf i 0) =
      algebraMap R (Localization.Away a.1) 0
    rw [glueBasicCoefficient_spec, _root_.map_zero]
    exact (f a).constantCoeff_eq_zero i

/-- The glued pointed map restricts to the given local pointed map. -/
theorem glueBasic_map (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, CoordinateMap (Localization.Away a.1) σ τ)
    (hf : BasicCompatible s f) (a : s) :
    (glueBasic s hs f hf).map (algebraMap R (Localization.Away a.1)) = f a := by
  apply CoordinateMap.ext
  funext i
  apply MvPowerSeries.ext
  intro d
  exact glueBasicCoefficient_spec s hs f hf i d a

end CoordinateMap

namespace ModuleLaw

variable {O : Type u} [CommRing O] [Algebra O R]
variable [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- The canonical coefficient extension to the ring of a principal affine open. -/
def basicCoefficientMap (a : R) : R →ₐ[O] Localization.Away a :=
  IsScalarTower.toAlgHom O R (Localization.Away a)

namespace Hom

/-- Matching actual O-linear formal maps on a basic-open cover. -/
def BasicCompatible (s : Set R)
    (f : ∀ a : s, Hom (M.map (basicCoefficientMap a.1)) (N.map (basicCoefficientMap a.1))) :
    Prop :=
  CoordinateMap.BasicCompatible s (fun a => (f a).toHom.toCoordinateMap)

/-- Equality of actual formal O-linear maps is Zariski local. -/
theorem ext_basic (s : Set R) (hs : Ideal.span s = ⊤) {f g : Hom M N}
    (h : ∀ a : s, f.map (basicCoefficientMap a.1) = g.map (basicCoefficientMap a.1)) :
    f = g := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  apply CoordinateMap.ext_basic s hs
  intro a
  exact congrArg (fun k => k.toHom.toCoordinateMap) (h a)

/-- Glue actual O-linear formal homomorphisms on any principal-open cover. -/
def glueBasic (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, Hom (M.map (basicCoefficientMap a.1)) (N.map (basicCoefficientMap a.1)))
    (hf : BasicCompatible s f) : Hom M N where
  toHom := {
    toCoordinateMap := CoordinateMap.glueBasic s hs
      (fun a => (f a).toHom.toCoordinateMap) hf
    map_add := by
      apply CoordinateMap.ext_basic s hs
      intro a
      simp only [CoordinateMap.map_comp, CoordinateMap.map_pair,
        CoordinateMap.map_fst, CoordinateMap.map_snd]
      rw [CoordinateMap.glueBasic_map s hs (fun a => (f a).toHom.toCoordinateMap) hf a]
      exact (f a).toHom.map_add }
  commutes b := by
    apply CommLaw.Hom.ext
    apply CoordinateMap.ext_basic s hs
    intro a
    simp only [CommLaw.Hom.comp_toCoordinateMap, CoordinateMap.map_comp]
    rw [CoordinateMap.glueBasic_map s hs (fun a => (f a).toHom.toCoordinateMap) hf a]
    exact congrArg CommLaw.Hom.toCoordinateMap ((f a).commutes b)

/-- The glued O-linear formal homomorphism has the prescribed restrictions. -/
theorem glueBasic_map (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, Hom (M.map (basicCoefficientMap a.1)) (N.map (basicCoefficientMap a.1)))
    (hf : BasicCompatible s f) (a : s) :
    (glueBasic s hs f hf).map (basicCoefficientMap a.1) = f a := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  exact CoordinateMap.glueBasic_map s hs _ hf a

/-- The global homomorphism with these local restrictions is unique. -/
theorem glueBasic_unique (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ∀ a : s, Hom (M.map (basicCoefficientMap a.1)) (N.map (basicCoefficientMap a.1)))
    (hf : BasicCompatible s f) (g : Hom M N)
    (hg : ∀ a : s, g.map (basicCoefficientMap a.1) = f a) :
    g = glueBasic s hs f hf :=
  ext_basic s hs (fun a => (hg a).trans (glueBasic_map s hs f hf a).symm)

end Hom

end ModuleLaw

end Langlands.FormalGroup
