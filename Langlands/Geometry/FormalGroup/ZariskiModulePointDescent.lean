import Langlands.Geometry.FormalGroup.ZariskiPointDescent
import Langlands.Geometry.FormalGroup.ZariskiDescent

/-! # Principal-open descent of actual formal O-module points -/

noncomputable section

universe u v w x

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {T : Type x} [CommRing T] [Algebra O T]
variable {σ κ : Type} [Finite σ]

variable (M : ModuleLaw O R σ)

/-- An actual coefficient triangle induces a linear map on series-valued points. -/
def mapPointsAlong (φ : R →ₐ[O] S) (ψ : R →ₐ[O] T) (f : S →+* T)
    (hf : f.comp φ.toRingHom = ψ.toRingHom) :
    (M.map φ).Point κ →ₗ[O] (M.map ψ).Point κ where
  toFun := SeriesPoint.map f
  map_add' a b := by
    change SeriesPoint S σ κ at a b
    change (SeriesPoint.eval (M.groupLaw.addition.map φ.toRingHom) (a.pair b)).map f =
      SeriesPoint.eval (M.groupLaw.addition.map ψ.toRingHom) ((a.map f).pair (b.map f))
    rw [SeriesPoint.map_eval, SeriesPoint.map_pair, CoordinateMap.map_ringHom_comp, hf]
  map_smul' c a := by
    change SeriesPoint S σ κ at a
    change (SeriesPoint.eval ((M.action c).toCoordinateMap.map φ.toRingHom) a).map f =
      SeriesPoint.eval ((M.action c).toCoordinateMap.map ψ.toRingHom) (a.map f)
    rw [SeriesPoint.map_eval, CoordinateMap.map_ringHom_comp, hf]

@[simp]
theorem mapPointsAlong_apply (φ : R →ₐ[O] S) (ψ : R →ₐ[O] T) (f : S →+* T)
    (hf : f.comp φ.toRingHom = ψ.toRingHom) (a : (M.map φ).Point κ) :
    M.mapPointsAlong φ ψ f hf a = SeriesPoint.map f a := rfl

/-- Restriction from the left principal localization to its pairwise overlap. -/
def basicOverlapLeft (a b : R) :
    (M.map (basicCoefficientMap a)).Point κ →ₗ[O]
      (M.map (basicCoefficientMap (a * b))).Point κ :=
  M.mapPointsAlong (basicCoefficientMap a) (basicCoefficientMap (a * b))
    (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away a) (P := Localization.Away (a * b)) a b)
    (RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b))

/-- Restriction from the right principal localization to the same overlap. -/
def basicOverlapRight (a b : R) :
    (M.map (basicCoefficientMap b)).Point κ →ₗ[O]
      (M.map (basicCoefficientMap (a * b))).Point κ :=
  M.mapPointsAlong (basicCoefficientMap b) (basicCoefficientMap (a * b))
    (IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away b) (P := Localization.Away (a * b)) b a)
    (RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a))

/-- The actual product of localized formal-module point carriers. -/
abbrev BasicPointFamily (s : Set R) :=
  (a : s) → (M.map (basicCoefficientMap a.val)).Point κ

/-- Matching tuples form a submodule for the actual localized formal laws. -/
def basicPointSubmodule (s : Set R) : Submodule O (M.BasicPointFamily (κ := κ) s) where
  carrier := SeriesPoint.BasicCompatible s
  zero_mem' := by
    intro a b
    change M.basicOverlapLeft a.val b.val 0 = M.basicOverlapRight a.val b.val 0
    rw [map_zero, map_zero]
  add_mem' := by
    intro z w hz hw a b
    change M.basicOverlapLeft a.val b.val (z a + w a) =
      M.basicOverlapRight a.val b.val (z b + w b)
    rw [map_add, map_add]
    specialize hz a b
    specialize hw a b
    change M.basicOverlapLeft a.val b.val (z a) =
      M.basicOverlapRight a.val b.val (z b) at hz
    change M.basicOverlapLeft a.val b.val (w a) =
      M.basicOverlapRight a.val b.val (w b) at hw
    rw [hz, hw]
  smul_mem' := by
    intro c z hz a b
    change M.basicOverlapLeft a.val b.val (c • z a) =
      M.basicOverlapRight a.val b.val (c • z b)
    rw [map_smul, map_smul]
    specialize hz a b
    change M.basicOverlapLeft a.val b.val (z a) =
      M.basicOverlapRight a.val b.val (z b) at hz
    rw [hz]

/-- Matching actual local points with their formal O-module structure. -/
abbrev MatchingBasicPoint (s : Set R) := M.basicPointSubmodule (κ := κ) s

/-- Restrict an actual global formal-module point to every member of a basic cover. -/
def toBasicPoints (s : Set R) : M.Point κ →ₗ[O] M.MatchingBasicPoint (κ := κ) s where
  toFun z := ⟨fun a => M.mapPoints (basicCoefficientMap a.val) z,
    SeriesPoint.basicCompatible_map s z⟩
  map_add' z w := by
    apply Subtype.ext
    funext a
    exact (M.mapPoints (basicCoefficientMap a.val)).map_add z w
  map_smul' c z := by
    apply Subtype.ext
    funext a
    exact (M.mapPoints (basicCoefficientMap a.val)).map_smul c z

/-- Actual formal O-module points glue uniquely and O-linearly on a basic cover. -/
def basicPointEquiv (s : Set R) (hs : Ideal.span s = ⊤) :
    M.Point κ ≃ₗ[O] M.MatchingBasicPoint (κ := κ) s where
  __ := M.toBasicPoints s
  invFun z := SeriesPoint.glueBasic s hs z.val z.property
  left_inv z := by
    apply SeriesPoint.ext_basic s hs
    intro a
    exact SeriesPoint.glueBasic_map s hs _ _ a
  right_inv z := by
    apply Subtype.ext
    funext a
    exact SeriesPoint.glueBasic_map s hs z.val z.property a

@[simp]
theorem basicPointEquiv_apply (s : Set R) (hs : Ideal.span s = ⊤)
    (z : M.Point κ) (a : s) :
    (M.basicPointEquiv s hs z).val a =
      SeriesPoint.map (algebraMap R (Localization.Away a.val)) z := rfl

/-- The constructed inverse has the prescribed actual localized tuples. -/
@[simp]
theorem basicPointEquiv_symm_map (s : Set R) (hs : Ideal.span s = ⊤)
    (z : M.MatchingBasicPoint (κ := κ) s) (a : s) :
    M.mapPoints (basicCoefficientMap a.val) ((M.basicPointEquiv s hs).symm z) =
      z.val a :=
  SeriesPoint.glueBasic_map s hs z.val z.property a

end Langlands.FormalGroup.ModuleLaw
