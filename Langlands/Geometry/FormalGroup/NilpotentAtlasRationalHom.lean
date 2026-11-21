import Langlands.Geometry.FormalGroup.NilpotentFormalHom
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasRationalCoverDetection
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Flat.Localization

/-! # Nilpotent rigidity for rational formal atlas maps -/

noncomputable section

universe u v w q

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}
variable {π : O}

attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem eq_top_of_map_eq_top_of_nilpotent (S : CommAlgCat.{v} R)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (J : Ideal R) (hJ : J.map (algebraMap R S) = ⊤) : J = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hjm⟩ := Ideal.exists_le_maximal J hne
  have hk : RingHom.ker (algebraMap R S) ≤ m := by
    intro r hr
    obtain ⟨n, hn⟩ := hI
    apply hm.isPrime.mem_of_pow_mem n
    have hp := Ideal.pow_mem_pow hr n
    rw [show RingHom.ker (algebraMap R S) ^ n = ⊥ from hn, Ideal.mem_bot] at hp
    rw [hp]
    exact m.zero_mem
  exact (Ideal.IsMaximal.map_of_surjective_of_ker_le hS hk).ne_top
    (top_unique (hJ ▸ Ideal.map_mono hjm))

/-- The original chart generators selected by coefficient extension. -/
def baseSourceSubcover (Y : BasicAtlas O R τ) (S : CommAlgCat.{v} R) : Set R :=
  Set.range (fun b : Y.baseOpens S => (Y.baseSource S b).val)

theorem baseSourceSubcover_subset (Y : BasicAtlas O R τ) (S : CommAlgCat.{v} R) :
    Y.baseSourceSubcover S ⊆ Y.opens := by
  rintro _ ⟨b, rfl⟩
  exact (Y.baseSource S b).property

/-- Over a nilpotent thickening the selected original generators still cover the base. -/
theorem baseSourceSubcover_covers (Y : BasicAtlas O R τ) (S : CommAlgCat.{v} R)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) :
    Ideal.span (Y.baseSourceSubcover S) = ⊤ := by
  apply eq_top_of_map_eq_top_of_nilpotent S hS hI
  have himage : algebraMap R S '' Y.baseSourceSubcover S = Y.baseOpens S := by
    ext b
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact (Y.baseSource_image S c).symm ▸ c.property
    · intro hb
      exact ⟨(Y.baseSource S ⟨b, hb⟩).val, ⟨⟨b, hb⟩, rfl⟩, Y.baseSource_image S ⟨b, hb⟩⟩
  rw [Ideal.map_span, himage]
  exact Y.baseOpens_covers S

private def principalBaseComparison (Y : BasicAtlas O R τ) (S : CommAlgCat.{v} R)
    (b : Y.baseOpens S) :
    principalChartAlgebra (Y.baseSource S b).val ⟶
      restrictTest S (principalChartAlgebra (R := S) b.val) := by
  let T := principalChartAlgebra (R := S) b.val
  exact CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (Y.baseSource S b).val
    (f := Algebra.ofId R (restrictTest S T))
    (Y.baseSource_unit S T b (principalChartAlgebra_unit b.val)))

private theorem principalBaseComparison_nilpotent (Y : BasicAtlas O R τ) (S : CommAlgCat.{v} R)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S))) (b : Y.baseOpens S) :
    Function.Surjective (Y.principalBaseComparison S b).hom ∧
      IsNilpotent (RingHom.ker (Y.principalBaseComparison S b).hom.toRingHom) := by
  let a := (Y.baseSource S b).val
  let hm : Submonoid.map (algebraMap R S) (Submonoid.powers a) =
      Submonoid.powers b.val :=
    (Submonoid.map_powers _ _).trans (congrArg Submonoid.powers (Y.baseSource_image S b))
  let _ : IsLocalization (Submonoid.map (algebraMap R S) (Submonoid.powers a))
      (Localization.Away b.val) := hm.symm ▸ inferInstance
  let β := IsLocalization.map (Localization.Away b.val) (algebraMap R S)
    (Submonoid.powers a).le_comap_map (S := Localization.Away a)
  let w : Localization.Away a →+* Localization.Away b.val :=
    (Y.principalBaseComparison S b).hom.toRingHom
  have he : w = β := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    exact ((Y.principalBaseComparison S b).hom.commutes r).trans
      (IsLocalization.map_eq (S := Localization.Away a) (Q := Localization.Away b.val)
        (g := algebraMap R S)
        (Submonoid.powers a).le_comap_map r).symm
  change Function.Surjective w ∧ IsNilpotent (RingHom.ker w)
  rw [he]
  constructor
  · exact IsLocalization.map_surjective_of_surjective (Submonoid.powers a)
      (Localization.Away a) (Localization.Away b.val) hS
  · have hk : RingHom.ker β =
        (RingHom.ker (algebraMap R S)).map (algebraMap R (Localization.Away a)) :=
      IsLocalization.ker_map (S := Localization.Away a) (Localization.Away b.val)
        (algebraMap R S) hm
    rw [hk]
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    change _ = ⊥
    rw [← Ideal.map_pow, show RingHom.ker (algebraMap R S) ^ n = ⊥ from hn, Ideal.map_bot]

namespace Hom

set_option backward.isDefEq.respectTransparency false in
/-- Base change through a nilpotent quotient detects integral atlas maps. -/
theorem baseChange_injective_of_nilpotent (S : CommAlgCat.{v} R)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π) :
    Function.Injective (baseChangeLinear (X := X) (Y := Y) (h := h) S) := by
  intro f g he
  apply ext_onPrincipalSubcover (Y.baseSourceSubcover S) (Y.baseSourceSubcover_subset S)
    (Y.baseSourceSubcover_covers S hS hI)
  rintro ⟨_, b, rfl⟩
  let a := Y.baseSource S b
  let T := principalChartAlgebra (R := S) b.val
  let ha := principalChartAlgebra_unit a.val
  let hb := principalChartAlgebra_unit b.val
  let haT := Y.baseSource_unit S T b hb
  let w := Y.principalBaseComparison S b
  let wO := w.hom.restrictScalars O
  obtain ⟨hsurj, hker⟩ := Y.principalBaseComparison_nilpotent S hS hI b
  have hf := (hX (sourceChart h a)).map (coefficientLift (O := O) a.val _ ha)
  have hg := (hY a).map (coefficientLift (O := O) a.val _ ha)
  apply ModuleLaw.Hom.map_injective_of_nilpotent wO hsurj hker hf hg
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (f.hom _ a ha).toHom.toCoordinateMap.map w.hom.toRingHom =
    (g.hom _ a ha).toHom.toCoordinateMap.map w.hom.toRingHom
  rw [f.natural w a ha haT, g.natural w a ha haT]
  have he' := congrArg (fun k : Hom (X.baseChange S) (Y.baseChange S) (baseOpens_eq S h) =>
    (k.hom T b hb).toHom.toCoordinateMap) he
  simpa only [baseChangeLinear_apply, baseChange_coordinates] using he'

end Hom

variable {F : Type w} [Field F] [Algebra O F] [Module.Flat O F]

namespace RationalHom

/-- Scalar extension preserves integral detection across a nilpotent thickening. -/
theorem baseChange_injective_of_nilpotent (S : CommAlgCat.{v} R)
    (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π) :
    Function.Injective (baseChange (F := F) (X := X) (Y := Y) (h := h) S) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (Hom.baseChange_injective_of_nilpotent S hS hI hX hY)

variable {S : Type v} [CommRing S] [Algebra O S]

/-- Detection applies to the supplied target O-algebra structure. -/
theorem baseChangeAlong_injective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π) :
    Function.Injective (baseChangeAlong (F := F) (X := X) (Y := Y) (h := h) φ) :=
  (reAlgebra (F := F) _ (coefficientAlgebraAlong_eq φ)).injective.comp
    (baseChange_injective_of_nilpotent (coefficientTest φ) hφ hI hX hY)

end RationalHom

namespace OrderAction

variable {S : Type v} [CommRing S] [Algebra O S]
variable {D : Type q} [Ring D] [Algebra O D]
variable {E : OrderAction D X} {G : OrderAction D Y}

/-- A full-order rational atlas map is determined by its nilpotent reduction. -/
theorem RationalHom.baseChangeAlong_injective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π) :
    Function.Injective (baseChangeAlong (F := F) (E := E) (E' := G) (h := h) φ) := by
  intro f g he
  apply ext
  apply BasicAtlas.RationalHom.baseChangeAlong_injective_of_nilpotent φ hφ hI hX hY
  simpa only [baseChangeAlong_val] using congrArg Subtype.val he

omit [Module.Flat O F] in
/-- Two full-order atlas quasi-isogenies with the same nilpotent reduction coincide. -/
theorem QuasiIsogeny.baseChangeAlong_injective_of_nilpotent
    [IsDomain O] [IsFractionRing O F] (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hX : ∀ a : X.opens, (X.chart a).IsPiDivisible π)
    (hY : ∀ b : Y.opens, (Y.chart b).IsPiPowerTorsion π) :
    Function.Injective
      (fun f : QuasiIsogeny F E G h => f.baseChangeAlong φ) := by
  let _ := IsLocalization.flat F (nonZeroDivisors O)
  intro f g he
  apply ext_hom
  exact RationalHom.baseChangeAlong_injective_of_nilpotent φ hφ hI hX hY
    (congrArg QuasiIsogeny.hom he)

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
