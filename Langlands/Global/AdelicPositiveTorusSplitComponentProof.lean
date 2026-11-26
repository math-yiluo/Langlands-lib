import Langlands.Global.AdelicPositiveTorusSplitComponentStatement
import Langlands.Global.PositiveRealTorusLog
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof

/-! # Positive torus points killed by a set of simple roots lie in the split component

Proof of `PositiveTorusSplitComponentStatement`. The normalized logarithm identifies the
intrinsic positive subgroup of a split torus with the real dual of its character group; the
perfect pairing between real characters and real cocharacters identifies that dual with the
real cocharacter space. The real cocharacters of the split component `A_J` of the standard
Levi `M_J` map onto the annihilator of `J` (`standardLeviCentralDirections`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

namespace PositiveRealTorus

variable {F : Type u} [Field F]

/-- The real functional `χ ↦ ⟨χ, v⟩` on characters defined by a real cocharacter `v`. -/
def cocharacterFunctional {T : CommGroupScheme (Spec (CommRingCat.of F))} (v : V T) :
    RealCharacterDual F T.toGrp where
  toFun χ := pair T (1 ⊗ₜ[ℤ] χ) v
  map_zero' := by simp
  map_add' χ ψ := by simp [TensorProduct.tmul_add]

theorem cocharacterFunctional_apply {T : CommGroupScheme (Spec (CommRingCat.of F))} (v : V T)
    (χ : characterLattice T) : cocharacterFunctional v χ = pair T (1 ⊗ₜ[ℤ] χ) v := rfl

/-- The functional of a postcomposed real cocharacter is the restriction of the functional. -/
theorem cocharacterFunctional_cocharacterMapReal
    {A T : CommGroupScheme (Spec (CommRingCat.of F))} (f : A ⟶ T) (w : V A) :
    cocharacterFunctional (cocharacterMapReal f w) =
      realCharacterDualMap F A.toGrp T.toGrp (CommGroupScheme.groupHom f)
        (cocharacterFunctional w) := by
  apply AddMonoidHom.ext
  intro χ
  change pair T (1 ⊗ₜ[ℤ] χ) (cocharacterMapReal f w) =
    pair A (1 ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) χ) w
  rw [pair_cocharacterMapReal]
  rfl

/-- On a split torus every real functional on characters is the functional of a real
cocharacter (perfectness of the real pairing). -/
theorem exists_cocharacterFunctional_eq {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (hT : IsSplitTorus T.toGrp) (ℓ : RealCharacterDual F T.toGrp) :
    ∃ v : V T, cocharacterFunctional v = ℓ := by
  let := isPerfPair_of_isSplitTorus hT
  let φ : Vstar T →ₗ[ℝ] ℝ :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton ℝ (characterLattice T →ₗ[ℤ] ℝ)
        (ℓ : characterLattice T →+ ℝ).toIntLinearMap)
  obtain ⟨v, hv⟩ := (LinearMap.IsPerfPair.bijective_right (pair T)).2 φ
  refine ⟨v, ?_⟩
  apply AddMonoidHom.ext
  intro χ
  change pair T (1 ⊗ₜ[ℤ] χ) v = ℓ χ
  have h := LinearMap.congr_fun hv (1 ⊗ₜ[ℤ] χ)
  rw [LinearMap.flip_apply] at h
  rw [h]
  simp [φ]
  rfl

variable [NumberField F]

/-- A positive point of a split torus is determined by its normalized logarithm. -/
theorem eq_of_characterLog_eq {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (hT : IsSplitTorus T.toGrp) {x y : AdelicGroupPoints F T.toGrp}
    (hx : x ∈ intrinsicSubgroup F T) (hy : y ∈ intrinsicSubgroup F T)
    (h : characterLog F T.toGrp x = characterLog F T.toGrp y) : x = y := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  have := (positiveLogEquiv F T I e).injective
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (congrArg Multiplicative.ofAdd h)
  exact congrArg Subtype.val this

/-- Every real functional on characters is the normalized logarithm of a positive point. -/
theorem exists_characterLog_eq {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (hT : IsSplitTorus T.toGrp) (ℓ : RealCharacterDual F T.toGrp) :
    ∃ x ∈ intrinsicSubgroup F T, characterLog F T.toGrp x = ℓ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  refine ⟨((positiveLogEquiv F T I e).symm (Multiplicative.ofAdd ℓ)).val,
    ((positiveLogEquiv F T I e).symm (Multiplicative.ofAdd ℓ)).property, ?_⟩
  have := (positiveLogEquiv F T I e).apply_symm_apply (Multiplicative.ofAdd ℓ)
  exact congrArg Multiplicative.toAdd this

/-- Let `f : A → T` be a map of split tori whose real cocharacter image is the annihilator of
a set `R` of characters of `T`. A positive point of `T` on which every character in `R` takes
the value `1` is the image of a positive point of `A`. -/
theorem exists_intrinsic_map_eq_of_range_eq_rootAnnihilator
    {A T : CommGroupScheme (Spec (CommRingCat.of F))}
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    (R : Set (characterLattice T)) (hrange : (cocharacterMapReal f).range = rootAnnihilator T R)
    {t : AdelicGroupPoints F T.toGrp} (ht : t ∈ intrinsicSubgroup F T)
    (hR : ∀ β ∈ R, Lie.characterValue β t = 1) :
    ∃ a' ∈ intrinsicSubgroup F A,
      map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a' = t := by
  obtain ⟨v, hv⟩ := exists_cocharacterFunctional_eq hT (characterLog F T.toGrp t)
  have hmem : v ∈ rootAnnihilator T R := by
    rw [mem_rootAnnihilator]
    intro β hβ
    rw [eval_eq_pair, ← cocharacterFunctional_apply, hv, characterLog_eq_log_characterValue,
      hR β hβ, map_one]
    simp
  rw [← hrange] at hmem
  obtain ⟨w, rfl⟩ := hmem
  obtain ⟨a', ha', hlog⟩ := exists_characterLog_eq hA (cocharacterFunctional w)
  refine ⟨a', ha', ?_⟩
  apply eq_of_characterLog_eq hT _ ht
  · rw [characterLog_map, hlog, ← cocharacterFunctional_cocharacterMapReal, hv]
  · exact map_intrinsicSubgroup_le F A T f ⟨a', ha', rfl⟩

end PositiveRealTorus

open PositiveRealTorus in
/-- Bernstein–Lapid §7.2: a positive point of the maximal split torus on which the simple roots
in `J` are trivial is, in `G(𝔸)`, a point of the positive split component of `P_J`. -/
theorem positiveTorusSplitComponent : PositiveTorusSplitComponentStatement.{u} := by
  intro F _ _ G _ _ _ 𝓕 J t ht hJ
  have hc := 𝓕.isCompatible J
  have : IsAffineHom (𝓕.M J).X.hom := hc.levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup (𝓕.l J ≫ 𝓕.p J) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  let : IsClosedImmersion (𝓕.l J ≫ 𝓕.p J).hom.hom.left := hjc
  have hrep : (standardLevi 𝓕.i 𝓕.ν J.1).IsRepresentedBy (𝓕.l J ≫ 𝓕.p J) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  obtain ⟨_, f, hf, _, _, hrange, _⟩ :=
    (standardLeviCentralDirections.2 F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit 𝓕.ν
      𝓕.generic J.1 J.2 (𝓕.M J) (𝓕.l J ≫ 𝓕.p J) hjc hrep).2 (𝓕.A J) (𝓕.a J)
      hc.splitComponent
  have hA : IsSplitTorus (𝓕.A J).toGrp := hc.splitComponent.1.1.1
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  obtain ⟨a', ha', hmap⟩ :=
    exists_intrinsic_map_eq_of_range_eq_rootAnnihilator hA hT f J.1 hrange ht hJ
  refine ⟨pointMap F (𝓕.A J).toGrp (𝓕.P J) (Adeles F) (𝓕.a J ≫ 𝓕.l J) a', ⟨a', ha', rfl⟩, ?_⟩
  rw [← hmap]
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, pointMap_apply]
  rw [Category.assoc, Category.assoc]
  congr 1
  have h := congrArg (fun z : (𝓕.A J).toGrp ⟶ G => z.hom.hom) hf
  simpa [Category.assoc] using h.symm

end Langlands.Global
