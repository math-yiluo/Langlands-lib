import Langlands.Global.AdelicGroupNormOne
import Mathlib.Topology.Order.Compact

/-! # Functoriality and compact subgroups of actual norm-one adelic points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global

/-- A continuous positive-real-valued character is trivial on every compact subgroup. -/
theorem continuousMonoidHom_eq_one_on_compactSubgroup
    {H : Type v} [Group H] [TopologicalSpace H]
    (φ : H →ₜ* ℝ≥0ˣ) (K : Subgroup H) (hK : IsCompact (K : Set H))
    {x : H} (hx : x ∈ K) : φ x = 1 := by
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨1, K.one_mem⟩
    (Units.continuous_val.comp φ.continuous).continuousOn
  have hbound : ∀ z ∈ K, (φ z : ℝ≥0) ≤ (φ y : ℝ≥0) := fun z hz => hmax hz
  have hsq : (φ y : ℝ≥0) * (φ y : ℝ≥0) ≤ (φ y : ℝ≥0) := by
    simpa only [map_mul, Units.val_mul] using hbound (y * y) (K.mul_mem hy hy)
  have hyone : (φ y : ℝ≥0) ≤ 1 :=
    (mul_le_iff_le_one_left (pos_iff_ne_zero.mpr (φ y).ne_zero)).mp hsq
  have hle : ∀ z ∈ K, φ z ≤ 1 := fun z hz => (hbound z hz).trans hyone
  apply le_antisymm (hle x hx)
  have hinv : (φ x)⁻¹ ≤ 1 := by simpa only [map_inv] using hle x⁻¹ (K.inv_mem hx)
  exact inv_le_one'.mp hinv

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G H : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual continuous adelic-point map induced by a group-scheme homomorphism. -/
def map (f : G ⟶ H) : AdelicGroupPoints F G →ₜ* AdelicGroupPoints F H where
  toMonoidHom := G.affinePointsTarget f (CommAlgCat.of F (AdeleRing (𝓞 F) F))
  continuous_toFun := G.continuous_affinePointsTarget _ f

@[simp] theorem map_apply (f : G ⟶ H) (x : AdelicGroupPoints F G) :
    map F G H f x = G.affinePointsTarget f (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x := rfl

omit [NumberField F] in
/-- Pulling an actual character back along a group morphism agrees with point evaluation. -/
theorem characterUnits_comp (f : G ⟶ H) (χ : AlgebraicCharacter F H)
    (A : CommAlgCat.{u} (CommRingCat.of F)) (x : G.affinePoints A) :
    characterUnits F G (f ≫ χ) A x =
      characterUnits F H χ A (G.affinePointsTarget f A x) := by
  unfold characterUnits
  simp only [MonoidHom.comp_apply, GroupScheme.affinePointsTarget_apply]
  congr 1

/-- The normalized idele norm respects pullback of actual rational characters. -/
theorem characterNorm_comp (f : G ⟶ H) (χ : AlgebraicCharacter F H)
    (x : AdelicGroupPoints F G) :
    characterNorm F G (f ≫ χ) x = characterNorm F H χ (map F G H f x) := by
  change IdeleAbsoluteValue.full F (characterUnits F G (f ≫ χ) _ x) =
    IdeleAbsoluteValue.full F (characterUnits F H χ _ (G.affinePointsTarget f _ x))
  rw [characterUnits_comp]

/-- Every actual group-scheme morphism sends norm-one points to norm-one points. -/
theorem map_normOneSubgroup_le (f : G ⟶ H) :
    (normOneSubgroup F G).map (map F G H f).toMonoidHom ≤ normOneSubgroup F H := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_normOneSubgroup F H _).mpr
  intro χ
  exact (characterNorm_comp F G H f χ x).symm.trans
    ((mem_normOneSubgroup F G x).mp hx (f ≫ χ))

/-- The induced continuous homomorphism on the actual norm-one adelic subgroups. -/
def mapNormOne (f : G ⟶ H) : normOneSubgroup F G →ₜ* normOneSubgroup F H where
  toMonoidHom :=
    { toFun := fun x => ⟨map F G H f x,
        map_normOneSubgroup_le F G H f ⟨x, x.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one (map F G H f))
      map_mul' x y := Subtype.ext (map_mul (map F G H f) (x : AdelicGroupPoints F G) (y : AdelicGroupPoints F G)) }
  continuous_toFun := ((map F G H f).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem mapNormOne_val (f : G ⟶ H) (x : normOneSubgroup F G) :
    (mapNormOne F G H f x : AdelicGroupPoints F H) = map F G H f x := rfl

/-- The induced norm-one map commutes with actual principal rational points. -/
theorem mapNormOne_rationalNormOne (f : G ⟶ H) (x : RationalGroupPoints F G) :
    mapNormOne F G H f (rationalNormOne F G x) =
      rationalNormOne F H (G.affinePointsTarget f (CommAlgCat.of F F) x) := by
  apply Subtype.ext
  exact (DFunLike.congr_fun (rational_naturality F G f) x).symm

/-- Every compact subgroup of actual adelic points lies in the actual norm-one subgroup. -/
theorem compactSubgroup_le_normOneSubgroup (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) : K ≤ normOneSubgroup F G := by
  intro x hx
  exact (mem_normOneSubgroup F G x).mpr fun χ =>
    continuousMonoidHom_eq_one_on_compactSubgroup (characterNorm F G χ) K hK hx

end AdelicGroupPoints

end Langlands.Global
