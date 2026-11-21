import Langlands.Global.AdelicBlockCompactProjection
import Langlands.Global.AdelicBlockSmoothCompactSlices

/-! # The actual finite and infinite factors of the adelic compact model -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global

open PrimitiveAdelicHeight GeneralLinear

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "K" => standardCompact F n
local notation "K∞" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n

/-- The actual standard compact subgroup is the product of its infinite compact
and finite integral factors, with their original topologies. -/
def standardCompactProductEquiv : K ≃ₜ* K∞ × Kf where
  toFun k :=
    ⟨⟨AdelicGL.infinite F n k.val, ((mem_standardCompact_iff F n _).mp k.property).1⟩,
      ⟨AdelicGL.finite F n k.val, ((mem_standardCompact_iff F n _).mp k.property).2⟩⟩
  invFun k := AdelicBlockScalarSections.compactPair F k.1 k.2
  left_inv k := Subtype.ext (AdelicGL.pair_projections F n k.val)
  right_inv k := Prod.ext
    (Subtype.ext (AdelicGL.infinite_pair F n k.1.val k.2.val))
    (Subtype.ext (AdelicGL.finite_pair F n k.1.val k.2.val))
  map_mul' a b := Prod.ext
    (Subtype.ext ((AdelicGL.infinite F n).map_mul a.val b.val))
    (Subtype.ext ((AdelicGL.finite F n).map_mul a.val b.val))
  continuous_toFun :=
    (((AdelicGL.infinite F n).continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      (((AdelicGL.finite F n).continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((AdelicGL.continuous_pair F n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp]
theorem standardCompactProductEquiv_symm_val (k : K∞ × Kf) :
    ((standardCompactProductEquiv F n).symm k).val = AdelicGL.pair F n k.1.val k.2.val := rfl

namespace AdelicBlockParabolic

variable {n} (B : BlockShape n)

/-- The intersection in the archimedean parabolic, using the actual infinite compact factor. -/
def infiniteCompactIntersection : Subgroup (Infinite F B) :=
  (standardInfiniteCompact F n).comap (B.parabolic (InfiniteAdeles F)).subtype

/-- The intersection in the finite parabolic, using the actual integral subgroup. -/
def finiteCompactIntersection : Subgroup (Finite F B) :=
  (FiniteAdelicGL.standardIntegral F n).toSubgroup.comap (B.parabolic (FiniteAdeles F)).subtype

local notation "H" => compactIntersection B F
local notation "H∞" => infiniteCompactIntersection F B
local notation "Hf" => finiteCompactIntersection F B

private def splitCompactIntersection (p : H) : H∞ × Hf :=
  let hp := (mem_standardCompact_iff F n p.val.val).mp p.property
  ⟨⟨infinite F B p.val, hp.1⟩, ⟨finite F B p.val, hp.2⟩⟩

private def pairCompactIntersection (p : H∞ × Hf) : H :=
  ⟨pair F B p.1.val p.2.val, by
    change (AdelicGL.pair F n p.1.val.val p.2.val.val) ∈ standardCompact F n
    exact (AdelicBlockScalarSections.compactPair F ⟨p.1.val.val, p.1.property⟩
      ⟨p.2.val.val, p.2.property⟩).property⟩

/-- The full compact parabolic intersection splits into the two actual intersections. -/
def compactIntersectionProductEquiv : H ≃ₜ* H∞ × Hf where
  toFun := splitCompactIntersection F B
  invFun := pairCompactIntersection F B
  left_inv p := Subtype.ext (pair_projections F B p.val)
  right_inv p := Prod.ext
    (Subtype.ext (infinite_pair F B p.1.val p.2.val))
    (Subtype.ext (finite_pair F B p.1.val p.2.val))
  map_mul' p q := Prod.ext
    (Subtype.ext ((infinite F B).map_mul p.val q.val))
    (Subtype.ext ((finite F B).map_mul p.val q.val))
  continuous_toFun := by
    unfold splitCompactIntersection
    exact (((infinite F B).continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      (((finite F B).continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    unfold pairCompactIntersection
    exact ((continuous_pair F B).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp]
theorem compactIntersectionProductEquiv_symm_val (p : H∞ × Hf) :
    ((compactIntersectionProductEquiv F B).symm p).val = pair F B p.1.val p.2.val := rfl

/-- The compact parabolic inclusion commutes with the actual compact product coordinates. -/
theorem standardCompactProductEquiv_compactIntersection (p : H) :
    standardCompactProductEquiv F n ⟨p.val.val, p.property⟩ =
      let a := compactIntersectionProductEquiv F B p
      (⟨a.1.val.val, a.1.property⟩, ⟨a.2.val.val, a.2.property⟩) := rfl

end AdelicBlockParabolic

end Langlands.Global
