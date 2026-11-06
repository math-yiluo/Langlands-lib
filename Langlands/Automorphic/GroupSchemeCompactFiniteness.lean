import Langlands.Automorphic.GroupSchemeForms
import Langlands.Representation.Compact.Definitions

/-! # Full compact-subgroup finiteness on the original finite-smooth carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  (C : OpenSubgroup (FiniteAdelicGroupPoints F G))

local instance compactFinitenessAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The original finite-smooth carrier is a smooth representation of the finite factor. -/
theorem finitePlotSmoothFiniteRightAction_isSmooth :
    Langlands.IsSmooth (finitePlotSmoothFiniteRightAction F G) := by
  intro f
  obtain ⟨L, hL⟩ := f.property.2
  refine ⟨L, fun l => ?_⟩
  apply Subtype.ext
  exact hL l

/-- The direct product acts through the actual infinite/finite point decomposition. -/
def finitePlotSmoothCompactProductAction :
    Representation ℂ (Kinf × C) (FinitePlotSmoothRationalFunctions F G) :=
  (finitePlotSmoothRightAction F G).comp
    ((AdelicGroupPoints.split F G).symm.toMonoidHom.comp
      (Kinf.subtype.prodMap C.toSubgroup.subtype))

/-- The actual subgroup Kinf*C of the full adelic point group. -/
def adelicCompactProductSubgroup : Subgroup (AdelicGroupPoints F G) :=
  (Kinf.prod C.toSubgroup).map (AdelicGroupPoints.split F G).symm.toMonoidHom

/-- Compactness is proved by the actual continuous product map. -/
theorem isCompact_adelicCompactProductSubgroup
    (hK : IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G)))
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G))) :
    IsCompact (adelicCompactProductSubgroup F G Kinf C : Set (AdelicGroupPoints F G)) := by
  rw [adelicCompactProductSubgroup, Subgroup.coe_map, Subgroup.coe_prod]
  exact (hK.prod hC).image (AdelicGroupPoints.split F G).symm.continuous

/-- On this original finite-smooth carrier, a compact open finite factor adds no finiteness condition. -/
theorem isAdelicInfiniteFinite_iff_compactProduct (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : FinitePlotSmoothRationalFunctions F G) :
    IsAdelicInfiniteFinite F G Kinf f ↔
      Langlands.FiniteVectors.IsFiniteVector (finitePlotSmoothCompactProductAction F G Kinf C) f := by
  let infAction := finitePlotSmoothInfiniteSubgroupAction F G Kinf
  let finAction := (finitePlotSmoothFiniteRightAction F G).comp C.toSubgroup.subtype
  let prodAction := finitePlotSmoothCompactProductAction F G Kinf C
  constructor
  · intro hf
    let : Finite (Langlands.Compact.orbit finAction f) :=
      Langlands.Compact.finite_orbit_of_smooth (finitePlotSmoothFiniteRightAction F G)
        (finitePlotSmoothFiniteRightAction_isSmooth F G) C hC f
    let S := ⨆ w : Langlands.Compact.orbit finAction f,
      Langlands.FiniteVectors.orbitSpan infAction w.val
    have hfinite (w : Langlands.Compact.orbit finAction f) :
        Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan infAction w.val) := by
      obtain ⟨c, hc⟩ := w.property
      rw [← hc]
      exact hf.finiteRightAction F G Kinf c.val
    let : ∀ w : Langlands.Compact.orbit finAction f,
      Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan infAction w.val) := hfinite
    let : Module.Finite ℂ S := inferInstance
    change Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan prodAction f)
    apply Submodule.finiteDimensional_of_le (S₂ := S)
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, c⟩, rfl⟩
    let w : Langlands.Compact.orbit finAction f := ⟨finAction c f, ⟨c, rfl⟩⟩
    have hw : infAction k w.val ∈ S := Submodule.mem_iSup_of_mem w
      (Langlands.FiniteVectors.action_mem_orbitSpan infAction k w.val)
    have haction : prodAction (k, c) f = infAction k w.val := by
      change finitePlotSmoothRightAction F G (AdelicGroupPoints.pair F G k.val c.val) f =
        finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G k.val)
          (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c.val) f)
      rw [← Module.End.mul_apply, ← map_mul]
      simp only [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.ofFinite_eq_pair,
        AdelicGroupPoints.pair_mul, mul_one, one_mul]
    change prodAction (k, c) f ∈ S
    rw [haction]
    exact hw
  · intro hf
    let : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan prodAction f) := hf
    change Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan infAction f)
    apply Submodule.finiteDimensional_of_le
      (S₂ := Langlands.FiniteVectors.orbitSpan prodAction f)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hmem := Langlands.FiniteVectors.action_mem_orbitSpan prodAction (k, 1) f
    change finitePlotSmoothRightAction F G (AdelicGroupPoints.pair F G k.val 1) f ∈ _ at hmem
    exact hmem

/-- Restriction to the actual full compact subgroup, not a replacement product model. -/
def finitePlotSmoothActualCompactAction :
    Representation ℂ (adelicCompactProductSubgroup F G Kinf C)
      (FinitePlotSmoothRationalFunctions F G) :=
  (finitePlotSmoothRightAction F G).comp (adelicCompactProductSubgroup F G Kinf C).subtype

/-- The actual full compact subgroup and its product parametrization have identical orbits. -/
theorem compactProductOrbit_eq_actualCompactOrbit (f : FinitePlotSmoothRationalFunctions F G) :
    Set.range (fun k => finitePlotSmoothCompactProductAction F G Kinf C k f) =
      Set.range (fun k => finitePlotSmoothActualCompactAction F G Kinf C k f) := by
  ext w
  constructor
  · rintro ⟨⟨k, c⟩, rfl⟩
    exact ⟨⟨AdelicGroupPoints.pair F G k.val c.val, ⟨(k.val, c.val),
      ⟨k.property, c.property⟩, rfl⟩⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨p, hp, hpk⟩ := k.property
    refine ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), ?_⟩
    change finitePlotSmoothRightAction F G ((AdelicGroupPoints.split F G).symm p) f =
      finitePlotSmoothRightAction F G k.val f
    change (AdelicGroupPoints.split F G).symm p = k.val at hpk
    rw [hpk]

/-- Exact source Kinf*Kf-finiteness for every compact open finite subgroup. -/
theorem isAdelicInfiniteFinite_iff_actualCompactFinite
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : FinitePlotSmoothRationalFunctions F G) :
    IsAdelicInfiniteFinite F G Kinf f ↔
      Langlands.FiniteVectors.IsFiniteVector (finitePlotSmoothActualCompactAction F G Kinf C) f := by
  rw [isAdelicInfiniteFinite_iff_compactProduct F G Kinf C hC]
  unfold Langlands.FiniteVectors.IsFiniteVector Langlands.FiniteVectors.orbitSpan
  rw [compactProductOrbit_eq_actualCompactOrbit]

end Langlands.Automorphic.GroupSchemeFunctions
