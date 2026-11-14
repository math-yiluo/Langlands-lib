import Langlands.Automorphic.PlaceComponentCarrier
import Langlands.Automorphic.PlaceComponentCarrierComplex

/-!
# Irreducible admissible components at a real place of a cuspidal realization

Let `T` be an actual cuspidal realization of `GL_{r+1}` and `v` a real place. This module
constructs a subspace of `T` that is irreducible for the place actions at `v` and admissible
for `O(r+1)` (`CuspidalOperatorRealization.exists_realPlaceComponent`).

Take a nonzero `f₀ ∈ T`, an open subgroup `U` fixing it, and the finite-dimensional
compact orbit span `E` of `f₀` in a basis. The carrier of linear maps `ℂ^m → T` with `U`-fixed
values that intertwine `E` with `T` away from `v` contains the inclusion of `E`, is stable under
post-composition with the place actions at `v`, and is admissible by joint admissibility. A
matrix representation of `O(r+1)` detecting the nonzero place-stable subspaces of `T` (by
irreducibility of `T`) detects those of the carrier, so the carrier contains an irreducible
admissible stable subspace. Its image under evaluation at a suitable basis vector is the
required subspace of `T`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance existenceRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance existenceContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance existenceSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance existenceFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance existenceStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance existenceSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- **Irreducible admissible components at a real place.** -/
theorem exists_realPlaceComponent (v : RP) :
    ∃ W : Submodule ℂ T.realization.Space,
      PlaceComponent.IsIrreducible (T.realization.realPlaceCompactRepresentation v)
          (T.realization.realPlaceLieAction v) W ∧
        PlaceComponent.IsAdmissible (T.realization.realPlaceCompactRepresentation v) W := by
  classical
  refine (T.realization.exists_realPlace_detection T.irreducible v).elim
    fun d₀ hd₀ => hd₀.elim fun τ₀ hτ₀ => ?_
  refine (exists_ne (0 : T.realization.Space)).elim fun f₀ hf₀ => ?_
  refine (T.realization.finiteRepresentation_isSmooth f₀).elim fun U hU => ?_
  -- the compact orbit span of `f₀`
  let E : Submodule ℂ T.realization.Space :=
    FiniteVectors.orbitSpan T.realization.compactRepresentation f₀
  have hEs : ∀ (k : standardInfiniteCompact F (r + 1)), ∀ y ∈ E,
      T.realization.compactRepresentation k y ∈ E := fun k _ hy =>
    (FiniteVectors.orbitSubrepresentation T.realization.compactRepresentation f₀
      ).apply_mem_toSubmodule k hy
  have hEfin : FiniteDimensional ℂ E := T.realization.compactRepresentation_isFiniteVector f₀
  have hEfix : E ≤ fixedVectors T.realization.finiteRepresentation U.toSubgroup := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    intro g
    exact (T.realization.finiteRepresentation_compactRepresentation g k f₀).trans
      (congrArg (T.realization.compactRepresentation k) (hU g))
  -- the representation of the compact factors on `ℂ^m`
  let b := Module.finBasis ℂ E
  let m := Module.finrank ℂ E
  let ρE := restrictRep T.realization.compactRepresentation E hEs
  let R : Representation ℂ (ArchimedeanCompactFactors F (r + 1)) (Fin m → ℂ) :=
    conjRep b.equivFun
      (ρE.comp (ArchimedeanCompactFactors.toStandardCompact F (r + 1)).toMonoidHom)
  let φ₀ : (Fin m → ℂ) →ₗ[ℂ] T.realization.Space := E.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hφ₀ : φ₀ ∈ T.realization.realCarrier v U.toSubgroup R :=
    ⟨fun x => hEfix (b.equivFun.symm x).2, fun q _ x =>
      congrArg E.subtype (b.equivFun.symm_apply_apply _)⟩
  have hφ₀0 : φ₀ ≠ 0 := by
    intro h
    apply hf₀
    have h1 : φ₀ (b.equivFun ⟨f₀, FiniteVectors.self_mem_orbitSpan _ f₀⟩) = f₀ :=
      congrArg E.subtype (b.equivFun.symm_apply_apply _)
    rw [h, LinearMap.zero_apply] at h1
    exact h1.symm
  -- the carrier and its irreducible admissible stable subspace
  have hJs := T.realization.isStable_realCarrier v U.toSubgroup R
  have hJa := T.realization.isAdmissible_realCarrier T.isJointlyAdmissible v U R
  have hJ0 : T.realization.realCarrier v U.toSubgroup R ≠ ⊥ := fun h =>
    hφ₀0 ((Submodule.mem_bot ℂ).mp ((congrArg (fun J => φ₀ ∈ J) h).mp hφ₀))
  refine (exists_isIrreducible_isAdmissible
    (postRep m (T.realization.realPlaceCompactRepresentation v))
    (postLie m (T.realization.realPlaceLieAction v)) hJs hJa hJ0 τ₀ hτ₀.1
    (fun N _ hNs hN0 => intertwiners_ne_bot_postRep m
      (T.realization.isLocallyFinite_realPlace v) (T.realization.isWeaklyContinuous_realPlace v)
      hτ₀.2 hNs hN0)).elim fun N₀ hN₀ => ?_
  have hirr := hN₀.2.1
  have hadm := hN₀.2.2
  refine (Submodule.exists_mem_ne_zero_of_ne_bot hirr.1).elim fun φ hφ => ?_
  have hex : ∃ j : Fin m, φ (Pi.single j 1) ≠ 0 := by
    by_contra h
    exact hφ.2 (eq_zero_of_single m φ fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  refine hex.elim fun j hj => ?_
  have hW0 : N₀.map (evalAt m (Pi.single j 1)) ≠ ⊥ := by
    intro h
    have hmem : φ (Pi.single j 1) ∈ N₀.map (evalAt m (Pi.single j 1)) := ⟨φ, hφ.1, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hj hmem
  have hinj := injOn_of_isIrreducible (κ' := T.realization.realPlaceCompactRepresentation v)
    (π' := T.realization.realPlaceLieAction v) (evalAt m (Pi.single j 1))
    (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0
  exact ⟨N₀.map (evalAt m (Pi.single j 1)),
    isIrreducible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0,
    isAdmissible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) hirr.2.1.1 hinj hadm⟩

/-- **Irreducible admissible components at a complex place.** -/
theorem exists_complexPlaceComponent (v : CP) :
    ∃ W : Submodule ℂ T.realization.Space,
      PlaceComponent.IsIrreducible (T.realization.complexPlaceCompactRepresentation v)
          (T.realization.complexPlaceLieAction v) W ∧
        PlaceComponent.IsAdmissible (T.realization.complexPlaceCompactRepresentation v) W := by
  classical
  refine (T.realization.exists_complexPlace_detection T.irreducible v).elim
    fun d₀ hd₀ => hd₀.elim fun τ₀ hτ₀ => ?_
  refine (exists_ne (0 : T.realization.Space)).elim fun f₀ hf₀ => ?_
  refine (T.realization.finiteRepresentation_isSmooth f₀).elim fun U hU => ?_
  -- the compact orbit span of `f₀`
  let E : Submodule ℂ T.realization.Space :=
    FiniteVectors.orbitSpan T.realization.compactRepresentation f₀
  have hEs : ∀ (k : standardInfiniteCompact F (r + 1)), ∀ y ∈ E,
      T.realization.compactRepresentation k y ∈ E := fun k _ hy =>
    (FiniteVectors.orbitSubrepresentation T.realization.compactRepresentation f₀
      ).apply_mem_toSubmodule k hy
  have hEfin : FiniteDimensional ℂ E := T.realization.compactRepresentation_isFiniteVector f₀
  have hEfix : E ≤ fixedVectors T.realization.finiteRepresentation U.toSubgroup := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    intro g
    exact (T.realization.finiteRepresentation_compactRepresentation g k f₀).trans
      (congrArg (T.realization.compactRepresentation k) (hU g))
  -- the representation of the compact factors on `ℂ^m`
  let b := Module.finBasis ℂ E
  let m := Module.finrank ℂ E
  let ρE := restrictRep T.realization.compactRepresentation E hEs
  let R : Representation ℂ (ArchimedeanCompactFactors F (r + 1)) (Fin m → ℂ) :=
    conjRep b.equivFun
      (ρE.comp (ArchimedeanCompactFactors.toStandardCompact F (r + 1)).toMonoidHom)
  let φ₀ : (Fin m → ℂ) →ₗ[ℂ] T.realization.Space := E.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hφ₀ : φ₀ ∈ T.realization.complexCarrier v U.toSubgroup R :=
    ⟨fun x => hEfix (b.equivFun.symm x).2, fun q _ x =>
      congrArg E.subtype (b.equivFun.symm_apply_apply _)⟩
  have hφ₀0 : φ₀ ≠ 0 := by
    intro h
    apply hf₀
    have h1 : φ₀ (b.equivFun ⟨f₀, FiniteVectors.self_mem_orbitSpan _ f₀⟩) = f₀ :=
      congrArg E.subtype (b.equivFun.symm_apply_apply _)
    rw [h, LinearMap.zero_apply] at h1
    exact h1.symm
  -- the carrier and its irreducible admissible stable subspace
  have hJs := T.realization.isStable_complexCarrier v U.toSubgroup R
  have hJa := T.realization.isAdmissible_complexCarrier T.isJointlyAdmissible v U R
  have hJ0 : T.realization.complexCarrier v U.toSubgroup R ≠ ⊥ := fun h =>
    hφ₀0 ((Submodule.mem_bot ℂ).mp ((congrArg (fun J => φ₀ ∈ J) h).mp hφ₀))
  refine (exists_isIrreducible_isAdmissible
    (postRep m (T.realization.complexPlaceCompactRepresentation v))
    (postLie m (T.realization.complexPlaceLieAction v)) hJs hJa hJ0 τ₀ hτ₀.1
    (fun N _ hNs hN0 => intertwiners_ne_bot_postRep m
      (T.realization.isLocallyFinite_complexPlace v) (T.realization.isWeaklyContinuous_complexPlace v)
      hτ₀.2 hNs hN0)).elim fun N₀ hN₀ => ?_
  have hirr := hN₀.2.1
  have hadm := hN₀.2.2
  refine (Submodule.exists_mem_ne_zero_of_ne_bot hirr.1).elim fun φ hφ => ?_
  have hex : ∃ j : Fin m, φ (Pi.single j 1) ≠ 0 := by
    by_contra h
    exact hφ.2 (eq_zero_of_single m φ fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  refine hex.elim fun j hj => ?_
  have hW0 : N₀.map (evalAt m (Pi.single j 1)) ≠ ⊥ := by
    intro h
    have hmem : φ (Pi.single j 1) ∈ N₀.map (evalAt m (Pi.single j 1)) := ⟨φ, hφ.1, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hj hmem
  have hinj := injOn_of_isIrreducible (κ' := T.realization.complexPlaceCompactRepresentation v)
    (π' := T.realization.complexPlaceLieAction v) (evalAt m (Pi.single j 1))
    (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0
  exact ⟨N₀.map (evalAt m (Pi.single j 1)),
    isIrreducible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) (fun _ _ => rfl) hirr hW0,
    isAdmissible_map (evalAt m (Pi.single j 1)) (fun _ _ => rfl) hirr.2.1.1 hinj hadm⟩

end CuspidalOperatorRealization

/-- **Proof of `CuspidalArchimedeanIrreducibleAdmissibleComponentStatement`.** Every actual
cuspidal realization has, at every infinite place, a subspace irreducible for the place actions
there and admissible for the compact group. -/
theorem cuspidalArchimedeanIrreducibleAdmissibleComponent :
    CuspidalArchimedeanIrreducibleAdmissibleComponentStatement.{u} := by
  intro F _ _ _ r T
  exact ⟨fun v => T.exists_realPlaceComponent v, fun v => T.exists_complexPlaceComponent v⟩

end Langlands.Automorphic
