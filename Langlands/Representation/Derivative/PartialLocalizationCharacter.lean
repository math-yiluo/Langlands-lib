import Langlands.Representation.Derivative.PartialLocalizationData
import Langlands.Representation.Derivative.MirabolicCharacter

/-! # Recursive matrix and character maps for partial localization -/

noncomputable section

namespace Langlands.Derivative.PartialLocalization

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF

variable {F : Type uF} [CommRing F] {k m : ℕ}

/-- Forget the redundant mirabolic certificate on the partial upper group. -/
def fromMirabolic : mirabolicPartialUpper k m F →* partialUpper k (m + 1) F :=
  ((mirabolic (k + m) F).subtype.comp (mirabolicPartialUpper k m F).subtype).codRestrict
    _ fun g => g.property

/-- The two actual subgroup realizations have identical underlying matrices. -/
def mirabolicEquiv : mirabolicPartialUpper k m F ≃* partialUpper k (m + 1) F where
  toFun := fromMirabolic
  invFun g := ⟨⟨g.val, partialUpper_le_mirabolic g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := fromMirabolic.map_mul

/-- Include the smaller partial group by the actual mirabolic Levi map. -/
def recursiveLevi : partialUpper k m F →* mirabolicPartialUpper k m F :=
  (levi.comp (partialUpper k m F).subtype).codRestrict _ levi_mem_partialUpper

/-- Extract the actual upper-left block, with its partial-group certificate. -/
def recursiveProjection : mirabolicPartialUpper k m F →* partialUpper k m F :=
  (projection.comp (mirabolicPartialUpper k m F).subtype).codRestrict _
    projection_mem_partialUpper

@[simp] theorem recursiveProjection_recursiveLevi (g : partialUpper k m F) :
    recursiveProjection (recursiveLevi g) = g :=
  Subtype.ext (projection_levi g.val)

/-- Include the actual final-column radical into the combined partial group. -/
def recursiveRadical : radical (k + m) F →* partialUpper k (m + 1) F :=
  fromMirabolic.comp (Subgroup.inclusion radical_le_partialUpper)

/-- The recursive Levi image is exactly the named smaller subgroup. -/
def partialLeviEquiv : partialUpper k m F ≃* partialLeviSubgroup k m F where
  toFun g := ⟨levi g.val, ⟨g.val, g.property, rfl⟩⟩
  invFun g := recursiveProjection ⟨g.val, partialLeviSubgroup_le_partialUpper g.property⟩
  left_inv g := recursiveProjection_recursiveLevi g
  right_inv g := by
    apply Subtype.ext
    obtain ⟨a, ha, he⟩ := g.property
    change levi (projection g.val) = g.val
    rw [← he, projection_levi]
  map_mul' g h := Subtype.ext (map_mul levi g.val h.val)

theorem partialLeviSubgroup_le_successor :
    partialLeviSubgroup k (m + 1) F ≤ successorSubgroup (k + m) F := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨g, partialUpper_le_mirabolic hg⟩, rfl⟩

/-- The recursive partial subgroup inside the actual successor mirabolic range. -/
def successorPartialSubgroup (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (successorSubgroup (k + m) F) :=
  (partialLeviSubgroup k (m + 1) F).subgroupOf (successorSubgroup (k + m) F)

/-- The canonical smaller-group copy used by character-localization towers. -/
def successorPartialEquiv :
    partialUpper k (m + 1) F ≃* successorPartialSubgroup k m F where
  toFun g := ⟨⟨levi g.val, partialLeviSubgroup_le_successor
    (show levi g.val ∈ partialLeviSubgroup k (m + 1) F from
      ⟨g.val, g.property, rfl⟩)⟩, ⟨g.val, g.property, rfl⟩⟩
  invFun g := partialLeviEquiv.symm ⟨g.val.val, g.property⟩
  left_inv g := partialLeviEquiv.left_inv g
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change levi (projection g.val.val) = g.val.val
    obtain ⟨a, ha, he⟩ := g.property
    change levi a = g.val.val at he
    rw [← he, projection_levi]
  map_mul' g h := Subtype.ext (Subtype.ext (map_mul levi g.val h.val))

theorem successorPartialSubgroup_map :
    (successorPartialSubgroup k m F).map (successorSubgroup (k + m) F).subtype =
      partialLeviSubgroup k (m + 1) F := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hg
    exact ⟨⟨g, partialLeviSubgroup_le_successor hg⟩, hg, rfl⟩

/-- Appending the final identity coordinate adds only a zero adjacent entry. -/
theorem finalSuperdiagonalSum_recursiveLevi (g : partialUpper k (m + 1) F) :
    (∑ i : Fin (m + 1),
      (fromMirabolic (recursiveLevi g)).val
        (i.castSucc.natAdd k) (i.succ.natAdd k)) =
      ∑ i : Fin m, g.val (i.castSucc.natAdd k) (i.succ.natAdd k) := by
  rw [Fin.sum_univ_castSucc]
  have hlast :
      (fromMirabolic (recursiveLevi g)).val
        ((Fin.last m).castSucc.natAdd k) ((Fin.last m).succ.natAdd k) = 0 := by
    change (levi g.val).val.val
      ((Fin.last m).castSucc.natAdd k) ((Fin.last m).succ.natAdd k) = 0
    have he : (Fin.last m).succ.natAdd k = Fin.last (k + (m + 1)) := by
      apply Fin.ext
      simp
    rw [he, Fin.natAdd_castSucc]
    exact levi_last g.val ((Fin.last m).natAdd k)
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  change (levi g.val).val.val
    (i.castSucc.castSucc.natAdd k) (i.castSucc.succ.natAdd k) = _
  simpa only [Fin.succ_castSucc, Fin.natAdd_castSucc] using
    levi_first g.val (i.castSucc.natAdd k) (i.succ.natAdd k)

/-- Exact character restriction along the actual recursive Levi map. -/
theorem character_recursiveLevi (ψ : AddChar F ℂ) :
    (character ψ k (m + 1)).comp (fromMirabolic.comp recursiveLevi) =
      character ψ k m := by
  cases m with
  | zero => simp [character]
  | succ m =>
    ext g
    change ψ (∑ i : Fin (m + 1),
      (fromMirabolic (recursiveLevi g)).val
        (i.castSucc.natAdd k) (i.succ.natAdd k)) =
      ψ (∑ i : Fin m, g.val (i.castSucc.natAdd k) (i.succ.natAdd k))
    rw [finalSuperdiagonalSum_recursiveLevi]

/-- On the last, Psi-minus step the final block has rank one and character one. -/
theorem character_recursiveRadical_one (ψ : AddChar F ℂ) :
    (character ψ k 1).comp (recursiveRadical (k := k) (m := 0)) = 1 := by
  simp [character]

/-- Only the last adjacent entry survives on the actual final-column radical. -/
theorem finalSuperdiagonalSum_recursiveRadical (u : radical (k + m + 1) F) :
    (∑ i : Fin (m + 1),
      (recursiveRadical (k := k) (m := m + 1) u).val
        (i.castSucc.natAdd k) (i.succ.natAdd k)) =
      radicalCoordinates u (Fin.last (k + m)) := by
  rw [Fin.sum_univ_castSucc]
  have hz : (∑ i : Fin m,
      (recursiveRadical (k := k) (m := m + 1) u).val
        (i.castSucc.castSucc.natAdd k) (i.castSucc.succ.natAdd k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change u.val.val.val
      (i.castSucc.castSucc.natAdd k) (i.castSucc.succ.natAdd k) = 0
    have hne : (i.castSucc.natAdd k).castSucc ≠ (i.succ.natAdd k).castSucc := by
      intro h
      have he := congrArg Fin.val h
      change k + i.val = k + (i.val + 1) at he
      omega
    have h := u.property ((i.castSucc.natAdd k).castSucc) (i.succ.natAdd k)
    rw [ite_eq_right hne] at h
    simpa only [Fin.succ_castSucc, Fin.natAdd_castSucc] using h
  rw [hz, zero_add]
  rfl

section Unitary

variable [TopologicalSpace F] (χ : UnitaryAdditiveCharacter F)

/-- The nonterminal recursive restriction is exactly the positive Phi-minus
character, with the same supplied additive character and no inverse. -/
theorem character_recursiveRadical_succ :
    (character χ.complex k (m + 2)).comp
      (recursiveRadical (k := k) (m := m + 1)) = Mirabolic.theta χ (k + m) := by
  ext u
  change χ.complex (∑ i : Fin (m + 1),
    (recursiveRadical (k := k) (m := m + 1) u).val
      (i.castSucc.natAdd k) (i.succ.natAdd k)) =
    χ.complex (radicalCoordinates u (Fin.last (k + m)))
  rw [finalSuperdiagonalSum_recursiveRadical]

end Unitary

section Topology

variable [TopologicalSpace F]

/-- The redundant mirabolic realization carries precisely the inherited topology. -/
def mirabolicContinuousEquiv :
    mirabolicPartialUpper k m F ≃ₜ* partialUpper k (m + 1) F where
  toMulEquiv := mirabolicEquiv
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun g : partialUpper k (m + 1) F =>
      (⟨⟨g.val, partialUpper_le_mirabolic g.property⟩, g.property⟩ :
        mirabolicPartialUpper k m F))
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The recursive Levi image and the smaller partial group have their actual topologies. -/
def partialLeviContinuousEquiv :
    partialUpper k m F ≃ₜ* partialLeviSubgroup k m F where
  toMulEquiv := partialLeviEquiv
  continuous_toFun := (continuous_levi.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_projection.comp continuous_subtype_val).subtype_mk _

/-- The second subgroup certificate also preserves the inherited topology. -/
def successorPartialContinuousEquiv :
    partialUpper k (m + 1) F ≃ₜ* successorPartialSubgroup k m F where
  toMulEquiv := successorPartialEquiv
  continuous_toFun := ((continuous_levi.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_projection.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

end Topology

end Langlands.Derivative.PartialLocalization
