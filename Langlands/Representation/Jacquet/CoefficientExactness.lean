import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-! Exactness of the native character-one quotient over a complex algebra. -/

noncomputable section

namespace Langlands.Jacquet.Localization.Coefficient

universe uR uG uV uW uX

section Algebra

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {X : Type uX} [AddCommGroup X] [Module R X]

/-- A surjective native intertwiner maps the exact character relations onto
all target relations. -/
theorem relations_map_of_surjective {ρ : Representation R G V}
    {σ : Representation R G W} (U : Subgroup G) (θ : U →* Rˣ)
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) :
    (relations ρ U θ).map p.toLinearMap = relations σ U θ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change p (ρ u v - (θ u : R) • v) ∈ relations σ U θ
    rw [map_sub, map_smul, p.isIntertwining]
    exact sub_mem_relations σ U θ u (p v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨ρ u v - (θ u : R) • v, sub_mem_relations ρ U θ u v, ?_⟩
    change p (ρ u v - (θ u : R) • v) = _
    rw [map_sub, map_smul, p.isIntertwining]

/-- Native character quotients preserve surjections over every commutative ring. -/
theorem map_surjective {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) :
    Function.Surjective (map U θ M hMU hθ p) := by
  intro x
  obtain ⟨w, rfl⟩ := mk_surjective σ U θ x
  obtain ⟨v, rfl⟩ := hp w
  exact ⟨mk ρ U θ v, rfl⟩

/-- Algebraic middle exactness of the native character quotient. -/
theorem map_range_eq_ker {ρ : Representation R G V} {σ : Representation R G W}
    {τ : Representation R G X} (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ) (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (map U θ M hMU hθ i).toLinearMap =
      LinearMap.ker (map U θ M hMU hθ p).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := mk_surjective ρ U θ x
    have hpiv : p (i v) = 0 := by
      change i v ∈ LinearMap.ker p.toLinearMap
      rw [← hex]
      exact ⟨v, rfl⟩
    change mk τ U θ (p (i v)) = 0
    rw [hpiv, map_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := mk_surjective σ U θ x
    have hpw : p w ∈ relations τ U θ := (mk_eq_zero τ U θ _).mp hx
    rw [← relations_map_of_surjective U θ p hp] at hpw
    obtain ⟨z, hz, hpz⟩ := hpw
    change p z = p w at hpz
    have hwz : w - z ∈ LinearMap.range i.toLinearMap := by
      rw [hex]
      change p (w - z) = 0
      rw [map_sub, hpz, sub_self]
    obtain ⟨v, hv⟩ := hwz
    refine ⟨mk ρ U θ v, ?_⟩
    change mk σ U θ (i v) = mk σ U θ w
    change i v = w - z at hv
    rw [hv, map_sub, (mk_eq_zero σ U θ z).mpr hz, sub_zero]

end Algebra

section Complex

open Langlands.Jacquet.CoefficientRestriction

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
  {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V] [IsScalarTower ℂ R V]
  {W : Type uW} [AddCommGroup W] [Module R W] [Module ℂ W] [IsScalarTower ℂ R W]

/-- Scalar restriction of an actual native intertwiner changes no function. -/
def complexIntertwiner {ρ : Representation R G V} {σ : Representation R G W}
    (i : ρ.IntertwiningMap σ) :
    (complexRepresentation ρ).IntertwiningMap (complexRepresentation σ) where
  toLinearMap := i.toLinearMap.restrictScalars ℂ
  isIntertwining' g := by
    ext v
    exact i.isIntertwining ρ σ g v

/-- The native character-one relation set is precisely its complex counterpart. -/
theorem mem_relations_one_iff (ρ : Representation R G V) (U : Subgroup G) (v : V) :
    v ∈ relations ρ U (1 : U →* Rˣ) ↔
      v ∈ relations (complexRepresentation ρ) U (1 : U →* ℂˣ) := by
  rw [relations_one, relations_one]
  change v ∈ Jacquet.relations ρ U ↔
    v ∈ Jacquet.coefficientRelations R (complexRepresentation ρ) U
  rw [coefficientRelations_eq_native]

/-- Compact containment and smoothness give left exactness for the literal
native character-one quotient. Finiteness and flatness are not required. -/
theorem map_one_injective_of_smooth [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    {ρ : Representation R G V} {σ : Representation R G W}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) :
    Function.Injective (map U 1 M hMU (isInvariant_one U M hMU) i) := by
  suffices hz : ∀ x, map U 1 M hMU (isInvariant_one U M hMU) i x = 0 → x = 0 from
    fun x y h => sub_eq_zero.mp (hz (x - y) (by simp [map_sub, h]))
  intro x
  obtain ⟨v, rfl⟩ := mk_surjective ρ U 1 x
  intro hv
  have hiv : i v ∈ relations (complexRepresentation σ) U (1 : U →* ℂˣ) :=
    (mem_relations_one_iff σ U (i v)).mp ((mk_eq_zero σ U 1 _).mp hv)
  have hinj := Localization.map_injective_of_smooth U hU 1 (IsLocallyConstant.const 1)
    M hMU (isInvariant_one U M hMU) (complexIntertwiner i) hi hσ
  have hvC : mk (complexRepresentation ρ) U 1 v = 0 := by
    apply hinj
    rw [map_zero]
    exact (mk_eq_zero (complexRepresentation σ) U 1 _).mpr hiv
  exact (mk_eq_zero ρ U 1 v).mpr
    ((mem_relations_one_iff ρ U v).mpr ((mk_eq_zero _ U 1 v).mp hvC))

end Complex

section CanonicalScalars

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- The native injectivity law needs no separately supplied complex module
structure: restrict the given coefficient action along the algebra map. -/
theorem map_one_injective
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    {ρ : Representation R G V} {σ : Representation R G W}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) :
    Function.Injective (map U 1 M hMU (isInvariant_one U M hMU) i) := by
  let := Module.restrictScalars ℂ R V
  let := Module.restrictScalars ℂ R W
  let := IsScalarTower.restrictScalars ℂ R V
  let := IsScalarTower.restrictScalars ℂ R W
  exact map_one_injective_of_smooth U hU M hMU i hi hσ

end CanonicalScalars

end Langlands.Jacquet.Localization.Coefficient
