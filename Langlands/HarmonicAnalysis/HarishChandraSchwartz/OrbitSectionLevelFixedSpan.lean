import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFixedTensor

/-! # A single section level for a finite span of compact coefficients -/

noncomputable section

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "Fixed" H => orbitSectionFixedCoefficients h K π H

omit [LocallyCompactSpace G] in
/-- A finite family of compact-picture vectors spans a subspace fixed
by one open subgroup of the form `H × H` with `H ≤ K`. -/
theorem exists_span_le_orbitSectionFixedCoefficients
    {B : Type uB} (S : Finset B) (v : B → Picture) :
    ∃ H : OpenSubgroup G, H ≤ K ∧ Submodule.span ℂ (v '' (S : Set B)) ≤ Fixed H := by
  classical
  have hsmooth (b : B) : ∃ L : OpenSubgroup (K.prod K),
      ∀ k : L, productInducedCompactRepresentation h K π.obj k.val (v b) = v b :=
    smoothInduced_smooth _ _ (v b)
  choose L hL using hsmooth
  let L₀ := S.inf L
  let D : OpenSubgroup (G × G) :=
    { toSubgroup := L₀.toSubgroup.map (K.prod K).toSubgroup.subtype
      isOpen' := (K.prod K).isOpen.isOpenMap_subtype_val _ L₀.isOpen }
  let H : OpenSubgroup G :=
    (OpenSubgroup.comap (MonoidHom.inl G G) (continuous_id.prodMk continuous_const) D ⊓
      OpenSubgroup.comap (MonoidHom.inr G G) (continuous_const.prodMk continuous_id) D) ⊓ K
  have hHK : H ≤ K := inf_le_right
  refine ⟨H, hHK, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  apply (mem_orbitSectionFixedCoefficients_iff h K π H hHK (v b)).mpr
  intro x
  have hx : x.val ∈ D := by
    have hx₁ : (x.val.1, 1) ∈ D := x.property.1.1.1
    have hx₂ : (1, x.val.2) ∈ D := x.property.2.1.2
    simpa using D.mul_mem hx₁ hx₂
  obtain ⟨k, hk, hkx⟩ := hx
  have hk' : k = ⟨x.val, hHK x.property.1, hHK x.property.2⟩ := Subtype.ext hkx
  rw [← hk']
  exact hL b ⟨k, (Finset.inf_le hb : L₀ ≤ L b) hk⟩

variable (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

set_option hygiene false in
local notation "Sections" => productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "R" => productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
set_option hygiene false in
local notation "Level" H => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "includeLevel[" H "]" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK H

omit [DecidableEq J] in
/-- A smooth section takes values in a fixed compact fiber exactly when it
is fixed by the corresponding product subgroup. This direction uses
faithfulness of the actual compact restriction. -/
theorem mem_orbitSectionLevelSubmodule_of_compactRestriction
    (H : OpenSubgroup G) (hHK : H ≤ K) (q : Sections)
    (hfixed : ∀ z : J → Circle, R q z ∈ Fixed H) :
    q.val ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H := by
  refine ⟨q.property, fun x => ?_⟩
  let k : K.prod K := ⟨x.val, hHK x.property.1, hHK x.property.2⟩
  let B := productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e
  have hq : B k q = q := by
    apply productInducedSmoothOrbitCompactRestriction_injective h hU ν π K hP hK hν hr hPK e
    funext z
    have he := productInducedOrbitRepresentation_restriction h hU ν π K hP hK hν hr hPK e k q.val z
    exact he.trans ((mem_orbitSectionFixedCoefficients_iff h K π H hHK (R q z)).mp (hfixed z) x)
  exact congrArg Subtype.val hq

/-- View an actual smooth section whose compact restrictions are fixed as an
element of that section level. -/
def orbitSectionLevelOfFixedRestriction
    (H : OpenSubgroup G) (hHK : H ≤ K) (q : Sections)
    (hfixed : ∀ z : J → Circle, R q z ∈ Fixed H) : Level H :=
  ⟨q.val, mem_orbitSectionLevelSubmodule_of_compactRestriction h K π hU hP hK hPK
    ν hν hr e H hHK q hfixed⟩

omit [DecidableEq J] in
@[simp]
theorem orbitSectionLevelOfFixedRestriction_toSections
    (H : OpenSubgroup G) (hHK : H ≤ K) (q : Sections)
    (hfixed : ∀ z : J → Circle, R q z ∈ Fixed H) :
    includeLevel[H] (orbitSectionLevelOfFixedRestriction h K π hU hP hK hPK
      ν hν hr e H hHK q hfixed) = q := rfl

end Langlands.HarishChandraSchwartz
