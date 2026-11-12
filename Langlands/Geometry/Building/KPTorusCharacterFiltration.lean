import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.Geometry.Building.KPLogCharacterCongruenceTopology
import Langlands.Geometry.Building.KPTorusNormNaturality
import Langlands.GroupScheme.Rational.ScalarExtensionTopology

/-! # Character congruences after extension and torus filtrations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Algebra

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (ω : AddValuation L (WithTop ℝ))
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Congruences tested on all actual characters after the specified scalar
extension, pulled back to the original rational-point group. -/
def extendedCharacterCongruence (r : ℝ≥0) : Subgroup (rationalPoints G) :=
  (characterCongruence ω (baseChanged k L G) r).comap (rationalExtend k L G)

@[simp] theorem mem_extendedCharacterCongruence (r : ℝ≥0) (g : rationalPoints G) :
    g ∈ extendedCharacterCongruence k L ω G r ↔
      rationalExtend k L G g ∈ characterCongruence ω (baseChanged k L G) r := Iff.rfl

theorem extendedCharacterCongruence_antitone :
    Antitone (extendedCharacterCongruence k L ω G) :=
  fun _ _ hrs => Subgroup.comap_mono (characterCongruence_antitone ω _ hrs)

/-- Extension on the original rational-point carriers is injective. -/
theorem rationalExtend_injective_of_isAffine [IsAffine G.X.left] :
    Function.Injective (rationalExtend k L G) := by
  intro x y h
  apply (rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k L G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv k L G) h

/-- The extended-character conditions are functorial under actual morphisms. -/
theorem map_extendedCharacterCongruence_le
    {H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) (r : ℝ≥0) :
    (extendedCharacterCongruence k L ω G r).map (rationalPoints.map f) ≤
      extendedCharacterCongruence k L ω H r := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_extendedCharacterCongruence, GaloisPointComparison.rationalExtend_map]
  exact map_characterCongruence_le ω
    ((GroupScheme.baseChange (baseMap k L)).map f) r ⟨_, hg, rfl⟩

/-- Characters after a splitting extension separate the original torus points. -/
theorem iInf_extendedCharacterCongruence_eq_bot
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    (hT : IsSplitTorus (baseChanged k L T.toGrp)) :
    ⨅ r : ℝ≥0, extendedCharacterCongruence k L ω T.toGrp r = ⊥ := by
  apply le_antisymm _ bot_le
  intro t ht
  apply Subgroup.mem_bot.mpr
  apply rationalExtend_injective_of_isAffine k L T.toGrp
  rw [map_one]
  have ht' : rationalExtend k L T.toGrp t ∈
      ⨅ r : ℝ≥0, characterCongruence ω (baseChanged k L T.toGrp) r := by
    simpa only [Subgroup.mem_iInf, mem_extendedCharacterCongruence] using ht
  have hchars := (mem_iInf_characterCongruence ω (baseChanged k L T.toGrp) _).mp ht'
  exact eq_one_of_rationalCharacters_of_isSplitTorus
    ((CommGroupScheme.baseChange (baseMap k L)).obj T) hT _ hchars

end Algebra

section Topology

variable (k L : Type u) [Field k] [NormedField L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left] [TopologicalSpace k] [IsUltrametricDist L]
  [Module.Finite ℤ (rationalCharacters (baseChanged k L G))]

private instance extendedCharacter_isAffine : IsAffine (baseChanged k L G).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback G.X.hom (baseMap k L))
  infer_instance

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
local instance : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
  rationalPointTopology L (baseChanged k L G).X

/-- Logarithmic extended-character congruence is open when the field inclusion
is continuous. -/
theorem isOpen_extendedCharacterCongruence_log
    (hcont : Continuous (algebraMap k L)) (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    IsOpen (extendedCharacterCongruence k L
      (logAdditiveValuation (NormedField.valuation (K := L)) c hc) G r :
        Set (rationalPoints G)) :=
  (isOpen_characterCongruence_log (baseChanged k L G) c hc r).preimage
    (continuous_rationalExtend k L G hcont)

end Topology

section Torus

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (ω : AddValuation L (WithTop ℝ))
  [FiniteDimensional k L] [IsGalois k L]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- A torus filtration with the specified norm Iwahori subgroup at zero and its
intersection with the extended-character congruence subgroup at positive depth. -/
def torusCharacterFiltration (r : ℝ≥0) : Subgroup (rationalPoints T.toGrp) :=
  if r = 0 then torusNormIwahori k L v T else
    torusNormIwahori k L v T ⊓ extendedCharacterCongruence k L ω T.toGrp r

@[simp] theorem torusCharacterFiltration_zero :
    torusCharacterFiltration k L ω v T 0 = torusNormIwahori k L v T := by
  simp [torusCharacterFiltration]

theorem torusCharacterFiltration_le (r : ℝ≥0) :
    torusCharacterFiltration k L ω v T r ≤ torusNormIwahori k L v T := by
  by_cases hr : r = 0
  · simp only [hr, torusCharacterFiltration_zero, le_refl]
  · simp only [torusCharacterFiltration, ite_eq_right hr]
    exact inf_le_left

theorem torusCharacterFiltration_antitone :
    Antitone (torusCharacterFiltration k L ω v T) := by
  intro r s hrs
  by_cases hr : r = 0
  · subst r
    rw [torusCharacterFiltration_zero]
    exact torusCharacterFiltration_le k L ω v T s
  · have hs : s ≠ 0 := by
      intro hs
      apply hr
      exact le_antisymm (hs ▸ hrs) (zero_le : (0 : ℝ≥0) ≤ r)
    simp only [torusCharacterFiltration, ite_eq_right hr, ite_eq_right hs]
    exact inf_le_inf_left _ (extendedCharacterCongruence_antitone k L ω T.toGrp hrs)

/-- The torus family is separated when the extension splits the torus. -/
theorem iInf_torusCharacterFiltration_eq_bot
    (hT : IsSplitTorus (baseChanged k L T.toGrp)) :
    ⨅ r : ℝ≥0, torusCharacterFiltration k L ω v T r = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← iInf_extendedCharacterCongruence_eq_bot k L ω T hT]
  intro t ht
  simp only [Subgroup.mem_iInf] at ht ⊢
  intro r
  have h := ht (r + 1)
  have hr : r + 1 ≠ 0 := ne_of_gt (by positivity)
  simp only [torusCharacterFiltration, ite_eq_right hr, Subgroup.mem_inf] at h
  exact extendedCharacterCongruence_antitone k L ω T.toGrp
    (le_add_of_nonneg_right zero_le) h.2

/-- The actual morphism of tori preserves this family at every depth. -/
theorem map_torusCharacterFiltration_le
    {U : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffine U.X.left]
    (f : T ⟶ U) (r : ℝ≥0) :
    (torusCharacterFiltration k L ω v T r).map
        (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
      torusCharacterFiltration k L ω v U r := by
  rintro _ ⟨t, ht, rfl⟩
  by_cases hr : r = 0
  · subst r
    rw [torusCharacterFiltration_zero] at ht ⊢
    exact map_torusNormIwahori_le k L v f ⟨t, ht, rfl⟩
  · simp only [torusCharacterFiltration, ite_eq_right hr, Subgroup.mem_inf] at ht ⊢
    exact ⟨map_torusNormIwahori_le k L v f ⟨t, ht.1, rfl⟩,
      map_extendedCharacterCongruence_le k L ω T.toGrp
        (CommGroupScheme.groupHom f) r ⟨t, ht.2, rfl⟩⟩

variable [TopologicalSpace k]

local instance : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X

/-- Openness of the zero subgroup and of the character conditions implies
openness of the resulting torus family. -/
theorem isOpen_torusCharacterFiltration
    (hzero : IsOpen (torusNormIwahori k L v T : Set (rationalPoints T.toGrp)))
    (hcong : ∀ r : ℝ≥0, IsOpen
      (extendedCharacterCongruence k L ω T.toGrp r : Set (rationalPoints T.toGrp)))
    (r : ℝ≥0) :
    IsOpen (torusCharacterFiltration k L ω v T r : Set (rationalPoints T.toGrp)) := by
  by_cases hr : r = 0
  · simpa only [hr, torusCharacterFiltration_zero] using hzero
  · simpa only [torusCharacterFiltration, ite_eq_right hr, Subgroup.coe_inf] using
      hzero.inter (hcong r)

end Torus

section TorusTopology

variable (k L : Type u) [Field k] [NormedField L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [TopologicalSpace k] [IsUltrametricDist L]
  [Module.Finite ℤ (rationalCharacters (baseChanged k L T.toGrp))]

local instance : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X

/-- For logarithmic norm congruences, openness of the norm subgroup suffices
for every member of the torus family to be open. -/
theorem isOpen_torusCharacterFiltration_log
    (hcont : Continuous (algebraMap k L)) (c : ℝ) (hc : 0 < c)
    (hzero : IsOpen (torusNormIwahori k L v T : Set (rationalPoints T.toGrp)))
    (r : ℝ≥0) :
    IsOpen (torusCharacterFiltration k L
      (logAdditiveValuation (NormedField.valuation (K := L)) c hc) v T r :
        Set (rationalPoints T.toGrp)) :=
  isOpen_torusCharacterFiltration k L _ v T hzero
    (isOpen_extendedCharacterCongruence_log k L T.toGrp hcont c hc) r

end TorusTopology

end Langlands.Geometry.Building
