import Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesStatement
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # Actual affine-root membership from supplied coordinate depths -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

/-- A coordinate depth jump after quotienting by the supplied subgroup `K`. -/
def CoordinateDepthJump {P : Type v} [Group P] (depth : P → WithTop ℝ)
    (K : Subgroup P) (r : ℝ) : Prop :=
  ¬ {p | (r : WithTop ℝ) ≤ depth p} ⊆
    {p | (r : WithTop ℝ) < depth p} * (K : Set P)

/-- With trivial quotient subgroup, a depth jump is exactly an attained finite depth. -/
theorem coordinateDepthJump_bot_iff {P : Type v} [Group P]
    (depth : P → WithTop ℝ) (r : ℝ) :
    CoordinateDepthJump depth ⊥ r ↔ ∃ p, depth p = (r : WithTop ℝ) := by
  change (¬ {p | (r : WithTop ℝ) ≤ depth p} ⊆
    {p | (r : WithTop ℝ) < depth p} * (1 : Set P)) ↔ _
  rw [mul_one]
  constructor
  · intro h
    obtain ⟨p, hp, hp'⟩ := Set.not_subset.mp h
    exact ⟨p, le_antisymm (not_lt.mp hp') hp⟩
  · rintro ⟨p, hp⟩ h
    have hlt : (r : WithTop ℝ) < depth p := h (by
      change (r : WithTop ℝ) ≤ depth p
      rw [hp])
    rw [hp] at hlt
    exact lt_irrefl _ hlt

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

namespace KPApartmentData

/-- The actual closed-versus-strict root-group criterion transports through any supplied
coordinate isomorphism that identifies depths and the double-root subgroup. -/
theorem affineRootGroup_subset_mul_iff_coordinates
    {P : Type v} [Group P] (a : relativeRoots i)
    (e : P ≃* rootGroupPoints i a) (depth : P → WithTop ℝ) (K : Subgroup P)
    (x : D.Apartment) (hdepth : ∀ p, x.val a (e p) = depth p)
    (hdouble : ∀ g : rationalPoints G, g ∈ doubleRootGroupPoints i a ↔
      ∃ p ∈ K, (e p : rationalPoints G) = g)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a) :
    (D.affineRootGroup a ψ : Set (rationalPoints G)) ⊆
        (D.affineRootGroupPlus a ψ : Set (rationalPoints G)) *
          (doubleRootGroupPoints i a : Set (rationalPoints G)) ↔
      {p | ((ψ x : ℝ) : WithTop ℝ) ≤ depth p} ⊆
        {p | ((ψ x : ℝ) : WithTop ℝ) < depth p} * (K : Set P) := by
  constructor
  · intro h p hp
    have hpe : (e p : rationalPoints G) ∈ D.affineRootGroup a ψ :=
      (D.mem_affineRootGroup_iff hlin x).mpr ⟨(e p).property, by rwa [hdepth]⟩
    obtain ⟨g, hg, z, hz, hgz⟩ := h hpe
    have hgroot := (D.mem_affineRootGroupPlus_iff hlin x).mp hg
    let q : P := e.symm ⟨g, hgroot.1⟩
    have hq : (e q : rationalPoints G) = g := by simp [q]
    obtain ⟨c, hc, hce⟩ := (hdouble z).mp hz
    refine ⟨q, ?_, c, hc, ?_⟩
    · change ((ψ x : ℝ) : WithTop ℝ) < depth q
      rw [← hdepth, hq]
      exact hgroot.2
    · apply e.injective
      apply Subtype.ext
      change (e (q * c) : rationalPoints G) = (e p : rationalPoints G)
      simpa only [map_mul, Subgroup.coe_mul, hq, hce] using hgz
  · intro h g hg
    have hgroot := (D.mem_affineRootGroup_iff hlin x).mp hg
    let p : P := e.symm ⟨g, hgroot.1⟩
    have hp : (e p : rationalPoints G) = g := by simp [p]
    have hpdepth : ((ψ x : ℝ) : WithTop ℝ) ≤ depth p := by
      rw [← hdepth, hp]
      exact hgroot.2
    obtain ⟨q, hq, c, hc, hqc⟩ := h hpdepth
    change q * c = p at hqc
    refine ⟨(e q : rationalPoints G), ?_, (e c : rationalPoints G),
      (hdouble _).mpr ⟨c, hc, rfl⟩, ?_⟩
    · apply (D.mem_affineRootGroupPlus_iff hlin x).mpr
      exact ⟨(e q).property, by rwa [hdepth]⟩
    · change (e q : rationalPoints G) * (e c : rationalPoints G) = g
      rw [← Subgroup.coe_mul, ← map_mul, hqc, hp]

/-- If the reduced root forms distinguish relative roots, a supplied coordinate depth
jump is exactly ordinary affine-root membership in the specified direction. -/
theorem mem_affineRoots_iff_coordinateDepthJump
    (hforms : Function.Injective (rootForm i))
    {P : Type v} [Group P] (a : relativeRoots i)
    (e : P ≃* rootGroupPoints i a) (depth : P → WithTop ℝ) (K : Subgroup P)
    (x : D.Apartment) (hdepth : ∀ p, x.val a (e p) = depth p)
    (hdouble : ∀ g : rationalPoints G, g ∈ doubleRootGroupPoints i a ↔
      ∃ p ∈ K, (e p : rationalPoints G) = g)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a) :
    ψ ∈ D.affineRoots ↔ CoordinateDepthJump depth K (ψ x) := by
  have hsubset := D.affineRootGroup_subset_mul_iff_coordinates
    a e depth K x hdepth hdouble hlin
  constructor
  · rintro ⟨b, hb, hnot⟩
    have hba : b = a := hforms (hb.symm.trans hlin)
    subst b
    exact fun h => hnot (hsubset.mpr h)
  · intro h
    exact ⟨a, hlin, fun h' => h (hsubset.mp h')⟩

end KPApartmentData

variable {j : Z ⟶ G} {s : S.toGrp ⟶ Z}

/-- Supplied quadratic unitary coordinates identify ordinary affine roots with the literal
coordinate depth jump modulo the zero-first-coordinate subgroup. -/
theorem RootUnitaryCoordinates.mem_affineRoots_iff_coordinateDepthJump
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (R : RootUnitaryCoordinates i j s a)
    (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    (w : AddValuation R.extension (WithTop ℝ)) (x : D.Apartment)
    (hdepth : ∀ p, x.val a (R.equiv p) = SU3Root.Parameters.depthA w p)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a) :
    ψ ∈ D.affineRoots ↔
      CoordinateDepthJump (SU3Root.Parameters.depthA w)
        (SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension)) (ψ x) := by
  apply D.mem_affineRoots_iff_coordinateDepthJump
    (Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split hS i)
    a R.equiv _ _ x hdepth ?_ hlin
  intro g
  simpa [doubleRootGroupPoints, h2a] using R.double g

/-- In a direction with no double root, supplied additive field coordinates identify
ordinary affine roots with valuations of nonzero coordinates. -/
theorem RootFieldCoordinates.mem_affineRoots_iff_exists_valuation
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (R : RootFieldCoordinates i j s a)
    (hNo2 : 2 • (a : characterLattice S) ∉ relativeRoots i)
    (w : AddValuation R.extension (WithTop ℝ)) (x : D.Apartment)
    (hdepth : ∀ t : R.extension,
      x.val a (R.equiv (Multiplicative.ofAdd t)) = w t)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a) :
    ψ ∈ D.affineRoots ↔ ∃ t : R.extension, t ≠ 0 ∧ w t = ((ψ x : ℝ) : WithTop ℝ) := by
  have hdouble : ∀ g : rationalPoints G, g ∈ doubleRootGroupPoints i a ↔
      ∃ p ∈ (⊥ : Subgroup (Multiplicative R.extension)),
        (R.equiv p : rationalPoints G) = g := by
    intro g
    simp only [doubleRootGroupPoints, ite_eq_right hNo2, Subgroup.mem_bot]
    constructor
    · intro hg
      exact ⟨1, rfl, by simp [hg]⟩
    · rintro ⟨p, rfl, hp⟩
      simpa only [map_one, Subgroup.coe_one] using hp.symm
  rw [D.mem_affineRoots_iff_coordinateDepthJump
    (Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split hS i)
    a R.equiv (fun p => w p.toAdd) ⊥ x (fun p => hdepth p.toAdd) hdouble hlin,
    coordinateDepthJump_bot_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.toAdd, ?_, hp⟩
    intro hzero
    rw [hzero, w.map_zero] at hp
    exact WithTop.top_ne_coe hp
  · rintro ⟨t, -, ht⟩
    exact ⟨Multiplicative.ofAdd t, ht⟩

end Langlands.Geometry.Building
