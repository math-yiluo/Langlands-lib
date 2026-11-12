import Langlands.Geometry.Building.MoyPrasadNormalizerCovariance
import Langlands.Geometry.Building.MoyPrasadGlobalExchange

/-! # Reduction of reduced-building covariance to root conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open scoped TensorProduct

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- The already proved generator cases leave only conjugation of a
negative doubled-root element by an ordinary depth-zero element. -/
theorem conjugate_root_mem_moyPrasad_of_double_opposite_bound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (hmixed : ∀ (a : characterLattice P.S), a ∈ relativeRoots P.i →
      2 • a ∈ relativeRoots P.i → ∀ (u v : rationalPoints G),
      u ∈ P.filtration x a 0 → v ∈ P.filtration x (-(2 • a)) r →
        u * v * u⁻¹ ∈ Zf.moyPrasad x r)
    (a b : relativeRoots P.i) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x b r) :
    u * v * u⁻¹ ∈ Zf.moyPrasad x r := by
  classical
  by_cases hnon : ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] (b : characterLattice P.S) : Vstar P.S) ≠
        -(t • (1 : ℝ) ⊗ₜ[ℤ] (a : characterLattice P.S))
  · exact Zf.conjugate_root_mem_moyPrasad_of_nonopposite x a.2 b.2 hnon r hu hv
  push Not at hnon
  obtain ⟨t, ht, heq⟩ := hnon
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hnb : -(b : characterLattice P.S) ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x b.2
  have heval : eval P.S (-(b : characterLattice P.S)) =
      t • eval P.S (a : characterLattice P.S) := by
    apply LinearMap.ext
    intro w
    have h := congrArg (fun chi => pair P.S chi w) heq
    simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
      smul_eq_mul, ← eval_eq_pair] at h
    rw [eval_neg_char, LinearMap.smul_apply, smul_eq_mul, h]
    ring
  rcases P.apartment.eq_or_double_of_eval_eq_smul hT
    hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
    a.2 hnb ht heval with h | h | h
  · have hb : (b : characterLattice P.S) = -(a : characterLattice P.S) := by
      rw [← h, neg_neg]
    have hv' : v ∈ P.filtration x (-(a : characterLattice P.S)) r := hb ▸ hv
    exact Zf.conjugate_opposite_mem_moyPrasad hP hZ x a.2 r hr hu hv'
  · have hb : (b : characterLattice P.S) = -(2 • (a : characterLattice P.S)) := by
      rw [← h, neg_neg]
    have h2a : 2 • (a : characterLattice P.S) ∈ relativeRoots P.i := h ▸ hnb
    exact hmixed a a.2 h2a u v hu (hb ▸ hv)
  · have h2nb : 2 • (-(b : characterLattice P.S)) ∈ relativeRoots P.i := h ▸ a.2
    have hu2 : u ∈ P.filtration x (2 • (-(b : characterLattice P.S))) 0 := h ▸ hu
    have hu0 : u ∈ P.filtration x (-(b : characterLattice P.S)) 0 := by
      simpa only [zero_div] using P.apartment.filtration_double_le_half x hnb h2nb 0 hu2
    exact Zf.conjugate_opposite_mem_moyPrasad hP hZ x hnb r hr hu0
      (by simpa only [neg_neg] using hv)

/-- Root-compatible middle conjugation and conjugation on all original
root generators assemble to normalization by the original sharp fixer. -/
theorem sharpFixer_le_normalizer_moyPrasad_of_root_conjugation
    (hZr : Zf.IsRootCompatible) (x : P.Apartment) (r : NNReal)
    (hroot : ∀ (a b : relativeRoots P.i) (u v : rationalPoints G),
      u ∈ P.filtration x a 0 → v ∈ P.filtration x b r →
        u * v * u⁻¹ ∈ Zf.moyPrasad x r) :
    P.sharpFixer {x} ≤ Subgroup.normalizer (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  refine iSup_le fun a => ?_
  rw [P.apartment.rootFixer_singleton]
  apply Subgroup.le_normalizer_iff.mpr
  intro u hu g hg
  have hle : Zf.moyPrasad x r ≤ (Zf.moyPrasad x r).comap
      (MulAut.conj u).toMonoidHom := by
    conv_lhs => rw [moyPrasad, P.apartment.sharpFiltration_eq_iSup]
    refine sup_le ?_ (iSup_le fun b v hv => ?_)
    · intro z hz
      change u * z * u⁻¹ ∈ Zf.moyPrasad x r
      exact Zf.conjugate_image_mem_moyPrasad hZr x a.2 r hu hz
    · change u * v * u⁻¹ ∈ Zf.moyPrasad x r
      exact hroot a b u v hu hv
  exact hle hg

/-- The actual quotient relation gives uniqueness of a Moy–Prasad
presentation once its original sharp fixers normalize the original groups. -/
theorem isMoyPrasadAt_unique_of_sharp_normalization
    (hZn : Zf.IsNormalizerStable)
    (hsharp : ∀ (x : P.Apartment) (r : NNReal),
      P.sharpFixer {x} ≤ Subgroup.normalizer (Zf.moyPrasad x r : Set (rationalPoints G)))
    (y : P.ReducedBuilding) (r : NNReal) (Q Q' : Subgroup (rationalPoints G))
    (hQ : Zf.IsMoyPrasadAt y r Q) (hQ' : Zf.IsMoyPrasadAt y r Q') :
    Q = Q' := by
  obtain ⟨g, x, hgy, rfl⟩ := hQ
  obtain ⟨h, x', hhy, rfl⟩ := hQ'
  have hpres : ApartmentQuotient.mk P.apartment.sharpFixerFamily (g, x) =
      ApartmentQuotient.mk P.apartment.sharpFixerFamily (h, x') :=
    (ApartmentQuotient.mk_eq_smul_apartment P.apartment.sharpFixerFamily g x).trans
      ((hgy.trans hhy.symm).trans
        (ApartmentQuotient.mk_eq_smul_apartment P.apartment.sharpFixerFamily h x').symm)
  obtain ⟨n, hnx, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff P.apartment.sharpFixerFamily g h x x').mp hpres
  let p : rationalPoints G := g⁻¹ * h * (n : rationalPoints G)
  have hpmap : (Zf.moyPrasad x r).map (MulAut.conj p).toMonoidHom = Zf.moyPrasad x r :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hsharp x r hp)
  have hnmap : (Zf.moyPrasad x' r).map
      (MulAut.conj (n : rationalPoints G)⁻¹).toMonoidHom = Zf.moyPrasad x r := by
    have hn := Zf.moyPrasad_map_conj_normalizer hZn x' r n⁻¹
    have hpoint : n⁻¹ • x' = x := by rw [← hnx, inv_smul_smul]
    simpa only [hpoint, Subgroup.coe_inv] using hn
  have heq : h = (g * p) * (n : rationalPoints G)⁻¹ := by
    dsimp only [p]
    group
  rw [heq, ← map_conj_map_conj, hnmap, ← map_conj_map_conj, hpmap]

/-- All local root cases and depth zero are discharged except the stated
ordinary-versus-doubled opposite conjugation bound. -/
theorem sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (hZr : Zf.IsRootCompatible)
    (hmixed : ∀ (x : P.Apartment) (r : NNReal), 0 < r →
      ∀ (a : characterLattice P.S), a ∈ relativeRoots P.i →
      2 • a ∈ relativeRoots P.i → ∀ (u v : rationalPoints G),
      u ∈ P.filtration x a 0 → v ∈ P.filtration x (-(2 • a)) r →
        u * v * u⁻¹ ∈ Zf.moyPrasad x r)
    (x : P.Apartment) (r : NNReal) :
    P.sharpFixer {x} ≤ Subgroup.normalizer (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  by_cases hr0 : r = 0
  · subst r
    have hle : P.sharpFixer {x} ≤ Zf.moyPrasad x 0 := by
      rw [Zf.moyPrasad_zero]
      exact P.sharpFixer_le_parahoric {x}
    apply Subgroup.le_normalizer_iff.mpr
    intro u hu v hv
    exact (Zf.moyPrasad x 0).mul_mem ((Zf.moyPrasad x 0).mul_mem (hle hu) hv)
      ((Zf.moyPrasad x 0).inv_mem (hle hu))
  · have hr : 0 < r := lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ r) (Ne.symm hr0)
    apply Zf.sharpFixer_le_normalizer_moyPrasad_of_root_conjugation hZr x r
    intro a b u v hu hv
    exact Zf.conjugate_root_mem_moyPrasad_of_double_opposite_bound hP hZ x r hr
      (hmixed x r hr) a b hu hv

/-- The exact local input still needed for full reduced-building uniqueness
is ordinary depth-zero versus doubled opposite positive-depth conjugation. -/
theorem isMoyPrasadAt_unique_of_double_opposite_bound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hmixed : ∀ (x : P.Apartment) (r : NNReal), 0 < r →
      ∀ (a : characterLattice P.S), a ∈ relativeRoots P.i →
      2 • a ∈ relativeRoots P.i → ∀ (u v : rationalPoints G),
      u ∈ P.filtration x a 0 → v ∈ P.filtration x (-(2 • a)) r →
        u * v * u⁻¹ ∈ Zf.moyPrasad x r)
    (y : P.ReducedBuilding) (r : NNReal) (Q Q' : Subgroup (rationalPoints G))
    (hQ : Zf.IsMoyPrasadAt y r Q) (hQ' : Zf.IsMoyPrasadAt y r Q') : Q = Q' :=
  Zf.isMoyPrasadAt_unique_of_sharp_normalization hZ.2.1
    (Zf.sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound hP hZ.1 hZ.2.2.2 hmixed)
    y r Q Q' hQ hQ'

/-- The original reduced-building subgroup, with its actual presentation
and uniqueness certificate, once local sharp normalization is supplied. -/
def moyPrasadAtUniqueOfSharpNormalization
    (hZn : Zf.IsNormalizerStable)
    (hsharp : ∀ (x : P.Apartment) (r : NNReal),
      P.sharpFixer {x} ≤ Subgroup.normalizer (Zf.moyPrasad x r : Set (rationalPoints G)))
    (y : P.ReducedBuilding) (r : NNReal) :
    {Q : Subgroup (rationalPoints G) //
      Zf.IsMoyPrasadAt y r Q ∧
        ∀ Q', Zf.IsMoyPrasadAt y r Q' → Q' = Q} := by
  apply Classical.choice
  obtain ⟨Q, hQ⟩ := Zf.exists_isMoyPrasadAt y r
  exact ⟨⟨Q, hQ, fun Q' hQ' =>
    Zf.isMoyPrasadAt_unique_of_sharp_normalization hZn hsharp y r Q' Q hQ' hQ⟩⟩

/-- Unique original reduced-building coordinates under the one remaining
mixed opposite-root conjugation input. -/
def moyPrasadAtUniqueOfDoubleOppositeBound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hmixed : ∀ (x : P.Apartment) (r : NNReal), 0 < r →
      ∀ (a : characterLattice P.S), a ∈ relativeRoots P.i →
      2 • a ∈ relativeRoots P.i → ∀ (u v : rationalPoints G),
      u ∈ P.filtration x a 0 → v ∈ P.filtration x (-(2 • a)) r →
        u * v * u⁻¹ ∈ Zf.moyPrasad x r)
    (y : P.ReducedBuilding) (r : NNReal) :
    {Q : Subgroup (rationalPoints G) //
      Zf.IsMoyPrasadAt y r Q ∧
        ∀ Q', Zf.IsMoyPrasadAt y r Q' → Q' = Q} :=
  Zf.moyPrasadAtUniqueOfSharpNormalization hZ.2.1
    (Zf.sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound hP hZ.1 hZ.2.2.2 hmixed)
    y r

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
