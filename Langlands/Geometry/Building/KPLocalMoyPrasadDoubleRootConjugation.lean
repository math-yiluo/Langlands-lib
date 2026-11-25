import Langlands.Geometry.Building.KPLocalMoyPrasadMixedConjugation
import Langlands.Geometry.Building.KPLocalCentralizerFiltrationNormalizerStable

/-! # K-level normality from ordinary and doubled-root torus bounds -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise NNReal TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The independent doubled-root torus estimate,
restricted to the given actual building and torus filtration. -/
def LocalTorusDoubleRootCommutatorFriendly : Prop :=
  ∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
    u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
    (u ∈ B.doubleRootGroup a.1 ∨ u' ∈ B.doubleRootGroup (-a.1)) →
    ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
    ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
      v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
      u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
      z ∈ B.centralizerTorusFiltration hZ (2 * r)

/-- The root compatibility clause of S1 for the given actual filtration. -/
def LocalTorusRootCompatible : Prop :=
  ∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
    ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
      z * u * z⁻¹ * u⁻¹ ∈
        B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1

/-- The actual central coordinate of an ordinary/doubled-opposite exchange
has the full doubled input depth under double-root friendliness. -/
theorem double_opposite_central_mem_of_doubleRootCommutatorFriendly
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-(2 • a)) r)
    (v' : rationalPoints H) (hv' : v' ∈ rootGroupPoints B.i (-a))
    (z : rationalPoints B.centralizer.Z) (u' : rationalPoints H)
    (hu' : u' ∈ rootGroupPoints B.i a)
    (heq : v' * rationalPoints.map B.centralizer.j z * u' = u * v) :
    z ∈ B.centralizerTorusFiltration hZ r := by
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hna : -a ∈ relativeRoots B.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  have h2na : 2 • (-a) ∈ relativeRoots B.i := by
    have hn := KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x h2a
    simpa only [smul_neg] using hn
  have hvHalf : v ∈ B.filtration x (-a) ((r : ℝ) / 2) :=
    B.apartment.filtration_double_le_half x hna h2na r
      (by simpa only [smul_neg] using hv)
  have hjinj : Function.Injective (rationalPoints.map B.centralizer.j) := by
    intro z w h
    have : Mono B.centralizer.j.hom.hom := B.centralizer.isRepresentedBy.1
    exact (cancel_mono B.centralizer.j.hom.hom).mp h
  by_cases hu1 : u = 1
  · have huniq := B.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'⟩,
        ⟨rationalPoints.map B.centralizer.j z,
          map_mem_centralizerPoints B.centralizer.isRepresentedBy z⟩, ⟨u', hu'⟩))
      (a₂ := (⟨v, hvHalf.1⟩, 1, 1)) (by simpa [hu1] using heq)
    have hzG : rationalPoints.map B.centralizer.j z = 1 :=
      congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
        rootGroupPoints B.i a => (p.2.1 : rationalPoints H)) huniq
    have hz1 : z = 1 := hjinj (by simpa using hzG)
    simpa only [hz1] using (B.centralizerTorusFiltration hZ r).one_mem
  by_cases hv1 : v = 1
  · have huniq := B.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'⟩,
        ⟨rationalPoints.map B.centralizer.j z,
          map_mem_centralizerPoints B.centralizer.isRepresentedBy z⟩, ⟨u', hu'⟩))
      (a₂ := (1, 1, ⟨u, hu.1⟩)) (by simpa [hv1] using heq)
    have hzG : rationalPoints.map B.centralizer.j z = 1 :=
      congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
        rootGroupPoints B.i a => (p.2.1 : rationalPoints H)) huniq
    have hz1 : z = 1 := hjinj (by simpa using hzG)
    simpa only [hz1] using (B.centralizerTorusFiltration hZ r).one_mem
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  obtain ⟨s, hs⟩ := KPApartmentData.exists_val_eq_coe x hna hvHalf.1 hv1
  have ht0 : 0 ≤ t := by
    have h := hu.2
    rwa [ht, WithTop.coe_le_coe] at h
  have hsr : (r : ℝ) / 2 ≤ s := by
    have h := hvHalf.2
    rwa [hs, WithTop.coe_le_coe] at h
  have hsum : 0 < t + s := by
    have hr' : 0 < (r : ℝ) := hr
    linarith
  let d : NNReal := ⟨t + s, hsum.le⟩
  have hd : 0 < d := hsum
  have hvalue : (((d : ℝ) : WithTop ℝ)) = x.val a u + x.val (-a) v := by
    rw [ht, hs, ← WithTop.coe_add]
    rfl
  have hvDouble : v ∈ B.doubleRootGroup (-a) := by
    change v ∈ doubleRootGroupPoints B.i (-a)
    simp only [doubleRootGroupPoints, h2na, ↓reduceIte]
    simpa only [smul_neg] using hv.1
  have hcomm : v⁻¹ * u * v * u⁻¹ =
      (v⁻¹ * v') * rationalPoints.map B.centralizer.j z * (u' * u⁻¹) := by
    calc v⁻¹ * u * v * u⁻¹ = v⁻¹ * (u * v) * u⁻¹ := by group
      _ = v⁻¹ * (v' * rationalPoints.map B.centralizer.j z * u') * u⁻¹ := by rw [heq]
      _ = (v⁻¹ * v') * rationalPoints.map B.centralizer.j z * (u' * u⁻¹) := by group
  have hzdepth : z ∈ B.centralizerTorusFiltration hZ (2 * d) :=
    hZ2 x ⟨a, ha⟩ u v hu.1 hu1 hvHalf.1 hv1 (Or.inr hvDouble)
      d hd hvalue (v⁻¹ * v') (u' * u⁻¹) z
      ((rootGroupPoints B.i (-a)).mul_mem
        ((rootGroupPoints B.i (-a)).inv_mem hvHalf.1) hv')
      ((rootGroupPoints B.i a).mul_mem hu' ((rootGroupPoints B.i a).inv_mem hu.1))
      hcomm
  apply B.centralizerTorusFiltration_antitone hZ (show r ≤ 2 * d from ?_) hzdepth
  apply NNReal.coe_le_coe.mp
  change (r : ℝ) ≤ 2 * (t + s)
  linarith

/-- Double-root friendliness discharges the last middle-coordinate input
for mixed doubled-opposite conjugation in the original subgroup. -/
theorem conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-(2 • a)) r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r :=
  B.conjugate_double_opposite_mem_moyPrasad_of_central_bound hZ hZcomm x ha h2a r hr hu hv
    (B.double_opposite_central_mem_of_doubleRootCommutatorFriendly
      hZ hZ2 x ha h2a r hr hu hv)

/-- The already proved generator cases leave only conjugation of a
negative doubled-root element by an ordinary depth-zero element. -/
theorem conjugate_root_mem_moyPrasad_of_double_opposite_bound
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) (r : NNReal) (hr : 0 < r)
    (hmixed : ∀ (a : characterLattice B.S), a ∈ relativeRoots B.i →
      2 • a ∈ relativeRoots B.i → ∀ (u v : rationalPoints H),
      u ∈ B.filtration x a 0 → v ∈ B.filtration x (-(2 • a)) r →
        u * v * u⁻¹ ∈ B.moyPrasad hZ x r)
    (a b : relativeRoots B.i) {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x b r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r := by
  classical
  by_cases hnon : ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] (b : characterLattice B.S) : Vstar B.S) ≠
        -(t • (1 : ℝ) ⊗ₜ[ℤ] (a : characterLattice B.S))
  · exact B.conjugate_root_mem_moyPrasad_of_nonopposite hZ x a.2 b.2 hnon r hu hv
  push Not at hnon
  obtain ⟨t, ht, heq⟩ := hnon
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hnb : -(b : characterLattice B.S) ∈ relativeRoots B.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x b.2
  have heval : eval B.S (-(b : characterLattice B.S)) =
      t • eval B.S (a : characterLattice B.S) := by
    apply LinearMap.ext
    intro w
    have h := congrArg (fun chi => pair B.S chi w) heq
    simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
      smul_eq_mul, ← eval_eq_pair] at h
    rw [eval_neg_char, LinearMap.smul_apply, smul_eq_mul, h]
    ring
  rcases B.apartment.eq_or_double_of_eval_eq_smul hT
    (B.isAffineRootSystemWithRankZero_extendedAffineRoots (exists_order_eq_one F))
    B.derivativeRoots_extendedAffineRoots
    a.2 hnb ht heval with h | h | h
  · have hb : (b : characterLattice B.S) = -(a : characterLattice B.S) := by
      rw [← h, neg_neg]
    have hv' : v ∈ B.filtration x (-(a : characterLattice B.S)) r := hb ▸ hv
    exact B.conjugate_opposite_mem_moyPrasad hZ hZcomm x a.2 r hr hu hv'
  · have hb : (b : characterLattice B.S) = -(2 • (a : characterLattice B.S)) := by
      rw [← h, neg_neg]
    have h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i := h ▸ hnb
    exact hmixed a a.2 h2a u v hu (hb ▸ hv)
  · have h2nb : 2 • (-(b : characterLattice B.S)) ∈ relativeRoots B.i := h ▸ a.2
    have hu2 : u ∈ B.filtration x (2 • (-(b : characterLattice B.S))) 0 := h ▸ hu
    have hu0 : u ∈ B.filtration x (-(b : characterLattice B.S)) 0 := by
      simpa only [zero_div] using B.apartment.filtration_double_le_half x hnb h2nb 0 hu2
    exact B.conjugate_opposite_mem_moyPrasad hZ hZcomm x hnb r hr hu0
      (by simpa only [neg_neg] using hv)


/-- The ordinary and doubled-root bounds cover every pair of root generators,
including the zero-depth case. -/
theorem conjugate_root_mem_moyPrasad_of_torus_commutator_bounds
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (x : B.Apartment) (r : NNReal) (a b : relativeRoots B.i)
    {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x b r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r := by
  by_cases hr0 : r = 0
  · subst r
    have humem := B.filtration_le_moyPrasad hZ x a 0 hu
    have hvmem := B.filtration_le_moyPrasad hZ x b 0 hv
    exact (B.moyPrasad hZ x 0).mul_mem
      ((B.moyPrasad hZ x 0).mul_mem humem hvmem)
      ((B.moyPrasad hZ x 0).inv_mem humem)
  · have hr : 0 < r := lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ r) (Ne.symm hr0)
    exact B.conjugate_root_mem_moyPrasad_of_double_opposite_bound hZ hZcomm x r hr
      (fun _a ha h2a _u _v hu hv =>
        B.conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly
          hZ hZcomm hZ2 x ha h2a r hr hu hv) a b hu hv

/-- Clause 1 of S2 follows from S1's first two clauses and the independent
actual doubled-root torus bound. -/
theorem localMoyPrasadNormality_of_torus_commutator_bounds
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (hZr : B.LocalTorusRootCompatible hZ) :
    LocalMoyPrasadNormality B hZ :=
  B.localMoyPrasadNormality_of_root_conjugation hZ hZr
    (fun x r a b _u _v hu hv =>
      B.conjugate_root_mem_moyPrasad_of_torus_commutator_bounds hZ hZcomm hZ2 x r a b hu hv)

/-- Clause 2 of S2 uses the same explicit rank-one inputs as clause 1;
normalizer stability itself is unconditional for the actual torus filtration. -/
theorem localMoyPrasadEquivariance_of_torus_commutator_bounds
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (hZr : B.LocalTorusRootCompatible hZ) :
    LocalMoyPrasadEquivariance B hZ :=
  B.localMoyPrasadEquivariance_of_normality hZ
    (B.localMoyPrasadNormality_of_torus_commutator_bounds hZ hZcomm hZ2 hZr)
    (fun n r => B.centralizerTorusImage_isNormalizerStable hZ n n.property r)

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
