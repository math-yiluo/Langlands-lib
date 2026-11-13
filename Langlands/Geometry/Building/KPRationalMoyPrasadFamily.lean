import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.ApartmentRootRays
import Langlands.Geometry.Building.KPBuilding
import Langlands.Geometry.Building.FilteredRootProducts

/-!
# Centralizer filtrations from a rational Moy–Prasad family (KP §9.8)

KP §9.8 defines `Z(F)_r = Z(K)_r ∩ Z(F)` for the maximal unramified extension `K` of `F`,
and Lemma 9.8.1 and Proposition 9.8.3 derive the properties of this filtration from the
Moy–Prasad subgroups `G(K)_{x,r}` over `K`. This module isolates the `F`-level half of that
argument. A family `Q y r ⊆ G(F)` indexed by the points `y` of the apartment and by `r ≥ 0`
(meant: `Q y r = G(K)_{y,r} ∩ G(F)`) is a *rational Moy–Prasad family* if it satisfies the
ten properties of `IsRationalMoyPrasadFamily`. From such a family we build a centralizer
filtration `Z(F)_r = j⁻¹(Q x₀ r)` and prove that it satisfies the filtration axioms, is
open and is double-root commutator friendly. The existence of such a family is the
`K`-level input and is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- A family `Q y r` of subgroups of `G(F)`, for `y` in the apartment and `r ≥ 0`, with the
properties of `G(K)_{y,r} ∩ G(F)` that KP §9.8 uses (KP Lemma 9.8.1, Proposition 9.8.3 and
their proofs), `K` the maximal unramified extension of `F`. Write `j : Z(F) → G(F)`. -/
structure IsRationalMoyPrasadFamily (Q : P.Apartment → NNReal → Subgroup (rationalPoints G)) :
    Prop where
  /-- `Q y r` decreases in `r`. -/
  antitone : ∀ y, Antitone (Q y)
  /-- `U_{b,y,s} ⊆ Q y s` for every relative root `b`. -/
  filtration_le : ∀ (y : P.Apartment) (b : relativeRoots P.i) (s : NNReal),
    P.filtration y b.1 s ≤ Q y s
  /-- `[Q y r, Q y s] ⊆ Q y (r + s)`. -/
  commutator_le : ∀ (y : P.Apartment) (r s : NNReal), ⁅Q y r, Q y s⁆ ≤ Q y (r + s)
  /-- `n (Q y r) n⁻¹ ⊆ Q (n y) r` for `n ∈ N(F)`. -/
  conj_mem : ∀ (n : normalizerPoints P.i) (y : P.Apartment) (r : NNReal) (g : rationalPoints G),
    g ∈ Q y r → (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈ Q (n • y) r
  /-- Iwahori factorization at positive depth: if `v' j(z) v ∈ Q y t` with `t > 0`,
  `v' ∈ U_{-a}(F)` and `v ∈ U_a(F)`, then `j(z) ∈ Q y t`. -/
  map_mem_of_mul_mem : ∀ (y : P.Apartment) (a : relativeRoots P.i) (t : NNReal), 0 < t →
    ∀ v' ∈ P.rootGroup (-a.1), ∀ v ∈ P.rootGroup a.1, ∀ z : rationalPoints P.centralizer.Z,
      v' * rationalPoints.map P.centralizer.j z * v ∈ Q y t →
        rationalPoints.map P.centralizer.j z ∈ Q y t
  /-- The `Z`-part `j⁻¹(Q y r)` does not depend on `y`. -/
  comap_eq : ∀ (y y' : P.Apartment) (r : NNReal),
    (Q y r).comap (rationalPoints.map P.centralizer.j) =
      (Q y' r).comap (rationalPoints.map P.centralizer.j)
  /-- At depth `0` the `Z`-part is `Z(F)^0`. -/
  comap_zero : ∀ y : P.Apartment,
    (Q y 0).comap (rationalPoints.map P.centralizer.j) = P.centralizerZero
  /-- The `Z`-parts are separated. -/
  iInf_comap : ∀ y : P.Apartment,
    ⨅ r, (Q y r).comap (rationalPoints.map P.centralizer.j) = ⊥
  /-- `U_a(F) ∩ Q y t ⊆ U_{a,y,t} U_{2a,y,t}`. -/
  mem_filtrationBlock : ∀ (y : P.Apartment) (a : relativeRoots P.i) (t : NNReal)
    (g : rationalPoints G), g ∈ P.rootGroup a.1 → g ∈ Q y t →
      g ∈ P.apartment.filtrationBlock y (fun _ => (t : ℝ)) a.1
  /-- The `Z`-parts are open in `Z(F)` for the point topology. -/
  isOpen :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine P.centralizer.Z.X.left := by
      have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
        P.centralizer.isClosedSubgroup
      exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
    letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
      rationalPointTopology F P.centralizer.Z.X
    ∀ (y : P.Apartment) (r : NNReal),
      IsOpen (((Q y r).comap (rationalPoints.map P.centralizer.j) : Subgroup _) :
        Set (rationalPoints P.centralizer.Z))

/-! ### Translations of the apartment along a root -/

/-- For a relative root `a` and `c ∈ ℝ`, some point `y` of the apartment satisfies
`y_a = x_a + c` and `y_{-a} = x_{-a} - c`: translate `x` by `(c/2)` times a coroot vector
of `a` (KP Lemma 6.1.6). -/
theorem exists_vadd_val_root (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    (a : relativeRoots P.i) (c : ℝ) :
    ∃ y : P.Apartment, ∀ g : rationalPoints G,
      y.val a.1 g = x.val a.1 g + ((c : ℝ) : WithTop ℝ) ∧
        y.val (-a.1) g = x.val (-a.1) g + ((-c : ℝ) : WithTop ℝ) := by
  obtain ⟨v, hv, -⟩ := KPApartmentData.exists_integralRootCoroot P.apartment P.centralizer hP a
  refine ⟨(Submodule.Quotient.mk ((c / 2) • v) : TranslationSpace P.i) +ᵥ x, fun g => ⟨?_, ?_⟩⟩
  · rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, map_smul, smul_eq_mul, hv]
    congr 2
    ring
  · rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, eval_neg_char, map_smul,
      smul_eq_mul, hv]
    congr 2
    ring

/-- If `x_a(u) + x_{-a}(u') = r` is finite, both values are finite and `-a` is a relative
root. -/
theorem exists_real_vals_of_add_eq {x : P.Apartment} {a : relativeRoots P.i}
    {u u' : rationalPoints G} {r : ℝ}
    (h : ((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') :
    ∃ p q : ℝ, x.val a.1 u = p ∧ x.val (-a.1) u' = q ∧ p + q = r ∧
      -a.1 ∈ relativeRoots P.i := by
  have hne : x.val a.1 u + x.val (-a.1) u' ≠ ⊤ := h ▸ WithTop.coe_ne_top
  obtain ⟨hp, hq⟩ := WithTop.add_ne_top.1 hne
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.1 hp
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hq
  refine ⟨p, q, hp.symm, hq.symm, ?_, ?_⟩
  · rw [← hp, ← hq, ← WithTop.coe_add] at h
    exact (WithTop.coe_inj.1 h).symm
  · by_contra hna
    rw [x.isValuation.eq_top_of_not_mem_roots (-a.1) hna u'] at hq
    exact WithTop.coe_ne_top hq

namespace IsRationalMoyPrasadFamily

variable {P} {Q : P.Apartment → NNReal → Subgroup (rationalPoints G)}
  (hQ : P.IsRationalMoyPrasadFamily Q)

include hQ

/-- An element of `U_b(F)` with `y_b(g) = t` lies in `Q y t`. -/
theorem mem_of_val_eq {y : P.Apartment} (b : relativeRoots P.i) {g : rationalPoints G}
    (hg : g ∈ P.rootGroup b.1) {t : NNReal} (h : y.val b.1 g = (((t : ℝ) : ℝ) : WithTop ℝ)) :
    g ∈ Q y t :=
  hQ.filtration_le y b t ⟨hg, le_of_eq h.symm⟩

/-- `u'⁻¹ u u' u⁻¹ ∈ Q y (r + s)` for `u' ∈ Q y r` and `u ∈ Q y s`. -/
theorem commutator_mem {y : P.Apartment} {r s : NNReal} {u u' : rationalPoints G}
    (hu' : u' ∈ Q y r) (hu : u ∈ Q y s) : u'⁻¹ * u * u' * u⁻¹ ∈ Q y (r + s) := by
  have h := hQ.commutator_le y r s
    (Subgroup.commutator_mem_commutator ((Q y r).inv_mem hu') hu)
  rwa [commutatorElement_def, inv_inv] at h

omit hQ in
/-- The centralizer filtration `Z(F)_r = j⁻¹(Q x₀ r)` of a rational Moy–Prasad family, at a
base point `x₀` of the apartment. -/
def centralizerFiltration (hQ : P.IsRationalMoyPrasadFamily Q) (x₀ : P.Apartment) :
    P.CentralizerFiltration where
  filtration r := (Q x₀ r).comap (rationalPoints.map P.centralizer.j)
  filtration_zero := hQ.comap_zero x₀
  antitone _ _ h := Subgroup.comap_mono (hQ.antitone x₀ h)
  separated := hQ.iInf_comap x₀

/-- `z ∈ Z(F)_r` iff `j(z) ∈ Q y r`, for every point `y`. -/
theorem mem_filtration_iff (x₀ y : P.Apartment) (r : NNReal)
    (z : rationalPoints P.centralizer.Z) :
    z ∈ (hQ.centralizerFiltration x₀).filtration r ↔
      rationalPoints.map P.centralizer.j z ∈ Q y r := by
  change z ∈ (Q x₀ r).comap (rationalPoints.map P.centralizer.j) ↔ _
  rw [hQ.comap_eq x₀ y r]
  rfl

/-- The `Z`-component of an element of `Q y t ∩ U_{-a}(F) j(Z(F)) U_a(F)` lies in `Z(F)_t`,
for `t > 0`. -/
theorem mem_filtration_of_mul_mem (x₀ y : P.Apartment) (a : relativeRoots P.i) {t : NNReal}
    (ht : 0 < t) {g v' v : rationalPoints G} {z : rationalPoints P.centralizer.Z}
    (hv' : v' ∈ P.rootGroup (-a.1)) (hv : v ∈ P.rootGroup a.1)
    (heq : g = v' * rationalPoints.map P.centralizer.j z * v) (hg : g ∈ Q y t) :
    z ∈ (hQ.centralizerFiltration x₀).filtration t := by
  rw [hQ.mem_filtration_iff x₀ y]
  exact hQ.map_mem_of_mul_mem y a t ht v' hv' v hv z (heq ▸ hg)

/-! ### The filtration axioms -/

theorem isCommutatorFriendly (hP : P.SatisfiesApartmentAxioms) (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsCommutatorFriendly := by
  intro x a u u' hu _ hu' _ r hr hsum v' v z hv' hv heq
  obtain ⟨p, q, hp, hq, hpq, hna⟩ := P.exists_real_vals_of_add_eq hsum
  obtain ⟨y, hy⟩ := P.exists_vadd_val_root hP x a (-p)
  have hyu : y.val a.1 u = (((0 : NNReal) : ℝ) : WithTop ℝ) := by
    rw [(hy u).1, hp, ← WithTop.coe_add, NNReal.coe_zero, add_neg_cancel]
  have hyu' : y.val (-a.1) u' = ((r : ℝ) : WithTop ℝ) := by
    rw [(hy u').2, hq, ← WithTop.coe_add, neg_neg, ← hpq, add_comm]
  have hmem := hQ.commutator_mem (hQ.mem_of_val_eq ⟨-a.1, hna⟩ hu' hyu')
    (hQ.mem_of_val_eq a hu hyu)
  rw [add_zero] at hmem
  exact hQ.mem_filtration_of_mul_mem x₀ y a hr hv' hv heq hmem

theorem isDoubleRootCommutatorFriendly (hP : P.SatisfiesApartmentAxioms) (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsDoubleRootCommutatorFriendly := by
  intro x a u u' hu hu1 hu' hu'1 hdouble r hr hsum v' v z hv' hv heq
  obtain ⟨p, q, hp, hq, hpq, hna⟩ := P.exists_real_vals_of_add_eq hsum
  have h2r : (0 : NNReal) < 2 * r := mul_pos two_pos hr
  have h2 : ((((2 * r : NNReal) : ℝ) : WithTop ℝ)) = 2 • ((r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_nsmul, NNReal.coe_mul, NNReal.coe_two, two_nsmul, two_mul]
  rcases hdouble with hd | hd
  · -- `u ∈ U_{2a}(F)`: move to `y` with `y_a(u) = r` and `y_{-a}(u') = 0`.
    by_cases h2a : 2 • a.1 ∈ relativeRoots P.i
    · have hu2 : u ∈ rootGroupPoints P.i (2 • a.1) := by
        simpa only [ValuationBuildingData.doubleRootGroup, doubleRootGroupPoints,
          ite_eq_left h2a] using hd
      obtain ⟨y, hy⟩ := P.exists_vadd_val_root hP x a q
      have hyu : y.val a.1 u = ((r : ℝ) : WithTop ℝ) := by
        rw [(hy u).1, hp, ← WithTop.coe_add, hpq]
      have hyu2 : y.val (2 • a.1) u = ((((2 * r : NNReal) : ℝ) : WithTop ℝ)) := by
        rw [y.isValuation.double a.1 a.2 h2a u hu2, hyu, h2]
      have hyu' : y.val (-a.1) u' = (((0 : NNReal) : ℝ) : WithTop ℝ) := by
        rw [(hy u').2, hq, ← WithTop.coe_add, NNReal.coe_zero, add_neg_cancel]
      have hmem := hQ.commutator_mem (hQ.mem_of_val_eq ⟨-a.1, hna⟩ hu' hyu')
        (hQ.mem_of_val_eq ⟨2 • a.1, h2a⟩ hu2 hyu2)
      rw [zero_add] at hmem
      exact hQ.mem_filtration_of_mul_mem x₀ y a h2r hv' hv heq hmem
    · have hbot : u ∈ (⊥ : Subgroup (rationalPoints G)) := by
        simpa only [ValuationBuildingData.doubleRootGroup, doubleRootGroupPoints,
          ite_eq_right h2a] using hd
      exact (hu1 (Subgroup.mem_bot.1 hbot)).elim
  · -- `u' ∈ U_{-2a}(F)`: move to `y` with `y_a(u) = 0` and `y_{-a}(u') = r`.
    by_cases h2a : 2 • (-a.1) ∈ relativeRoots P.i
    · have hu2 : u' ∈ rootGroupPoints P.i (2 • (-a.1)) := by
        simpa only [ValuationBuildingData.doubleRootGroup, doubleRootGroupPoints,
          ite_eq_left h2a] using hd
      obtain ⟨y, hy⟩ := P.exists_vadd_val_root hP x a (-p)
      have hyu : y.val a.1 u = (((0 : NNReal) : ℝ) : WithTop ℝ) := by
        rw [(hy u).1, hp, ← WithTop.coe_add, NNReal.coe_zero, add_neg_cancel]
      have hyu' : y.val (-a.1) u' = ((r : ℝ) : WithTop ℝ) := by
        rw [(hy u').2, hq, ← WithTop.coe_add, neg_neg, ← hpq, add_comm]
      have hyu2 : y.val (2 • (-a.1)) u' = ((((2 * r : NNReal) : ℝ) : WithTop ℝ)) := by
        rw [y.isValuation.double (-a.1) hna h2a u' hu2, hyu', h2]
      have hmem := hQ.commutator_mem (hQ.mem_of_val_eq ⟨2 • (-a.1), h2a⟩ hu2 hyu2)
        (hQ.mem_of_val_eq a hu hyu)
      rw [add_zero] at hmem
      exact hQ.mem_filtration_of_mul_mem x₀ y a h2r hv' hv heq hmem
    · have hbot : u' ∈ (⊥ : Subgroup (rationalPoints G)) := by
        simpa only [ValuationBuildingData.doubleRootGroup, doubleRootGroupPoints,
          ite_eq_right h2a] using hd
      exact (hu'1 (Subgroup.mem_bot.1 hbot)).elim

/-- Conjugation by `n ∈ N(F)` maps `j(Z(F)_r)` into itself. -/
theorem conj_image_le (x₀ : P.Apartment) (n : normalizerPoints P.i) (r : NNReal) :
    ((hQ.centralizerFiltration x₀).image r).map
        (MulAut.conj (n : rationalPoints G)).toMonoidHom ≤
      (hQ.centralizerFiltration x₀).image r := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hc : (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
      (n : rationalPoints G)⁻¹ ∈ centralizerPoints P.i :=
    conj_mem_centralizerPoints P.i n.2
      (map_mem_centralizerPoints P.centralizer.isRepresentedBy z)
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hc
  obtain ⟨w, hw⟩ := hc
  let z' : rationalPoints P.centralizer.Z := w
  have hz'' : rationalPoints.map P.centralizer.j z' = (n : rationalPoints G) *
      rationalPoints.map P.centralizer.j z * (n : rationalPoints G)⁻¹ := by
    rw [rationalPoints.map_apply]
    exact hw
  have hz0 : z ∈ (hQ.centralizerFiltration x₀).filtration r := hz
  refine ⟨z', ?_, ?_⟩
  · show z' ∈ (hQ.centralizerFiltration x₀).filtration r
    rw [hQ.mem_filtration_iff x₀ (n • x₀), hz'']
    exact hQ.conj_mem n x₀ r _ ((hQ.mem_filtration_iff x₀ x₀ r z).1 hz0)
  · rw [hz'']
    rfl

theorem isNormalizerStable (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsNormalizerStable := by
  intro n hn r
  refine le_antisymm (hQ.conj_image_le x₀ ⟨n, hn⟩ r) fun g hg => ?_
  refine ⟨_, hQ.conj_image_le x₀ (⟨n, hn⟩⁻¹) r ⟨g, hg, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv, inv_inv]
  group

theorem isCommutatorFiltered (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsCommutatorFiltered := by
  intro r s
  rw [Subgroup.commutator_le]
  intro g hg h hh
  change rationalPoints.map P.centralizer.j ⁅g, h⁆ ∈ Q x₀ (r + s)
  rw [map_commutatorElement]
  exact hQ.commutator_le x₀ r s (Subgroup.commutator_mem_commutator hg hh)

theorem isRootCompatible (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsRootCompatible := by
  intro x a r s _ ⟨z, hz, hzg⟩ u hu
  subst hzg
  have hzx : rationalPoints.map P.centralizer.j z ∈ Q x r :=
    (hQ.mem_filtration_iff x₀ x r z).1 hz
  have hux : u ∈ Q x s := hQ.filtration_le x a s hu
  have hmem : rationalPoints.map P.centralizer.j z * u *
      (rationalPoints.map P.centralizer.j z)⁻¹ * u⁻¹ ∈ Q x (r + s) := by
    have h := hQ.commutator_le x r s (Subgroup.commutator_mem_commutator hzx hux)
    rwa [commutatorElement_def] at h
  have hconj : rationalPoints.map P.centralizer.j z * u *
      (rationalPoints.map P.centralizer.j z)⁻¹ ∈ P.rootGroup a.1 := by
    have h := conj_mem_rootGroupPoints (P.centralizer.toNormalizer z) hu.1
    rwa [weylAction_centralizerToNormalizer] at h
  have hroot : rationalPoints.map P.centralizer.j z * u *
      (rationalPoints.map P.centralizer.j z)⁻¹ * u⁻¹ ∈ P.rootGroup a.1 :=
    (P.rootGroup a.1).mul_mem hconj ((P.rootGroup a.1).inv_mem hu.1)
  exact hQ.mem_filtrationBlock x a (r + s) _ hroot hmem

theorem satisfiesFiltrationAxioms (hP : P.SatisfiesApartmentAxioms) (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).SatisfiesFiltrationAxioms :=
  ⟨hQ.isCommutatorFriendly hP x₀, hQ.isNormalizerStable x₀, hQ.isCommutatorFiltered x₀,
    hQ.isRootCompatible x₀⟩

theorem isOpenFiltration (x₀ : P.Apartment) :
    (hQ.centralizerFiltration x₀).IsOpenFiltration :=
  hQ.isOpen x₀

end IsRationalMoyPrasadFamily

/-- A rational Moy–Prasad family gives a centralizer filtration that satisfies the filtration
axioms, is open and is double-root commutator friendly. -/
theorem exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily
    (hP : P.SatisfiesApartmentAxioms) {Q : P.Apartment → NNReal → Subgroup (rationalPoints G)}
    (hQ : P.IsRationalMoyPrasadFamily Q) :
    ∃ Zf : P.CentralizerFiltration, Zf.SatisfiesFiltrationAxioms ∧ Zf.IsOpenFiltration ∧
      Zf.IsDoubleRootCommutatorFriendly := by
  let x₀ : P.Apartment := Classical.arbitrary P.Apartment
  exact ⟨hQ.centralizerFiltration x₀, hQ.satisfiesFiltrationAxioms hP x₀,
    hQ.isOpenFiltration x₀, hQ.isDoubleRootCommutatorFriendly hP x₀⟩

end Langlands.Geometry.Building.ParahoricBuildingData
