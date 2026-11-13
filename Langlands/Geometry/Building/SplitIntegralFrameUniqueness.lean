import Langlands.Geometry.Building.SplitIntegralFrame
import Langlands.Geometry.Building.GenericSpecialFixedPoint
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Geometry.Building.RegularUnitExistence

/-!
# Uniqueness of the fixed point of a split integral frame

For a split integral frame `F` on integer-valued building data `B`, the point `x` at which
every root value `φ_a(u_a(1))` vanishes is the only point of the reduced building fixed by
`F.K`, provided `G(k) = F.K · P(k)` for the dynamic parabolic `P` of a generic cocharacter
`ν`, and some unit `c` makes every `c^{⟨b, ν⟩} - 1` (`b` positive) a unit.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {B : IntegerValuationBuildingData v G}

/-- The cocharacter `ν` evaluated at a unit of valuation one lies in the common kernel of
the character valuations of the torus. -/
theorem cocharacterPoints_mem_characterValuationKernel {c : kˣ} (hc : v (c : k) = 1)
    (ν : cocharacterLattice B.S) :
    CocharacterUniformizer.cocharacterPoints k B.S ν c ∈
      characterValuationKernel v B.S.toGrp := by
  rw [mem_characterValuationKernel]
  intro χ
  have h := CocharacterUniformizer.rationalCharacterEval_cocharacterPoints k B.S
    (rationalCharacters.equivCharacterLattice B.S χ) ν c
  rw [AddEquiv.symm_apply_apply] at h
  rw [h, Units.val_zpow_eq_zpow_val, map_zpow₀, hc, one_zpow]

/-- The image `i(ν(c)) ∈ G(k)` of a unit `c` under a cocharacter `ν` of the torus of `B`.
For suitable `c` it is the regular centralizer element of the uniqueness argument. -/
def cocharacterPoint (B : IntegerValuationBuildingData v G) (ν : cocharacterLattice B.S)
    (c : kˣ) : rationalPoints G :=
  rationalPoints.map B.i (CocharacterUniformizer.cocharacterPoints k B.S ν c)

theorem cocharacterPoint_eq_map_j (ν : cocharacterLattice B.S) (c : kˣ) :
    B.cocharacterPoint ν c = rationalPoints.map B.centralizer.j
      (rationalPoints.map B.centralizer.s (CocharacterUniformizer.cocharacterPoints k B.S ν c)) :=
  (B.coe_torusNormalizer _).symm

theorem cocharacterPoint_mem_centralizerPoints (ν : cocharacterLattice B.S) (c : kˣ) :
    B.cocharacterPoint ν c ∈ centralizerPoints B.i := by
  rw [cocharacterPoint_eq_map_j]
  exact map_mem_centralizerPoints B.centralizer.isRepresentedBy _

/-- For a unit `c` of valuation one, `i(ν(c))` fixes every apartment point. -/
theorem cocharacterPoint_smul_eq_self {c : kˣ} (hc : v (c : k) = 1) (ν : cocharacterLattice B.S)
    (x : B.Apartment) :
    (⟨B.cocharacterPoint ν c, centralizerPoints_le_normalizerPoints B.i
      (cocharacterPoint_mem_centralizerPoints ν c)⟩ : normalizerPoints B.i) • x = x := by
  have hN : (⟨B.cocharacterPoint ν c, centralizerPoints_le_normalizerPoints B.i
      (cocharacterPoint_mem_centralizerPoints ν c)⟩ : normalizerPoints B.i) =
      B.centralizer.toNormalizer
        (rationalPoints.map B.centralizer.s (CocharacterUniformizer.cocharacterPoints k B.S ν c)) :=
    Subtype.ext (cocharacterPoint_eq_map_j ν c)
  rw [hN]
  exact ((B.mem_characterValuationKernel_iff_smul_eq _ x).mp
    (IntegerValuation.map_mem_characterValuationKernel v B.centralizer.s
      (cocharacterPoints_mem_characterValuationKernel hc ν))).2

namespace SplitIntegralFrame

variable (F : B.SplitIntegralFrame)

theorem cocharacterPoint_mem_K {c : kˣ} (hc : v (c : k) = 1) (ν : cocharacterLattice B.S) :
    B.cocharacterPoint ν c ∈ F.K := by
  rw [cocharacterPoint_eq_map_j]
  exact F.centralizer_mem_K _ (IntegerValuation.map_mem_characterValuationKernel v
    B.centralizer.s (cocharacterPoints_mem_characterValuationKernel hc ν))

omit [IsAffineHom G.X.hom] in
theorem order_eq_zero_of_valuation_eq_one {c : kˣ} (hc : v (c : k) = 1) :
    IntegerValuation.order v c = 0 := by
  rw [IntegerValuation.order, (IntegerValuation.orderUnits_eq_one_iff v c).mpr hc]
  simp

omit [IsAffineHom G.X.hom] in
theorem order_mul (c d : kˣ) :
    IntegerValuation.order v (c * d) = IntegerValuation.order v c +
      IntegerValuation.order v d := by
  simp only [IntegerValuation.order, map_mul, toAdd_mul, Int.cast_add]

include F in
/-- The value condition of the abstract uniqueness theorem for the image of a torus point
`t` whose positive root values `b(t)` satisfy `v (b(t) - 1) = 1`. -/
theorem val_inv_mul_conj (t : rationalPoints B.S.toGrp) {b : characterLattice B.S}
    (hb : b ∈ relativeRoots B.i) (htb : v ((B.charEval b t : k) - 1) = 1)
    {h : rationalPoints G} (hh : h ∈ rootGroupPoints B.i b) (z : B.Apartment) :
    z.val b (h⁻¹ * (rationalPoints.map B.i t * h * (rationalPoints.map B.i t)⁻¹)) =
      z.val b h := by
  obtain ⟨e, rfl⟩ := F.u_surjective b hb h hh
  rw [F.torus_conj b hb t e]
  have hinv : (F.u b e)⁻¹ = F.u b (-e) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← F.u_add b hb, neg_add_cancel, F.u_zero hb]
  rw [hinv, ← F.u_add b hb]
  have hcomb : -e + (B.charEval b t : k) * e = ((B.charEval b t : k) - 1) * e := by ring
  rw [hcomb]
  by_cases he : e = 0
  · rw [he, mul_zero]
  have hβ : (B.charEval b t : k) - 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at htb
    exact zero_ne_one htb
  set β : kˣ := Units.mk0 _ hβ with hβ_def
  set E : kˣ := Units.mk0 e he with hE_def
  have h1 : ((B.charEval b t : k) - 1) * e = ((β * E : kˣ) : k) := by
    simp only [hβ_def, hE_def, Units.val_mul, Units.val_mk0]
  have h2 : e = (E : k) := by simp only [hE_def, Units.val_mk0]
  rw [h1, h2, F.val_u z hb, F.val_u z hb, order_mul, order_eq_zero_of_valuation_eq_one
    (by simpa only [hβ_def, Units.val_mk0] using htb), zero_add]

/-- **Uniqueness for a split integral frame.** Let `x` be a point at which every root value
of the frame vanishes. Assume the Iwasawa covering `G(k) = F.K · P(k)` for the dynamic
parabolic `P` of a generic cocharacter `ν`, and a unit `c` such that
`v (c^{⟨b, ν⟩} - 1) = 1` for every root `b` positive on `ν`. Then the image of `x` is the
only point of the reduced building fixed by `F.K`. -/
theorem eq_apartmentMap_of_forall_smul_eq (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0)
    (ν : cocharacterLattice B.S) (hν : IsGenericCocharacter B.i ν)
    (hIw : ∀ g : rationalPoints G, ∃ κ ∈ F.K,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ B.i)).carrier (Over.mk (𝟙 _)),
        g = κ * p)
    {c : kˣ} (hc : v (c : k) = 1)
    (hcreg : ∀ b ∈ positiveRelativeRoots B.i ν,
      v (((c : k) ^ (latticePairing B.S b ν).toNat) - 1) = 1)
    (y : B.ReducedBuilding) (hy : ∀ g ∈ F.K, g • y = y) : y = B.apartmentMap x := by
  set t := CocharacterUniformizer.cocharacterPoints k B.S ν c with ht_def
  have hsK : B.cocharacterPoint ν c ∈ F.K := F.cocharacterPoint_mem_K hc ν
  have hsC := cocharacterPoint_mem_centralizerPoints (B := B) ν c
  have hsx := cocharacterPoint_smul_eq_self (B := B) hc ν x
  have hKx : ∀ g ∈ F.K, g • B.apartmentMap x = B.apartmentMap x := by
    intro g hg
    rw [F.K_eq_oneStabilizer hk hx] at hg
    exact (B.mem_oneStabilizer.mp hg).2
  refine KPApartmentData.eq_apartmentMap_of_forall_smul_eq B.apartment B.isConnectedReductive
    B.isMaximalSplitTorus F.two_smul_not_mem x F.K hKx ν hν hIw hsK hsC hsx ?_ ?_ ?_ y hy
  · intro b hb h hh z
    refine F.val_inv_mul_conj t hb.1 ?_ hh z
    have hpos := hb.2
    rw [ht_def, CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
      Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg hpos.le, zpow_natCast]
    exact hcreg b hb
  · intro a ha g hg
    exact F.sharpFixer_le_K hx (B.apartment.filtration_le_sharpFixer x ha hg)
  · intro a ha
    exact ⟨F.u a 1, F.u_mem a ha 1, by rw [F.val_u_one x ha, hx a ha]; rfl⟩

/-- **Uniqueness for a split integral frame over a valuation with infinite residue field.**
The unit `c` of the general theorem, and the unit `d` with `d ^ 2 ≠ 1` used by the frame,
exist because the residue field is infinite. -/
theorem eq_apartmentMap_of_forall_smul_eq_of_infinite
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0)
    (ν : cocharacterLattice B.S) (hν : IsGenericCocharacter B.i ν)
    (hIw : ∀ g : rationalPoints G, ∃ κ ∈ F.K,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ B.i)).carrier (Over.mk (𝟙 _)),
        g = κ * p)
    (y : B.ReducedBuilding) (hy : ∀ g ∈ F.K, g • y = y) : y = B.apartmentMap x := by
  classical
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.1.1
  have hfin : (positiveRelativeRoots B.i ν).Finite :=
    (hS.finite_relativeRoots B.i).subset (fun _ h => h.1)
  obtain ⟨c, hc, hcN⟩ := exists_unit_valuation_pow_sub_one_eq_one v
    (hfin.toFinset.image fun b => (latticePairing B.S b ν).toNat) (by
      intro m hm
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
      have := ((Set.Finite.mem_toFinset hfin).mp hb).2
      omega)
  exact F.eq_apartmentMap_of_forall_smul_eq (exists_unit_sq_ne_one v) hx ν hν hIw hc
    (fun b hb => hcN _ (Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset hfin).mpr hb))) y hy

end SplitIntegralFrame

end IntegerValuationBuildingData

end Langlands.Geometry.Building
