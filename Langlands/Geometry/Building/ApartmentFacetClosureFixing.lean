import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.ChamberSharpCore
import Langlands.Geometry.Building.AffineTorsorFacetVertices
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.LinearAlgebra.RootFaceReflection

/-! # Fixing segments and closed facets in the reduced quotient over any field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- Evaluation of the opposite character. -/
theorem eval_neg_character_apply (b : characterLattice S) (w : V S) :
    eval S (-b) w = -eval S b w := by
  induction w using TensorProduct.inductionOn with
  | tmul s ν => simp [map_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]

omit [Mono i.hom.hom.left] in
/-- For every `w ∈ V(S)` there is a generic cocharacter `ν` such that every relative root `b`
with `⟨b, ν⟩ > 0` satisfies `b(w) ≥ 0`. -/
theorem exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (w : V S) :
    ∃ ν : cocharacterLattice S, IsGenericCocharacter i ν ∧
      ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hfin := hT.finite_relativeRoots i
  obtain ⟨ν₀, hν₀⟩ := hT.exists_genericCocharacter i
  obtain ⟨mu, hmu⟩ := Langlands.LinearAlgebra.RootFaceCone.exists_int_sign_realization
    hfin.toFinset (fun b => latticePairing S (-b)) (fun b => -eval S b)
    (fun b t n => by
      rw [LinearMap.neg_apply, eval_tmul, map_neg, LinearMap.neg_apply, Int.cast_neg, mul_neg]) w
  set M : ℤ := 1 + ∑ b ∈ hfin.toFinset, |latticePairing S b ν₀| with hMdef
  have hM : ∀ b ∈ relativeRoots i, |latticePairing S b ν₀| < M := by
    intro b hb
    have h := Finset.single_le_sum (f := fun b => |latticePairing S b ν₀|)
      (fun _ _ => abs_nonneg _) (hfin.mem_toFinset.2 hb)
    omega
  have hpair : ∀ b, latticePairing S b (M • mu + ν₀) =
      M * latticePairing S b mu + latticePairing S b ν₀ := by
    intro b
    rw [map_add, map_zsmul, smul_eq_mul]
  have hneg : ∀ b ∈ relativeRoots i, eval S b w < 0 → latticePairing S b mu < 0 := by
    intro b hb hw
    have h := (hmu b (hfin.mem_toFinset.2 hb)).2 (by
      rw [LinearMap.neg_apply]
      linarith)
    rw [map_neg, LinearMap.neg_apply] at h
    omega
  refine ⟨M • mu + ν₀, fun b hb => ?_, fun b hb hpos => ?_⟩
  · rw [hpair]
    have hq := abs_lt.1 (hM b hb)
    rcases lt_trichotomy (latticePairing S b mu) 0 with hp | hp | hp
    · nlinarith
    · rw [hp, mul_zero, zero_add]
      exact hν₀ b hb
    · nlinarith
  · by_contra hw
    have hp := hneg b hb (lt_of_not_ge hw)
    rw [hpair] at hpos
    have hq := abs_lt.1 (hM b hb)
    nlinarith

variable (D : KPApartmentData i ω)

/-- If `v n` fixes the image of `x` in the reduced quotient, with `v` in the unipotent group
of a generic cocharacter and `n ∈ N(k)`, then `n` fixes `x`. Any field; no apartment axioms. -/
theorem smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq_of_isMaximalSplitTorus
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {v : rationalPoints G}
    (hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (n : normalizerPoints i)
    (hx : (v * (n : rationalPoints G)) • D.apartmentMap x = D.apartmentMap x) :
    n • x = x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨m, hmx, s, hs, hgsm⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff D.sharpFixerFamily x _).1
      (MulAction.mem_stabilizer_iff.2 hx)
  obtain ⟨vw, ⟨v', hv', w, hw, rfl⟩, q, hq, hvwq⟩ := hsharp hs
  change v' * w * q = s at hvwq
  obtain ⟨-, hqN, hqx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hq
  set n' : normalizerPoints i := ⟨q, hqN⟩ * m * n⁻¹ with hn'def
  have hv'U := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hv').1
  have hwU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hw).1
  have hpos : v'⁻¹ * v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hv'U) hvU
  have hopp : w⁻¹ ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact Subgroup.inv_mem _ hwU
  have heq : (n' : rationalPoints G) = w⁻¹ * (v'⁻¹ * v) := by
    rw [hn'def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change q * (m : rationalPoints G) * (n : rationalPoints G)⁻¹ = _
    rw [← hvwq] at hgsm
    calc q * (m : rationalPoints G) * (n : rationalPoints G)⁻¹
        = w⁻¹ * v'⁻¹ * (v' * w * q * (m : rationalPoints G)) * (n : rationalPoints G)⁻¹ := by
          group
      _ = w⁻¹ * (v'⁻¹ * v) := by
          rw [← hgsm]
          group
  have hn' : n' = 1 :=
    normalizer_eq_one_of_unipotent_product i ν n' ⟨_, hopp⟩ ⟨_, hpos⟩ heq
  have hn : n = ⟨q, hqN⟩ * m := (mul_inv_eq_one.1 (hn'def ▸ hn')).symm
  rw [hn, mul_smul, hmx, hqx]

/-- The zero-depth root groups at `x` whose roots are nonnegative on `w` stay in the sharp
fixer of `w + x`. -/
theorem positiveChamberRootGroups_le_sharpFixer_vadd
    (x : D.Apartment) (ν : cocharacterLattice S) {w : V S}
    (hw : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b) ≤
      D.sharpFixer {(Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x} := by
  refine iSup_le fun b => ?_
  change D.filtration x b 0 ≤ _
  have hb := hw b b.2.1 b.2.2
  refine le_trans ?_ (D.rootFixer_singleton (b : characterLattice S) _ ▸
    D.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ _)
  intro t ht
  rw [filtration_mk_vadd]
  exact ⟨ht.1, le_trans (WithTop.coe_le_coe.2 (by linarith)) ht.2⟩

/-- **Two-point fixation.** An element of `G(k)` fixing the images of two apartment points in
the reduced quotient fixes the image of every point of the segment between them. Any field,
no apartment axioms; KP Lemma 7.7.4's Bruhat argument. -/
theorem smul_apartmentMap_lineMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {h : rationalPoints G} {y z : D.Apartment}
    (hy : h • D.apartmentMap y = D.apartmentMap y)
    (hz : h • D.apartmentMap z = D.apartmentMap z)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    h • D.apartmentMap (AffineMap.lineMap y z t) =
      D.apartmentMap (AffineMap.lineMap y z t) := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  obtain ⟨w, hw⟩ := exists_mk_vadd_eq y z
  have hp1 : AffineMap.lineMap y z t =
      (Submodule.Quotient.mk (t • w) : TranslationSpace i) +ᵥ y := by
    rw [AffineMap.lineMap_apply, hw, vadd_vsub, Submodule.Quotient.mk_smul]
  have hp2 : AffineMap.lineMap y z t =
      (Submodule.Quotient.mk ((1 - t) • -w) : TranslationSpace i) +ᵥ z := by
    rw [hp1, hw, vadd_vadd, ← Submodule.Quotient.mk_add]
    have hsum : (1 - t) • -w + w = t • w := by module
    rw [hsum]
  obtain ⟨ν, hν, hadapt⟩ := exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus hG hi w
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hadapt' : ∀ b ∈ relativeRoots i, 0 < latticePairing S b (-ν) →
      0 ≤ eval S b ((1 - t) • -w) := by
    intro b hb hpos
    have hnb : -b ∈ relativeRoots i := neg_mem_relativeRoots_of_rankOne hT hrank y hb
    have h1 := hadapt (-b) hnb (by rw [map_neg, LinearMap.neg_apply]; simpa using hpos)
    rw [eval_neg_character_apply] at h1
    rw [map_smul, map_neg, smul_eq_mul]
    nlinarith
  -- decompose `h` at `y`
  obtain ⟨m, hmy, s, hs, rfl⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff D.sharpFixerFamily y h).1
      (MulAction.mem_stabilizer_iff.2 hy)
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi y (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨_, ⟨u, hu, v, hv, rfl⟩, q, hq, hsq⟩ := hsharp hs
  change u * v * q = s at hsq
  obtain ⟨-, hqN, hqy⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hq
  set n : normalizerPoints i := ⟨q, hqN⟩ * m with hn
  have hh : s * (m : rationalPoints G) = u * (v * (n : rationalPoints G)) := by
    rw [hn, Subgroup.coe_mul, ← hsq]
    change u * v * q * (m : rationalPoints G) = u * (v * (q * (m : rationalPoints G)))
    group
  -- the positive factor fixes the ray from `y` through `z`
  have hu_fix : ∀ r : ℝ, 0 ≤ r →
      u • D.apartmentMap ((Submodule.Quotient.mk (r • w) : TranslationSpace i) +ᵥ y) =
        D.apartmentMap ((Submodule.Quotient.mk (r • w) : TranslationSpace i) +ᵥ y) := by
    intro r hr
    have hle := D.positiveChamberRootGroups_le_sharpFixer_vadd y ν (w := r • w)
      (fun b hb hpos => by
        rw [map_smul, smul_eq_mul]
        exact mul_nonneg hr (hadapt b hb hpos))
    exact D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer _ (hle hu))
  have huz : u • D.apartmentMap z = D.apartmentMap z := by
    have h1 := hu_fix 1 zero_le_one
    rwa [one_smul, ← hw] at h1
  -- the remaining factor `v n` fixes `z`
  have hvnz : (v * (n : rationalPoints G)) • D.apartmentMap z = D.apartmentMap z := by
    rw [hh, mul_smul] at hz
    exact (smul_left_cancel_iff u).1 (hz.trans huz.symm)
  have hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)) :=
    (D.positiveChamberRootGroups_le_sharpUnipotentPoints y (-ν) hv).1
  have hnz : n • z = z :=
    D.smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq_of_isMaximalSplitTorus hG hi z (-ν)
      hνneg hvU n hvnz
  have hny : n • y = y := by
    rw [hn, mul_smul, hmy, hqy]
  have hnzG : (n : rationalPoints G) • D.apartmentMap z = D.apartmentMap z := by
    rw [← D.apartmentMap_smul, hnz]
  have hvz : v • D.apartmentMap z = D.apartmentMap z := by
    rw [mul_smul, hnzG] at hvnz
    exact hvnz
  have hv' := D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq hG hi z (-ν)
    hνneg hvU hvz
  -- the negative factor fixes the ray from `z` through `y`
  have hv_fix : v • D.apartmentMap (AffineMap.lineMap y z t) =
      D.apartmentMap (AffineMap.lineMap y z t) := by
    rw [hp2]
    have hle := D.positiveChamberRootGroups_le_sharpFixer_vadd z (-ν) hadapt'
    exact D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer _ (hle hv'))
  -- the normalizer factor fixes the segment
  have hn_fix : (n : rationalPoints G) • D.apartmentMap (AffineMap.lineMap y z t) =
      D.apartmentMap (AffineMap.lineMap y z t) := by
    rw [← D.apartmentMap_smul]
    congr 1
    have := (D.normalizerAffineEquiv n).apply_lineMap y z t
    simp only [normalizerAffineEquiv_apply] at this
    rw [this, hny, hnz]
  have hu_p : u • D.apartmentMap (AffineMap.lineMap y z t) =
      D.apartmentMap (AffineMap.lineMap y z t) := by
    rw [hp1]
    exact hu_fix t ht0
  rw [hh, mul_smul, mul_smul, hn_fix, hv_fix, hu_p]

/-- The original quotient fixed locus in vector coordinates based at `o`. -/
def fixedApartmentCoordinates (h : rationalPoints G) (o : D.Apartment) :
    Set (TranslationSpace i) :=
  {v | h • D.apartmentMap (v +ᵥ o) = D.apartmentMap (v +ᵥ o)}

/-- The fixed locus of an actual rational element is convex in apartment coordinates. -/
theorem convex_fixedApartmentCoordinates
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : rationalPoints G) (o : D.Apartment) :
    Convex ℝ (D.fixedApartmentCoordinates h o) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy v hv
  rw [segment_eq_image_lineMap] at hv
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hv
  change h • D.apartmentMap (AffineMap.lineMap x y t +ᵥ o) =
    D.apartmentMap (AffineMap.lineMap x y t +ᵥ o)
  have hvadd := AffineMap.lineMap_vadd_lineMap x y o o t
  rw [AffineMap.lineMap_same_apply] at hvadd
  rw [hvadd]
  exact D.smul_apartmentMap_lineMap_eq hG hi hx hy ht0 ht1

/-- An element fixing the images of `v + o` for all `v` in a finite set fixes the image of
`v + o` for every `v` in its convex hull. -/
theorem smul_apartmentMap_vadd_eq_of_mem_convexHull
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {h : rationalPoints G} (o : D.Apartment) (s : Finset (TranslationSpace i))
    (hfix : ∀ v ∈ s, h • D.apartmentMap (v +ᵥ o) = D.apartmentMap (v +ᵥ o))
    {v : TranslationSpace i} (hv : v ∈ convexHull ℝ (s : Set (TranslationSpace i))) :
    h • D.apartmentMap (v +ᵥ o) = D.apartmentMap (v +ᵥ o) := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty =>
    simp only [Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hv
  | insert a s ha ih =>
    have hfa := hfix a (Finset.mem_insert_self a s)
    have hfs : ∀ v ∈ s, h • D.apartmentMap (v +ᵥ o) = D.apartmentMap (v +ᵥ o) :=
      fun v hv => hfix v (Finset.mem_insert_of_mem hv)
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp only [insert_empty_eq, Finset.coe_singleton, convexHull_singleton,
        Set.mem_singleton_iff] at hv
      rw [hv]
      exact hfa
    · rw [Finset.coe_insert, convexHull_insert (Finset.coe_nonempty.2 hne), mem_convexJoin]
        at hv
      obtain ⟨a', ha', b, hb, hab⟩ := hv
      rw [Set.mem_singleton_iff] at ha'
      subst a'
      rw [segment_eq_image_lineMap] at hab
      obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hab
      have hvadd := AffineMap.lineMap_vadd_lineMap a b o o c
      rw [AffineMap.lineMap_same_apply] at hvadd
      rw [hvadd]
      exact D.smul_apartmentMap_lineMap_eq hG hi hfa (ih hfs hb) hc0 hc1

/-- **Closed facets are fixed through their vertices.** For apartment data over any field
whose affine roots form an affine root system (rank zero allowed), an element of `G(k)` fixing
the images of all vertices of the closed facet of `p` fixes the image of the whole closure. -/
theorem smul_apartmentMap_eq_of_mem_facetClosure
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (p : D.Apartment) {h : rationalPoints G}
    (hfix : ∀ q : D.Apartment, q ∈ AffineRootSystem.facetClosure D.affineRoots p →
      AffineRootSystem.IsVertex D.affineRoots q →
      h • D.apartmentMap q = D.apartmentMap q)
    {x : D.Apartment} (hx : x ∈ AffineRootSystem.facetClosure D.affineRoots p) :
    h • D.apartmentMap x = D.apartmentMap x := by
  classical
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  let : Fintype (relativeRoots i) := (hT.finite_relativeRoots i).fintype
  let := RootTranslationMetric.normedAddCommGroup i
  let := RootTranslationMetric.normedSpace i
  have := RootTranslationMetric.finiteDimensional i
  let e : TranslationSpace i ≃ᵃ[ℝ] D.Apartment := AffineEquiv.vaddConst ℝ p
  have hΨ' := hΨ.transport e.symm
  have hconv := AffineRootSystem.convexHull_facetClosureVertexFinset hΨ' (e.symm p)
  have hxv : e.symm x ∈ convexHull ℝ
      (↑(AffineRootSystem.facetClosureVertexFinset hΨ' (e.symm p)) :
        Set (TranslationSpace i)) := by
    rw [hconv]
    exact (AffineRootSystem.mem_facetClosure_transportedRoots_iff e.symm D.affineRoots p x).2
      hx
  have key := D.smul_apartmentMap_vadd_eq_of_mem_convexHull hG hi p _ (fun v hv => by
      rw [AffineRootSystem.mem_facetClosureVertexFinset] at hv
      have hev : e v = v +ᵥ p := rfl
      have hsymm : e.symm (e v) = v := e.symm_apply_apply v
      rw [← hev]
      apply hfix
      · rw [← AffineRootSystem.mem_facetClosure_transportedRoots_iff e.symm D.affineRoots p,
          hsymm]
        exact hv.1
      · rw [← AffineRootSystem.isVertex_transportedRoots_iff e.symm D.affineRoots, hsymm]
        exact hv.2) hxv
  have hx' : e.symm x +ᵥ p = x := e.apply_symm_apply x
  rwa [hx'] at key

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- For integer-valuation building data whose affine roots form an affine root system, every
element of `G(k)` fixing the images of all vertices of a closed apartment facet fixes the
image of that whole closed facet in the original reduced quotient. -/
theorem smul_apartmentMap_eq_of_vertices_fixed
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) :
    ∀ (p : B.Apartment) (h : rationalPoints G),
      (∀ q : B.Apartment,
        q ∈ AffineRootSystem.facetClosure B.affineRoots p →
        AffineRootSystem.IsVertex B.affineRoots q →
        h • B.apartmentMap q = B.apartmentMap q) →
      ∀ x ∈ AffineRootSystem.facetClosure B.affineRoots p,
        h • B.apartmentMap x = B.apartmentMap x :=
  fun p _ hfix _ hx =>
    B.apartment.smul_apartmentMap_eq_of_mem_facetClosure B.isConnectedReductive
      B.isMaximalSplitTorus hΨ p hfix hx

end IntegerValuationBuildingData

end Langlands.Geometry.Building
