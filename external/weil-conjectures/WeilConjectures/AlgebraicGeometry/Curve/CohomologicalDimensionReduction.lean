/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Cohomological dimension of a curve: reduction to integral curves

Let `C` be a curve over an algebraically closed field `k` and `F` a torsion étale sheaf on `C`.
We show `Hᵠ(C, F) = 0` for `q ≥ 3` by reduction to integral curves, where it is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_isIntegral`
(blueprint `theorem-cohomology-curves`, Step 1).

Let `cₚ : Zₚ ⟶ C` be the irreducible components of `C` with their reduced structure. Away from
the finite set `S` of closed points lying on two components, `C` is covered by the disjoint open
pieces `Vₚ` of the components, over which `cₚ` is a surjective closed immersion, hence a
universal homeomorphism. So the units assemble to a map `F ⟶ ⨁ₚ cₚ_* cₚ^* F` which is an
isomorphism away from `S`, hence bijective on `Hᵠ` for `q ≥ 2`; and
`Hᵠ(C, cₚ_* cₚ^* F) = Hᵠ(Zₚ, cₚ^* F)` vanishes for `q ≥ 3` since `Zₚ` is an integral curve.
No reducedness of `C` is needed: the closed immersions `cₚ` need not be isomorphisms over `Vₚ`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_generic`: `Hᵠ(C, F) = 0` for
  `q ≥ 3`, `C` any curve over an algebraically closed field and `F` a torsion sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

open Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Cohomological dimension of a curve, by reduction to integral curves.** Let `C` be a curve
over an algebraically closed field `k`. Then `Hᵠ(C, F) = 0` for every torsion étale sheaf `F` on
`C` and `q ≥ 3`. Let `cₚ : Zₚ ⟶ C` be the irreducible components with their reduced structure.
The units `F ⟶ cₚ_* cₚ^* F` assemble to a map `F ⟶ ⨁ₚ cₚ_* cₚ^* F` which is an isomorphism away
from the finitely many closed points lying on two components
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_of_isUniversalHomeomorphism`), hence
bijective on `Hᵠ` (`AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map`), and
`Hᵠ(C, cₚ_* cₚ^* F) = Hᵠ(Zₚ, cₚ^* F) = 0` by the integral case
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_isIntegral`.
(blueprint: `theorem-cohomology-curves`, Step 1) -/
theorem subsingleton_sheafH_of_three_le_generic (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  let ι := ↥(irreducibleComponents C)
  have : Finite ι := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  have := Fintype.ofFinite ι
  -- the irreducible components `Z p`, with their reduced structure
  let I (p : ι) : C.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨p.1, isClosed_of_mem_irreducibleComponents _ p.2⟩
  let Z (p : ι) : Scheme.{u} := (I p).subscheme
  let c (p : ι) : Z p ⟶ C := (I p).subschemeι
  have hrange (p : ι) : Set.range (c p).base = p.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hirr (p : ι) : IrreducibleSpace (Z p) := by
    let h := (c p).isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range (c p).base) :=
      Subtype.irreducibleSpace ((hrange p).symm ▸ p.2.1)
    rw [irreducibleSpace_def]
    have := (IrreducibleSpace.isIrreducible_univ _).image h.symm h.symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective h.symm.surjective] at this
  have hint (p : ι) : IsIntegral (Z p) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcurve (p : ι) : IsCurve (c p ≫ f) :=
    { krullDim_le_one := ((c p).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans
        (IsCurve.krullDim_le_one (f := f)) }
  -- every point lies on a component
  have hcov (x : C) : ∃ p : ι, x ∈ p.1 := by
    obtain ⟨u, hu, hxu⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    exact ⟨⟨u, hu⟩, hxu rfl⟩
  -- the good locus of each component: where it meets no other component
  let O (p : ι) : Set (Z p) := ⋂ q ∈ Finset.univ.filter (· ≠ p), ((c p).base ⁻¹' q.1)ᶜ
  have hOopen (p : ι) : IsOpen (O p) := isOpen_biInter_finset fun q _ ↦
    ((isClosed_of_mem_irreducibleComponents _ q.2).preimage (c p).continuous).isOpen_compl
  have hOne (p : ι) : (O p).Nonempty := by
    -- the generic point of `Z p` lies on no other component
    refine ⟨genericPoint (Z p), ?_⟩
    simp only [O, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hqp hmem
    have hle : p.1 ⊆ q.1 := by
      rw [← hrange p, ← Set.image_univ, ← (genericPoint_spec (Z p)).def]
      refine (image_closure_subset_closure_image (c p).continuous).trans
        (closure_minimal ?_ (isClosed_of_mem_irreducibleComponents _ q.2))
      simpa using hmem
    exact hqp (Subtype.ext ((p.2.2 q.2.1 hle).antisymm hle))
  have hnoeth (p : ι) : IsNoetherian (Z p) := by
    have : IsLocallyNoetherian (Z p) := LocallyOfFiniteType.isLocallyNoetherian (c p ≫ f)
    have : CompactSpace (Z p) := (quasiCompact_iff_compactSpace (c p ≫ f)).mp inferInstance
    exact ⟨⟩
  have hdimZ (p : ι) : topologicalKrullDim (Z p) ≤ 1 := IsCurve.krullDim_le_one (f := c p ≫ f)
  have hOfin (p : ι) : (O p)ᶜ.Finite :=
    (hOopen p).finite_compl_of_topologicalKrullDim_le_one (hdimZ p) (hOne p)
  have hOcl (p : ι) (z : Z p) (hz : z ∉ O p) : IsClosed ({z} : Set (Z p)) :=
    (hOopen p).isClosed_singleton_of_mem_compl (hdimZ p) (hOne p) hz
  -- the bad set `S`
  let S : Set C := ⋃ p, (c p).base '' (O p)ᶜ
  have hSfin : S.Finite := Set.finite_iUnion fun p ↦ (hOfin p).image _
  have hScl (x : C) (hx : x ∈ S) : IsClosed ({x} : Set C) := by
    obtain ⟨p, z, hz, rfl⟩ := Set.mem_iUnion.1 hx
    simpa using (c p).isClosedEmbedding.isClosedMap _ (hOcl p z hz)
  have hSclosed : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion hScl
  let U : C.Opens := ⟨Sᶜ, hSclosed.isOpen_compl⟩
  -- the pieces `V p` of `U`, away from the other components
  let V (p : ι) : C.Opens := ⟨Sᶜ ∩ ⋂ q ∈ Finset.univ.filter (· ≠ p), (q.1)ᶜ,
    hSclosed.isOpen_compl.inter (isOpen_biInter_finset fun q _ ↦
      (isClosed_of_mem_irreducibleComponents _ q.2).isOpen_compl)⟩
  have hVU (p : ι) : V p ≤ U := fun _ hx ↦ hx.1
  have hVZ (p : ι) (x : C) (hx : x ∈ V p) : x ∈ Set.range (c p).base := by
    obtain ⟨q, hq⟩ := hcov x
    by_cases hqp : q = p
    · exact hqp ▸ (hrange q).symm ▸ hq
    · refine absurd hq ?_
      have := hx.2
      simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this q hqp
  have hUV (x : C) (hx : x ∈ U) : ∃ p, x ∈ V p := by
    obtain ⟨p, hp⟩ := hcov x
    refine ⟨p, hx, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hqp hxq
    obtain ⟨z, rfl⟩ : x ∈ Set.range (c p).base := (hrange p).symm ▸ hp
    refine hx (Set.mem_iUnion.2 ⟨p, z, fun hz ↦ ?_, rfl⟩)
    have := hz
    simp only [O, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this q hqp hxq
  have hdisj (p q : ι) (hqp : q ≠ p) :
      Disjoint (Set.range (V p).ι.base) (Set.range (c q).base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_right, hrange q]
    intro x hx hxV
    have := hxV.2
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this q hqp hx
  have huh (p : ι) : IsUniversalHomeomorphism (c p ∣_ V p) := by
    have : Surjective (c p ∣_ V p) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨z, hz⟩ := hVZ p y.1 y.2
      refine ⟨⟨z, show (c p).base z ∈ V p from hz ▸ y.2⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe _ _ _).trans hz
    have : IsClosedImmersion (c p ∣_ V p) :=
      IsZariskiLocalAtTarget.restrict (inferInstanceAs (IsClosedImmersion (c p))) _
    infer_instance
  -- the comparison map `F ⟶ ⨁ₚ cₚ_* cₚ^* F`
  have : HasFiniteBiproducts (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let adj (p : ι) := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c p)
  let G (p : ι) : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (c p)_*[AddCommGrpCat.{u + 1}].obj ((c p)^*[AddCommGrpCat.{u + 1}].obj F)
  let φ : F ⟶ ⨁ G := biproduct.lift fun p ↦ (adj p).unit.app F
  have hG (p : ι) : Subsingleton (Sheaf.H (G p) (m + 2)) := by
    have := hcurve p
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (Z p).smallEtaleTopology AddCommGrpCat.{u + 1})).obj
        ((c p)^*[AddCommGrpCat.{u + 1}].obj F)) (m + 2)) :=
      subsingleton_sheafH_of_three_le_of_isIntegral (c p ≫ f) _ (isTorsion_upperStar _ hF) _ hq
    exact (bijective_edgeMap_of_isFinite (c p) _ (m + 2)).injective.subsingleton
  have hφ : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map φ) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun p ↦ C.homOfLE (hVU p)) (fun x ↦ ?_) _ fun p ↦ ?_
    · obtain ⟨p, hp⟩ := hUV x.1 x.2
      exact ⟨p, ⟨x.1, hp⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
    have e := upperStarComp AddCommGrpCat.{u + 1} (C.homOfLE (hVU p)) U.ι (V p).ι
      (Scheme.homOfLE_ι _ _).symm
    rw [← Functor.comp_map, ← NatIso.isIso_map_iff e φ]
    let P := ((V p).ι)^*[AddCommGrpCat.{u + 1}]
    have hz (q : ι) (hqp : q ≠ p) : IsZero (P.obj (G q)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ (V p).ι (c q) (hdisj p q hqp) _
    have hπ : IsIso (P.map (biproduct.π G p)) := by
      refine ⟨P.map (biproduct.ι G p), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G), P.map_sum,
          Finset.sum_eq_single p (fun q _ hqp ↦ ?_) (by simp)]
        rw [P.map_comp, (hz q hqp).eq_zero_of_tgt (P.map (biproduct.π G q)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have := huh p
    have hunit : IsIso (P.map ((adj p).unit.app F)) :=
      isIso_upperStar_map_unit_of_isUniversalHomeomorphism (c p) (V p) F
    have : IsIso (P.map φ ≫ P.map (biproduct.π G p)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  have hSU : (U : Set C)ᶜ = S := compl_compl S
  have hsep (x : C) (hx : x ∉ U) : IsSepClosed (C.residueField x) := by
    have := Scheme.isAlgClosed_residueField_of_isClosed f x (hScl x (hSU ▸ hx))
    infer_instance
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hb := bijective_H_map_of_isIso_upperStar_map U (hSU ▸ hSfin)
    (fun x hx ↦ hScl x (hSU ▸ hx)) hsep φ hφ (n + 1)
  have : Subsingleton (Sheaf.H (⨁ G) (n + 1 + 2)) :=
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit G) (n + 1 + 2)).toEquiv.subsingleton
  exact hb.injective.subsingleton

end AlgebraicGeometry.IsCurve
