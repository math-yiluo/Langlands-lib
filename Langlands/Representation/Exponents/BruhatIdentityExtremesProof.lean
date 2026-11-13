import Langlands.Representation.Exponents.TemperedBruhatRemarksStatements
import Langlands.Representation.Intertwining.OppositeIdentitySupportProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct

/-! # The identity double coset is Bruhat-extreme (Renard VII.3.1)

Proof of `BruhatIdentityExtremesStatement`.

* `P = Q`: write `P(F) = P(χ)(F)` for a cocharacter `χ`. The open cell
  `Ω = P(χ)(F) U(χ⁻¹)(F)` is open and dense in `G(F)`, so `Ω ∩ gΩ` is nonempty for every `g`,
  and `P(F) g P(F)` contains a point `u` of `U(χ⁻¹)(F)`. Conjugating `u` by the powers of
  `χ⁻¹(t)` (with `tⁿ → 0`), which lie in `P(F)`, gives points of `P(F) g P(F)` tending to `1`.
  Hence `P(F)` lies in the closure of `P(F) g P(F)`.
* `Q = P̄`: `P(F) Q(F)` is dense (`dense_identityParabolicDoubleCoset_of_opposite`), so its
  closure is `G(F)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The dynamic open cell `P(χ)(F) U(χ⁻¹)(F)` is dense in `G(F)`. -/
theorem dense_range_dynamicOpenCellMap {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    Dense (Set.range (HarishChandraSchwartz.openCellMap
      (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (V := (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))))) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨-, hint⟩ := Plancherel.RationalCellConull.noetherian_and_integral k G
  have := hint
  obtain ⟨Z, hZc, hZne, hZeq⟩ := Plancherel.rationalDynamicOpenCellBoundary k G χ
  have hempty := Plancherel.RationalCellConull.interior_evaluation_preimage_eq_empty k G.X
    ⟨Z, hZc⟩ (fun h => hZne
      (congrArg (fun W : TopologicalSpace.Closeds G.X.left => (W : Set G.X.left)) h))
  change interior ((fun x : rationalPoints G => x.left (IsLocalRing.closedPoint k)) ⁻¹' Z) = ∅
    at hempty
  rw [hZeq, interior_eq_empty_iff_dense_compl, compl_compl] at hempty
  exact hempty

/-- Renard VII.3.1, `Q = P`: the identity double coset `P(F)` lies in the closure of every
double coset `P(F) g P(F)`. -/
theorem bruhatLE_identityParabolicDoubleCoset_self
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ w : parabolicDoubleCosets p p,
      Geometric.BruhatLE (pointImage p) (pointImage p) (identityParabolicDoubleCoset p p) w := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : IsTopologicalGroup (rationalPoints G) :=
    AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup k G
  let : T2Space k := Langlands.BruhatTits.localField_t2Space k
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  have : IsOpenUnits k := inferInstance
  have hpc : IsClosedSubgroup p := hp.isClosedSubgroup
  obtain ⟨χ, hPχ⟩ := (parabolicDynamic k G hG P p hpc).1 hp
  have hPpt : pointImage p = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hPχ]
  set ξ := Dynamic.inverseCocharacter χ with hξ
  set Ω := Set.range (HarishChandraSchwartz.openCellMap
      (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (V := (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) with hΩ
  have hΩo : IsOpen Ω :=
    (HarishChandraSchwartz.isOpenEmbedding_openCellMap_rationalPoint k G χ).isOpen_range
  have hΩd : Dense Ω := dense_range_dynamicOpenCellMap hG χ
  have h1 : (1 : rationalPoints G) ∈ Ω :=
    ⟨(1, 1), by simp [HarishChandraSchwartz.openCellMap]⟩
  intro w
  obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk (pointImage p) (pointImage p) g = w :=
    ⟨w.out, DoubleCoset.out_eq' w⟩
  -- A point of `U(χ⁻¹)(F)` in the double coset of `g`.
  have hgo : IsOpen ((fun x => g * x) '' Ω) := (Homeomorph.mulLeft g).isOpenMap Ω hΩo
  obtain ⟨y, ⟨x, hxΩ, hxy⟩, hyΩ⟩ := hΩd.inter_open_nonempty _ hgo ⟨g, 1, h1, mul_one g⟩
  obtain ⟨⟨a, v⟩, rfl⟩ := hyΩ
  obtain ⟨⟨a', v'⟩, rfl⟩ := hxΩ
  simp only [HarishChandraSchwartz.openCellMap] at hxy
  -- `hxy : g * (a' * v'⁻¹) = a * v⁻¹`
  set u : rationalPoints G := (a : rationalPoints G)⁻¹ * g * a' with hu
  have huv : u = (v : rationalPoints G)⁻¹ * v' := by
    rw [hu]
    calc (a : rationalPoints G)⁻¹ * g * a'
        = (a : rationalPoints G)⁻¹ * (g * (a' * (v' : rationalPoints G)⁻¹)) * v' := by group
      _ = (v : rationalPoints G)⁻¹ * v' := by rw [hxy]; group
  have huU : u ∈ (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 _)) := by
    rw [huv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ v.2) v'.2
  -- The contracting cocharacter values lie in `P(F)`.
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := k)
  set c : rationalPoints G := MatrixRepresentation.gmRationalPoint t ≫ ξ.hom.hom with hc
  have hcP : c ∈ pointImage p := by
    rw [hPpt]
    apply RationalPoint.levi_le_parabolic χ
    have h := BruhatTits.DynamicUnipotentContainment.cocharPoint_mem_centralizer ξ t
    rw [MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp,
      hξ, Dynamic.centralizer_inverseCocharacter] at h
    exact h
  have hlim := (MatrixRepresentation.mem_unipotent_iff_tendsto_conj k ξ t ht u).1 huU
  have haP : (a : rationalPoints G) ∈ pointImage p := by rw [hPpt]; exact a.2
  have ha'P : (a' : rationalPoints G) ∈ pointImage p := by rw [hPpt]; exact a'.2
  intro z hz
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hz
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := DoubleCoset.eq.mp hz.symm
  have hzP : h₁ * 1 * h₂ ∈ pointImage p :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₁ (Subgroup.one_mem _)) hh₂
  have hlim' : Tendsto (fun n : ℕ => (h₁ * 1 * h₂) * (c ^ n * u * (c ^ n)⁻¹)) atTop
      (𝓝 (h₁ * 1 * h₂)) := by
    simpa using (tendsto_const_nhds (x := h₁ * 1 * h₂)).mul hlim
  refine mem_closure_of_tendsto hlim' (Eventually.of_forall fun n => ?_)
  rw [DoubleCoset.mem_quotToDoubleCoset_iff, DoubleCoset.eq]
  have hcn : c ^ n ∈ pointImage p := Subgroup.pow_mem _ hcP n
  refine ⟨((h₁ * 1 * h₂) * c ^ n * (a : rationalPoints G)⁻¹)⁻¹,
    Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hzP hcn)
      (Subgroup.inv_mem _ haP)),
    (a' * (c ^ n)⁻¹)⁻¹,
    Subgroup.inv_mem _ (Subgroup.mul_mem _ ha'P (Subgroup.inv_mem _ hcn)), ?_⟩
  rw [hu]
  group

/-- Renard VII.3.1, `Q = P̄`: every double coset `P(F) g Q(F)` lies in the closure of the
identity double coset `P(F) Q(F)`, which is dense. -/
theorem bruhatLE_identityParabolicDoubleCoset_of_opposite
    {G P M Q : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    {q : Q ⟶ G} {lQ : M ⟶ Q} (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hlev : lQ ≫ q = l ≫ p)
    (hpts : pointImage p ⊓ pointImage q = pointImage (l ≫ p)) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ w : parabolicDoubleCosets p q,
      Geometric.BruhatLE (pointImage p) (pointImage q) w (identityParabolicDoubleCoset p q) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  obtain ⟨U, rQ, hrQ, -⟩ := hlQ.exists_unipotentRadical
  have hd := dense_identityParabolicDoubleCoset_of_opposite hG hp hl hq hlQ hrQ hlev hpts
  intro w x _
  rw [hd.closure_eq]
  trivial

/-- **Renard VII.3.1.** The identity double coset is the least element of `P \ G / P` and the
greatest element of `P \ G / P̄` for the Bruhat order. -/
theorem bruhatIdentityExtremes : BruhatIdentityExtremesStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M p l hp
  refine ⟨bruhatLE_identityParabolicDoubleCoset_self hG hp, ?_⟩
  intro Q q lQ hq hl hlQ hlev hpts
  exact bruhatLE_identityParabolicDoubleCoset_of_opposite hG hp hl hq hlQ hlev hpts

end Langlands.Aubert.General.RepresentedParabolic
