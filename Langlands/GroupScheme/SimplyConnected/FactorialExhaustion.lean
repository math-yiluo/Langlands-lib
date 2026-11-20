import Langlands.GroupScheme.SimplyConnected.FactorialBoundaryChart
import Langlands.GroupScheme.SimplyConnected.FactorialStabilizer
import Langlands.Geometry.Building.SplitIntegralPinningOfRoots
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism

/-! # Exhaustion: the complement of the big cell and its translates has codimension two -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell Langlands.AlgebraicGeometry.FunctionFieldChart

/-! ### Points through open immersions and residue fields -/

/-- A point whose range lies in the range of an open immersion factors through it. -/
theorem exists_eq_comp_of_range_subset {S : Scheme.{u}} {C X W : Over S} (φ : C ⟶ X)
    [IsOpenImmersion φ.left] (g : W ⟶ X) (h : Set.range g.left.base ⊆ Set.range φ.left.base) :
    ∃ z : W ⟶ C, z ≫ φ = g := by
  refine ⟨Over.homMk (IsOpenImmersion.lift φ.left g.left h) ?_, ?_⟩
  · rw [← Over.w φ, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w g]
  · apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac φ.left g.left h

/-- The residue field at a point of a test scheme, as a test scheme with a single point and a
field of global functions. -/
theorem exists_residue_point {S : Scheme.{u}} {W : Over S} (w : W.left) :
    ∃ (W' : Over S) (a : W' ⟶ W), (∀ p, a.left.base p = w) ∧
      (∀ x : Γ(W'.left, ⊤), x = 0 ∨ IsUnit x) ∧ Nonempty W'.left ∧
        Nontrivial Γ(W'.left, ⊤) := by
  refine ⟨Over.mk (W.left.fromSpecResidueField w ≫ W.hom),
    Over.homMk (W.left.fromSpecResidueField w) rfl, fun p => ?_, fun x => ?_, ?_, ?_⟩
  · exact Scheme.fromSpecResidueField_apply w p
  · rcases eq_or_ne ((Scheme.ΓSpecIso (W.left.residueField w)).hom x) 0 with h | h
    · left
      have := congrArg (Scheme.ΓSpecIso (W.left.residueField w)).inv h
      simpa using this
    · right
      have hu := (IsUnit.mk0 _ h).map (Scheme.ΓSpecIso (W.left.residueField w)).inv.hom
      simpa using hu
  · exact inferInstanceAs (Nonempty (PrimeSpectrum (W.left.residueField w)))
  · exact (Scheme.ΓSpecIso (W.left.residueField w)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G) {m n : ℕ} (neg : Fin m ≃ {α // ¬ D.b.IsPos α})
  (pos : Fin n ≃ {α // D.b.IsPos α})

/-! ### Points of the big cell -/

/-- Every cell point is a point of the big-cell chart. -/
theorem exists_comp_chart_eq {W : Over (Spec (CommRingCat.of k))} (v : Fin m → Γ(W.left, ⊤))
    (t : W ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X) (w : Fin n → Γ(W.left, ⊤)) :
    ∃ z : W ⟶ cellSpec k D.I m n,
      z ≫ D.chart neg pos = cellPoint D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J))
        W v t w := by
  obtain ⟨x, hx⟩ := (LocalSplitBigCell.coordTriple_bijective k D.I m n W).2 (v, t, w)
  obtain ⟨z, hz⟩ := (bijective_comp_cellCoordHom W).2 x
  have hz' : z ≫ cellCoordHom k D.I m n = x := hz
  simp only [LocalSplitBigCell.coordTriple, Prod.mk.injEq] at hx
  refine ⟨z, ?_⟩
  rw [chart, ← Category.assoc, hz', comp_cellMap, hx.1, hx.2.1, hx.2.2]

/-- The big cell is stable under left multiplication by the negative span. -/
theorem exists_negSpan_mul_chart {W : Over (Spec (CommRingCat.of k))} {g : W ⟶ G.X}
    (hg : g ∈ D.negSpan.carrier W) (z : W ⟶ cellSpec k D.I m n) :
    ∃ z' : W ⟶ cellSpec k D.I m n, g * (z ≫ D.chart neg pos) = z' ≫ D.chart neg pos := by
  have hmem : g * orderedProduct D.u (fun r => (neg r : D.J)) W
      (fun r => pointRing z (negVar k D.I m n r)) ∈ D.negSpan.carrier W :=
    mul_mem hg (D.orderedProduct_mem_rootSpan D.isClosedRootSet_neg neg W _)
  obtain ⟨v', hv'⟩ := D.exists_eq_orderedProduct D.isClosedRootSet_neg neg hmem
  obtain ⟨z', hz'⟩ := D.exists_comp_chart_eq neg pos v' (z ≫ specTorus k D.I m n)
    (fun r => pointRing z (posVar k D.I m n r))
  refine ⟨z', ?_⟩
  rw [hz', comp_chart, cellPoint, cellPoint]
  change _ = orderedProduct D.u (fun r => (neg r : D.J)) W v' * _ * _
  rw [hv', mul_assoc, mul_assoc, mul_assoc]

/-- The big cell is stable under left multiplication by the torus. -/
theorem exists_torus_mul_chart {W : Over (Spec (CommRingCat.of k))}
    (t₀ : W ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X) (z : W ⟶ cellSpec k D.I m n) :
    ∃ z' : W ⟶ cellSpec k D.I m n,
      (t₀ ≫ D.i.hom.hom) * (z ≫ D.chart neg pos) = z' ≫ D.chart neg pos := by
  set N := orderedProduct D.u (fun r => (neg r : D.J)) W
      (fun r => pointRing z (negVar k D.I m n r)) with hN
  have hmem : (t₀ ≫ D.i.hom.hom) * N * (t₀ ≫ D.i.hom.hom)⁻¹ ∈ D.negSpan.carrier W :=
    D.torus_conj_mem_rootSpan D.isClosedRootSet_neg t₀
      (D.orderedProduct_mem_rootSpan D.isClosedRootSet_neg neg W _)
  obtain ⟨v', hv'⟩ := D.exists_eq_orderedProduct D.isClosedRootSet_neg neg hmem
  obtain ⟨z', hz'⟩ := D.exists_comp_chart_eq neg pos v' (t₀ * (z ≫ specTorus k D.I m n))
    (fun r => pointRing z (posVar k D.I m n r))
  refine ⟨z', ?_⟩
  rw [hz', comp_chart, cellPoint, cellPoint, hv', MonObj.mul_comp, ← hN]
  group

/-- **Left multiplication of a cell point by a simple root point over a field.** The product
lies in the big cell or in its translate by `u_a(1)`. -/
theorem rootPoint_mul_chart_mem {a : D.J} (ha : a ∈ D.b.support) {W : Over (Spec (CommRingCat.of k))}
    [Nontrivial Γ(W.left, ⊤)] (hW : ∀ x : Γ(W.left, ⊤), x = 0 ∨ IsUnit x) (e : Γ(W.left, ⊤))
    (z : W ⟶ cellSpec k D.I m n) :
    (∃ z' : W ⟶ cellSpec k D.I m n,
        rootPoint (D.u a) W e * (z ≫ D.chart neg pos) = z' ≫ D.chart neg pos) ∨
      ∃ z' : W ⟶ cellSpec k D.I m n,
        rootPoint (D.u a) W e * (z ≫ D.chart neg pos) = z' ≫ D.tchart neg pos a := by
  set y := pointRing z (negVar k D.I m n (D.oppIndex (neg := neg) ha)) with hy
  rcases hW (1 + e * y) with h0 | hu
  · -- `1 + e y = 0`: translate by `u_a(e - 1)` first
    have hy0 : -y ≠ 0 := by
      intro h
      rw [neg_eq_zero] at h
      rw [h, mul_zero, add_zero] at h0
      exact one_ne_zero h0
    obtain hu' := (hW (-y)).resolve_left hy0
    obtain ⟨v', w', h⟩ := D.exists_translate_cellPoint ha neg pos W
      (fun r => pointRing z (negVar k D.I m n r)) (z ≫ specTorus k D.I m n)
      (fun r => pointRing z (posVar k D.I m n r)) (e - 1) hu'.unit
      (by rw [IsUnit.unit_spec]; change -y = 1 + (e - 1) * y; linear_combination (-1 : Γ(W.left, ⊤)) * h0)
    obtain ⟨z', hz'⟩ := D.exists_comp_chart_eq neg pos v'
      (cocharPoint (D.P.coroot a) W hu'.unit * (z ≫ specTorus k D.I m n)) w'
    refine Or.inr ⟨z', ?_⟩
    have he1 : rootPoint (D.u a) W e = rootPoint (D.u a) W 1 * rootPoint (D.u a) W (e - 1) := by
      rw [← rootPoint_add, add_sub_cancel]
    rw [comp_tchart, hz', ← h, ← comp_chart, he1, mul_assoc]
  · obtain ⟨v', w', h⟩ := D.exists_translate_cellPoint ha neg pos W
      (fun r => pointRing z (negVar k D.I m n r)) (z ≫ specTorus k D.I m n)
      (fun r => pointRing z (posVar k D.I m n r)) e hu.unit (by rw [IsUnit.unit_spec]; rfl)
    obtain ⟨z', hz'⟩ := D.exists_comp_chart_eq neg pos v'
      (cocharPoint (D.P.coroot a) W hu.unit * (z ≫ specTorus k D.I m n)) w'
    exact Or.inl ⟨z', by rw [hz', ← h, comp_chart]⟩

/-! ### Translates of points of a closed set avoiding the big cell -/

/-- Translation by a group whose points keep the big cell stable never moves points outside the
big cell into it. -/
theorem translate_notMem_of_stable {H : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G)
    (hst : ∀ (W : Over (Spec (CommRingCat.of k))) (h : W ⟶ H.X) (z : W ⟶ cellSpec k D.I m n),
      ∃ z' : W ⟶ cellSpec k D.I m n,
        (h ≫ j.hom.hom) * (z ≫ D.chart neg pos) = z' ≫ D.chart neg pos)
    {Z : Set G.X.left} (hZ : Disjoint Z (Set.range (D.chart neg pos).left.base))
    (W : Over (Spec (CommRingCat.of k))) (h : W ⟶ H.X) (z : W ⟶ G.X) (w : W.left)
    (hzw : z.left.base w ∈ Z) :
    ((h ≫ j.hom.hom) * z).left.base w ∉ Set.range (D.chart neg pos).left.base := by
  intro hmem
  obtain ⟨W', a, ha, -, ⟨p⟩, -⟩ := exists_residue_point w
  obtain ⟨z₁, hz₁⟩ := exists_eq_comp_of_range_subset (D.chart neg pos)
    (a ≫ ((h ≫ j.hom.hom) * z)) (by
      rintro _ ⟨p', rfl⟩
      change ((h ≫ j.hom.hom) * z).left.base (a.left.base p') ∈ _
      rw [ha]
      exact hmem)
  have hz : a ≫ z = ((a ≫ h)⁻¹ ≫ j.hom.hom) * (z₁ ≫ D.chart neg pos) := by
    rw [hz₁, MonObj.comp_mul, GrpObj.inv_comp, ← Category.assoc, inv_mul_cancel_left]
  obtain ⟨z₂, hz₂⟩ := hst W' (a ≫ h)⁻¹ z₁
  rw [hz₂] at hz
  apply Set.disjoint_left.1 hZ hzw
  refine ⟨z₂.left.base p, ?_⟩
  change (z₂ ≫ D.chart neg pos).left.base p = _
  rw [← hz]
  change z.left.base (a.left.base p) = _
  rw [ha]

/-- Translation by a simple root group never moves points of a closed set avoiding the big cell
and its translate by `u_a(1)` into the big cell. -/
theorem translate_notMem_of_simple {a : D.J} (ha : a ∈ D.b.support) {Z : Set G.X.left}
    (hZ : Disjoint Z (Set.range (D.chart neg pos).left.base))
    (hZa : Disjoint Z (Set.range (D.tchart neg pos a).left.base))
    (W : Over (Spec (CommRingCat.of k))) (h : W ⟶ (Ga k).X) (z : W ⟶ G.X) (w : W.left)
    (hzw : z.left.base w ∈ Z) :
    ((h ≫ (D.u a).hom.hom) * z).left.base w ∉ Set.range (D.chart neg pos).left.base := by
  intro hmem
  obtain ⟨W', b, hb, hfield, ⟨p⟩, hnt⟩ := exists_residue_point w
  obtain ⟨z₁, hz₁⟩ := exists_eq_comp_of_range_subset (D.chart neg pos)
    (b ≫ ((h ≫ (D.u a).hom.hom) * z)) (by
      rintro _ ⟨p', rfl⟩
      change ((h ≫ (D.u a).hom.hom) * z).left.base (b.left.base p') ∈ _
      rw [hb]
      exact hmem)
  have hz : b ≫ z = rootPoint (D.u a) W' (-gaCoord (b ≫ h)) * (z₁ ≫ D.chart neg pos) := by
    rw [hz₁, MonObj.comp_mul, rootPoint_neg, ← Category.assoc, comp_eq_rootPoint,
      inv_mul_cancel_left]
  have hpz : z.left.base w = (b ≫ z).left.base p := by
    change _ = z.left.base (b.left.base p)
    rw [hb]
  rcases D.rootPoint_mul_chart_mem neg pos ha hfield (-gaCoord (b ≫ h)) z₁ with
    ⟨z₂, hz₂⟩ | ⟨z₂, hz₂⟩
  · apply Set.disjoint_left.1 hZ hzw
    refine ⟨z₂.left.base p, ?_⟩
    change (z₂ ≫ D.chart neg pos).left.base p = _
    rw [hpz, hz, hz₂]
  · apply Set.disjoint_left.1 hZa hzw
    refine ⟨z₂.left.base p, ?_⟩
    change (z₂ ≫ D.tchart neg pos a).left.base p = _
    rw [hpz, hz, hz₂]

/-! ### Generation of all root groups by the simple ones -/

/-- A subgroup functor containing the root groups of the simple roots and their opposites
contains every root group. -/
theorem rootPoint_mem_of_simple (F : SubgroupFunctor G)
    (hF : ∀ a ∈ D.b.support, ∀ (W : Over (Spec (CommRingCat.of k))) (c : Γ(W.left, ⊤)),
      rootPoint (D.u a) W c ∈ F.carrier W ∧
        rootPoint (D.u (D.P.reflectionPerm a a)) W c ∈ F.carrier W)
    (β : D.J) (W : Over (Spec (CommRingCat.of k))) (c : Γ(W.left, ⊤)) :
    rootPoint (D.u β) W c ∈ F.carrier W := by
  classical
  have : Mono D.i.hom.hom.left := by
    have : IsClosedImmersion D.i.hom.hom.left := D.isClosedSubgroup
    infer_instance
  have : Fintype D.J := Fintype.ofFinite _
  -- the root subgroup of a root character is the range of its parametrization
  have hrange : ∀ α : D.J, RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ D.I) D.i
      (splitTorus.exponentCharacter _ D.I (D.P.root α)) = SubgroupFunctor.range (D.u α) :=
    fun α => (D.hu α).represents.2.symm
  have hrangeF : ∀ α : D.J, (∀ (W : Over (Spec (CommRingCat.of k))) (c : Γ(W.left, ⊤)),
      rootPoint (D.u α) W c ∈ F.carrier W) → SubgroupFunctor.range (D.u α) ≤ F := by
    intro α hα W g hg
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    rw [comp_eq_rootPoint]
    exact hα W _
  suffices hQ : ∀ α : D.J, RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ D.I) D.i
      (Langlands.Geometry.Building.SplitIntegralPinning.rootChar (k := k) D.P α) ≤ F by
    have h := hQ β W
    rw [Langlands.Geometry.Building.SplitIntegralPinning.rootChar, hrange] at h
    exact h (SubgroupFunctor.mem_range.2 ⟨VectorGroup.scalarPoint _ W c, rfl⟩)
  intro α
  refine Langlands.Geometry.Building.SplitIntegralPinning.induction_rootChar D.b
    (fun χ => RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ D.I) D.i χ ≤ F)
    (fun j hj => ?_) (fun j hj α' hα' => ?_) α
  · rw [Langlands.Geometry.Building.SplitIntegralPinning.rootChar, hrange]
    exact hrangeF j (fun W c => (hF j hj W c).1)
  · let nW := Langlands.Geometry.Building.SplitIntegralPinning.simpleWeylPoint D.b D.weyl j hj
    have hact := Langlands.Geometry.Building.SplitIntegralPinning.weylAction_simpleWeylPoint_rootChar
      D.b D.weyl j hj α'
    intro W g hg
    rw [← hact] at hg
    set C := G.constantPoint nW W with hCdef
    have hC : C ∈ F.carrier W := by
      rw [hCdef, show G.constantPoint nW W = toUnit W ≫
          weylPoint (D.u j) (D.u (D.P.reflectionPerm j j)) from
        (toUnit_comp_eq_constantPoint _ W).symm]
      rw [weylPoint, MonObj.comp_mul, MonObj.comp_mul, comp_rootPoint, comp_rootPoint,
        map_neg, map_one]
      exact mul_mem (mul_mem (hF j hj W _).2 (hF j hj W _).1) (hF j hj W _).2
    have hconj : C * (C⁻¹ * g * C) * C⁻¹ = g := by group
    have hg' : C⁻¹ * g * C ∈ F.carrier W := by
      apply hα' W
      refine (RelativeRoot.normalizer_conj_mem_iff (S := splitTorus.commGroupScheme _ D.I) D.i
        (Langlands.Geometry.Building.SplitIntegralPinning.rootChar (k := k) D.P α') nW
        (C⁻¹ * g * C)).1 ?_
      rw [← hCdef, hconj]
      exact hg
    rw [← hconj]
    exact mul_mem (mul_mem hC hg') (inv_mem hC)

/-! ### The final contradiction -/

theorem ga_geometry : Smooth (Ga k).X.hom ∧ IsAffineHom (Ga k).X.hom ∧
    ConnectedSpace (Ga k).X.left := by
  refine ⟨Corepresented.smooth_groupScheme_iff.mpr inferInstance, ?_, ?_⟩
  · change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
    infer_instance

omit [IsAffineHom G.X.hom] in
/-- Under the hypotheses of `range_subset_of_maximal`, every point of the smooth connected affine
group `H` maps into the stabilizer of `Z`. -/
theorem comp_mem_stabilizer {H : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom]
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] (j : H ⟶ G) {Z V : Set G.X.left}
    (hV : IsOpen V) (hZ : IsIrreducible Z)
    (hmax : ∀ T : Set G.X.left, IsIrreducible T → IsClosed T → Z ⊆ T → Disjoint T V → T ⊆ Z)
    (hyp : ∀ (W : Over (Spec (CommRingCat.of k))) (h : W ⟶ H.X) (z : W ⟶ G.X) (w : W.left),
      z.left.base w ∈ Z → ((h ≫ j.hom.hom) * z).left.base w ∉ V)
    {Y : Over (Spec (CommRingCat.of k))} (h : Y ⟶ H.X) :
    h ≫ j.hom.hom ∈ (stabilizer Z).carrier Y := by
  intro W y z hz
  rw [← Category.assoc]
  refine ⟨range_subset_of_maximal j hV hZ hmax hyp (y ≫ h) z hz, ?_⟩
  rw [← GrpObj.inv_comp]
  exact range_subset_of_maximal j hV hZ hmax hyp (y ≫ h)⁻¹ z hz

/-- **Exhaustion.** Let `Z` be an irreducible subset of `G` that is disjoint from the big cell,
and assume that every closed irreducible set containing `Z` and disjoint from the big cell is
contained in `Z` (so `Z` is closed, and maximal among closed irreducible subsets of the
complement of the big cell). Then `Z` meets one of the translated charts `tchart a`
(the translates `u_a(1) · Ω` of the big cell, `a` simple). -/
theorem false_of_maximal [Smooth G.X.hom] [ConnectedSpace G.X.left] {Z : Set G.X.left}
    (hZ : IsIrreducible Z)
    (hmax : ∀ T : Set G.X.left, IsIrreducible T → IsClosed T → Z ⊆ T →
      Disjoint T (Set.range (D.chart neg pos).left.base) → T ⊆ Z)
    (hZV : Disjoint Z (Set.range (D.chart neg pos).left.base))
    (hZa : ∀ a ∈ D.b.support, Disjoint Z (Set.range (D.tchart neg pos a).left.base)) :
    False := by
  classical
  set V := Set.range (D.chart neg pos).left.base with hVdef
  have hVo : IsOpen V := (D.chart neg pos).left.isOpenEmbedding.isOpen_range
  obtain ⟨hGa1, hGa2, hGa3⟩ := ga_geometry (k := k)
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) D.I).X.hom :=
    isAffineHom_splitTorus _ _
  have : Smooth (splitTorus (Spec (CommRingCat.of k)) D.I).X.hom := smooth_splitTorus D.I
  set F := stabilizer (G := G) Z with hF
  -- simple root groups and their opposites
  have hsimple : ∀ a ∈ D.b.support, ∀ (W : Over (Spec (CommRingCat.of k))) (c : Γ(W.left, ⊤)),
      rootPoint (D.u a) W c ∈ F.carrier W ∧
        rootPoint (D.u (D.P.reflectionPerm a a)) W c ∈ F.carrier W := by
    intro a ha W c
    constructor
    · exact comp_mem_stabilizer (D.u a) hVo hZ hmax
        (D.translate_notMem_of_simple neg pos ha hZV (hZa a ha)) _
    · refine comp_mem_stabilizer (D.u (D.P.reflectionPerm a a)) hVo hZ hmax
        (D.translate_notMem_of_stable neg pos _ (fun W' h z => ?_) hZV) _
      rw [comp_eq_rootPoint]
      exact D.exists_negSpan_mul_chart neg pos
        (D.rootPoint_mem_negSpan (D.not_isPos_reflectionPerm_self ha) W' _) z
  have hroot := D.rootPoint_mem_of_simple F hsimple
  have htorus : ∀ {W : Over (Spec (CommRingCat.of k))}
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X),
      t ≫ D.i.hom.hom ∈ F.carrier W := fun t =>
    comp_mem_stabilizer D.i hVo hZ hmax
      (D.translate_notMem_of_stable neg pos D.i (fun W' h z => D.exists_torus_mul_chart neg pos h z)
        hZV) t
  have hprod : ∀ {r : ℕ} (e : Fin r → D.J) (W : Over (Spec (CommRingCat.of k)))
      (c : Fin r → Γ(W.left, ⊤)), orderedProduct D.u e W c ∈ F.carrier W := by
    intro r e W c
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨q, rfl⟩ := List.mem_ofFn.1 hg
    exact hroot _ W _
  have hcell : ∀ {W : Over (Spec (CommRingCat.of k))} (z : W ⟶ cellSpec k D.I m n),
      z ≫ D.chart neg pos ∈ F.carrier W := by
    intro W z
    rw [comp_chart, cellPoint]
    exact mul_mem (mul_mem (hprod _ W _) (htorus _)) (hprod _ W _)
  -- a point of `Z`, its residue field and the base change of `G` to it
  obtain ⟨y₀, hy₀⟩ := hZ.nonempty
  let W₀ : Over (Spec (CommRingCat.of k)) :=
    Over.mk (G.X.left.fromSpecResidueField y₀ ≫ G.X.hom)
  let z₀ : W₀ ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField y₀) rfl
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  let Wp : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd G.X.hom W₀.hom ≫ W₀.hom)
  let τ : Wp ⟶ G.X := Over.homMk (pullback.fst G.X.hom W₀.hom) pullback.condition
  let pr : Wp ⟶ W₀ := Over.homMk (pullback.snd G.X.hom W₀.hom) rfl
  let zp : Wp ⟶ G.X := pr ≫ z₀
  have hext : ∀ {W : Over (Spec (CommRingCat.of k))} (f g : W ⟶ Wp), f ≫ τ = g ≫ τ →
      f ≫ pr = g ≫ pr → f = g := by
    intro W f g h1 h2
    apply Over.OverMorphism.ext
    exact pullback.hom_ext (congrArg CommaMorphism.left h1) (congrArg CommaMorphism.left h2)
  -- right translation by the point of `Z`, on the base change
  have hlift : ∀ q : Wp ⟶ G.X, q.left ≫ G.X.hom = pullback.snd G.X.hom W₀.hom ≫ W₀.hom :=
    fun q => Over.w q
  let ρ : Wp ⟶ Wp := Over.homMk (pullback.lift (τ * zp).left (pullback.snd _ _) (hlift _))
    (by simp only [Wp, Over.mk_hom]; rw [pullback.lift_snd_assoc])
  let ρ' : Wp ⟶ Wp := Over.homMk (pullback.lift (τ * zp⁻¹).left (pullback.snd _ _) (hlift _))
    (by simp only [Wp, Over.mk_hom]; rw [pullback.lift_snd_assoc])
  have hρτ : ρ ≫ τ = τ * zp := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hρpr : ρ ≫ pr = pr := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have hρ'τ : ρ' ≫ τ = τ * zp⁻¹ := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hρ'pr : ρ' ≫ pr = pr := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have hρ'ρ : ρ' ≫ ρ = 𝟙 Wp := by
    apply hext
    · rw [Category.assoc, hρτ, MonObj.comp_mul, hρ'τ, Category.id_comp]
      change τ * zp⁻¹ * (ρ' ≫ pr ≫ z₀) = τ
      rw [← Category.assoc, hρ'pr, inv_mul_cancel_right]
    · rw [Category.assoc, hρpr, hρ'pr, Category.id_comp]
  -- two nonempty opens of the irreducible base change
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hW₀ne : Nonempty W₀.left := inferInstanceAs
    (Nonempty (PrimeSpectrum (G.X.left.residueField y₀)))
  obtain ⟨v₀⟩ : Nonempty (cellSpec k D.I m n).left := inferInstance
  obtain ⟨p₁, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.X.hom) (g := W₀.hom)
    ((D.chart neg pos).left.base v₀) (Nonempty.some hW₀ne) (Subsingleton.elim _ _)
  let O₁ : Set Wp.left := ⇑τ.left ⁻¹' V
  let O₂ : Set Wp.left := ⇑(τ * zp).left ⁻¹' V
  have hO₁ : IsOpen O₁ := hVo.preimage τ.left.continuous
  have hO₂ : IsOpen O₂ := hVo.preimage (τ * zp).left.continuous
  have hp₁O : p₁ ∈ O₁ := by
    change (pullback.fst G.X.hom W₀.hom) p₁ ∈ V
    rw [hp₁]
    exact ⟨v₀, rfl⟩
  have hp₂O : ρ'.left.base p₁ ∈ O₂ := by
    change (τ * zp).left.base (ρ'.left.base p₁) ∈ V
    rw [← hρτ]
    change τ.left.base ((ρ' ≫ ρ).left.base p₁) ∈ V
    rw [hρ'ρ]
    exact hp₁O
  have hW₀irr : IrreducibleSpace W₀.left :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (G.X.left.residueField y₀)))
  have hUO : UniversallyOpen G.X.hom := inferInstance
  have hirr : IrreducibleSpace Wp.left :=
    GeometricallyIrreducible.irreducibleSpace (pullback.snd G.X.hom W₀.hom)
      (pullback.snd G.X.hom W₀.hom).isOpenMap
  obtain ⟨p₀, -, hp⟩ := (IrreducibleSpace.isIrreducible_univ Wp.left).2
    O₁ O₂ hO₁ hO₂ ⟨p₁, trivial, hp₁O⟩ ⟨_, trivial, hp₂O⟩
  -- restrict to the intersection
  let U : Wp.left.Opens := ⟨O₁ ∩ O₂, hO₁.inter hO₂⟩
  let WU : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ Wp.hom)
  let incl : WU ⟶ Wp := Over.homMk U.ι rfl
  obtain ⟨zc, hzc⟩ := exists_eq_comp_of_range_subset (D.chart neg pos) (incl ≫ τ) (by
    rintro _ ⟨q, rfl⟩
    exact q.2.1)
  have hτU : incl ≫ τ ∈ F.carrier WU := by
    rw [← hzc]
    exact hcell zc
  have hzU : Set.range (incl ≫ zp).left.base ⊆ Z := by
    rintro _ ⟨q, rfl⟩
    change z₀.left.base ((incl ≫ pr).left.base q) ∈ Z
    change G.X.left.fromSpecResidueField y₀ _ ∈ Z
    rw [Scheme.fromSpecResidueField_apply]
    exact hy₀
  have h := (hτU WU (𝟙 _) (incl ≫ zp) hzU).1
  rw [Category.id_comp, ← MonObj.comp_mul] at h
  apply Set.disjoint_left.1 hZV (h ⟨⟨p₀, hp⟩, rfl⟩)
  exact hp.2

end CellData

end Langlands.GroupScheme.SplitFactorial
