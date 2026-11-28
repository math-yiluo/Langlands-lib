import Langlands.AlgebraicGeometry.HenselianBirationalSolution.MulBarAssoc

/-! # Local solutions to the equation `xz = y`

Two points over the same base point lie in a common section chart. In that chart one chooses a
section `c` so that `xr = c` and `cs = y` can be solved using the original law in a neighbourhood
of the given pair. Associativity of the extended multiplication gives `x(rs) = y` there.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology NeronModelInfra GroupLawOverBase

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m) [S.IsSeparated] (hL : HasSectionLifts g)

@[simp]
theorem comp_mulPts {T T' : Scheme.{u}} {t : T ⟶ S} {t' : T' ⟶ S} (f : T' ⟶ T)
    (hf : f ≫ t = t') (x y : SchemeHomOver t (toS H)) :
    schemeHomOverComp f hf (mulPts H hL x y) =
      mulPts H hL (schemeHomOverComp f hf x) (schemeHomOverComp f hf y) := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe, mulPts, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

include hL in
/-- Any two points over a point of the base lie in a common chart indexed by a section. -/
theorem exists_common_chart (p : GG H) :
    ∃ d : Sect g, p ∈ Set.range (chartPair H (some d) (some d)) := by
  obtain ⟨i, a, ha⟩ := Glue.exists_chart H (secTrans H) (Gfst H p)
  obtain ⟨j, b, hb⟩ := Glue.exists_chart H (secTrans H) (Gsnd H p)
  have hp : p ∈ Set.range (chartPair H i j) := by
    rw [chartPair, Scheme.Pullback.range_map]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  obtain ⟨w, rfl⟩ := hp
  let x := pullback.fst g g
  let y := pullback.snd g g
  let q := x ≫ g
  obtain ⟨A, e, he, hA, ha⟩ := chartCover H hL i q x rfl
  obtain ⟨B, f, hf, hB, hb⟩ := chartCover H hL j q y pullback.condition.symm
  obtain ⟨d, hdA, hdB⟩ := hL _ q (Set.range e ∩ Set.range f)
    (e.isOpenEmbedding.isOpen_range.inter f.isOpenEmbedding.isOpen_range)
    (FibreGenerizationDense.inter hA hB e.isOpenEmbedding.isOpen_range) w
  have mem_chart {Z : Scheme.{u}} (k : Option (Sect g)) (a : pullback g g ⟶ Y)
      (j : Z ⟶ pullback g q) [IsOpenImmersion j]
      (hj : ∀ (d : Sect g) (O : (pullback g g).Opens) (l : O.toScheme ⟶ Z),
        l ≫ j = O.ι ≫ secLift q d →
          ∀ o : O.toScheme, ch H k (a (O.ι o)) ∈ Set.range (ch H (some d)))
      (hd : secLift q d w ∈ Set.range j) :
      ch H k (a w) ∈ Set.range (ch H (some d)) := by
    let O := secLift q d ⁻¹ᵁ j.opensRange
    have hO : Set.range (O.ι ≫ secLift q d) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    exact hj d O (IsOpenImmersion.lift j _ hO) (IsOpenImmersion.lift_fac _ _ _) ⟨w, hd⟩
  refine ⟨d, ?_⟩
  rw [chartPair, Scheme.Pullback.range_map]
  constructor
  · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, chartPair, pullback.lift_fst,
      Scheme.Hom.comp_apply]
    exact mem_chart i x e ha hdA
  · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, chartPair, pullback.lift_snd,
      Scheme.Hom.comp_apply]
    exact mem_chart j y f hb hdB

include hL in
/-- Local division in any chart. Both divisions that use the original law are defined on the
neighbourhood where the pairs `(x,c)` and `(c,y)` lie in the image of the left translation. -/
theorem exists_local_division_in_chart {T : Scheme.{u}} {t : T ⟶ S}
    (i : Option (Sect g)) (x y : SchemeHomOver t g) (p : T) :
    ∃ (O : T.Opens) (z : SchemeHomOver (O.ι ≫ t) (toS H)), p ∈ O ∧
      mulPts H hL (chartPt H i (schemeHomOverComp O.ι rfl x)) z =
        chartPt H i (schemeHomOverComp O.ι rfl y) := by
  let A := pairFst x.1 x.2 ⁻¹ᵁ (leftT m).opensRange
  let B := pairSnd y.1 y.2 ⁻¹ᵁ (leftT m).opensRange
  have hA : FibreGenerizationDense (pullback.snd g t) (A : Set _) :=
    fibreGenerizationDense_pairFst x.1 x.2 H.strict.left_fst
  have hB : FibreGenerizationDense (pullback.snd g t) (B : Set _) :=
    fibreGenerizationDense_pairSnd y.1 y.2 H.strict.left_snd
  obtain ⟨c, hc⟩ := hL _ t (A ⊓ B : (pullback g t).Opens) (A ⊓ B).isOpen
    (FibreGenerizationDense.inter hA hB A.isOpen) p
  let O := secLift t c ⁻¹ᵁ (A ⊓ B)
  let q := O.ι ≫ t
  let xO : SchemeHomOver q g := schemeHomOverComp O.ι rfl x
  let yO : SchemeHomOver q g := schemeHomOverComp O.ι rfl y
  let cO : SchemeHomOver q g := schemeHomOverComp q (Category.comp_id q) c
  have hxc : PairIn xO.1 cO.1 (xO.2.trans cO.2.symm) (Set.range (leftT m)) := by
    have he : pullback.lift xO.1 cO.1 (xO.2.trans cO.2.symm) =
        O.ι ≫ secLift t c ≫ pairFst x.1 x.2 := by
      apply pullback.hom_ext <;> simp [xO, cO, q]
    rintro _ ⟨w, rfl⟩
    rw [he, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact w.2.1
  have hcy : PairIn cO.1 yO.1 (cO.2.trans yO.2.symm) (Set.range (leftT m)) := by
    have he : pullback.lift cO.1 yO.1 (cO.2.trans yO.2.symm) =
        O.ι ≫ secLift t c ≫ pairSnd y.1 y.2 := by
      apply pullback.hom_ext <;> simp [cO, yO, q]
    rintro _ ⟨w, rfl⟩
    rw [he, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact w.2.2
  let r : SchemeHomOver q g := ⟨m.ldiv xO.1 cO.1 _ hxc, (m.ldiv_comp_g _ _ _ hxc).symm.trans xO.2⟩
  let s : SchemeHomOver q g := ⟨m.ldiv cO.1 yO.1 _ hcy, (m.ldiv_comp_g _ _ _ hcy).symm.trans cO.2⟩
  obtain ⟨hdr, hr⟩ := m.ldiv_spec _ _ _ hxc
  obtain ⟨hds, hs⟩ := m.ldiv_spec _ _ _ hcy
  have er : mulPts H hL (chartPt H i xO) (chartPt H none r) = chartPt H i cO := by
    rw [mulPts_in_chart H hL i xO r hdr]
    exact congrArg (chartPt H i) (Subtype.ext hr)
  have es : mulPts H hL (chartPt H i cO) (chartPt H none s) = chartPt H i yO := by
    rw [mulPts_in_chart H hL i cO s hds]
    exact congrArg (chartPt H i) (Subtype.ext hs)
  refine ⟨O, mulPts H hL (chartPt H none r) (chartPt H none s), hc, ?_⟩
  change mulPts H hL (chartPt H i xO) _ = chartPt H i yO
  rw [← mulPts_assoc, er, es]

include hL in
/-- Every point of the parameter scheme has an open neighbourhood on which `x z = y` has a
solution. -/
theorem exists_local_division {T : Scheme.{u}} {t : T ⟶ S} (x y : SchemeHomOver t (toS H)) (p : T) :
    ∃ (Q : Scheme.{u}) (j : Q ⟶ T) (_ : IsOpenImmersion j) (z : SchemeHomOver (j ≫ t) (toS H)),
      p ∈ Set.range j ∧ mulPts H hL (schemeHomOverComp j rfl x) z = schemeHomOverComp j rfl y := by
  let xy := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  obtain ⟨d, hd⟩ := exists_common_chart H hL (xy p)
  let V := xy ⁻¹ᵁ (chartPair H (some d) (some d)).opensRange
  have hV : Set.range (V.ι ≫ xy) ⊆ Set.range (chartPair H (some d) (some d)) := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let a := IsOpenImmersion.lift _ _ hV
  have ha : a ≫ chartPair H (some d) (some d) = V.ι ≫ xy := IsOpenImmersion.lift_fac _ _ _
  have hx : a ≫ pullback.fst g g ≫ ch H (some d) = V.ι ≫ x.1 := by
    simpa only [Category.assoc, chartPair, pullback.lift_fst, pullback.lift_fst_assoc, xy, Gfst]
      using congrArg (· ≫ Gfst H) ha
  have hy : a ≫ pullback.snd g g ≫ ch H (some d) = V.ι ≫ y.1 := by
    simpa only [Category.assoc, chartPair, pullback.lift_snd, pullback.lift_snd_assoc, xy, Gsnd]
      using congrArg (· ≫ Gsnd H) ha
  let xV : SchemeHomOver (V.ι ≫ t) g := ⟨a ≫ pullback.fst g g, by
    simpa only [Category.assoc, ch_toS, x.2] using congrArg (· ≫ toS H) hx⟩
  let yV : SchemeHomOver (V.ι ≫ t) g := ⟨a ≫ pullback.snd g g, by
    simpa only [Category.assoc, ch_toS, y.2] using congrArg (· ≫ toS H) hy⟩
  obtain ⟨O, z, hO, hmul⟩ := exists_local_division_in_chart H hL (some d) xV yV ⟨p, hd⟩
  let j := O.ι ≫ V.ι
  have hj : j ≫ t = O.ι ≫ V.ι ≫ t := Category.assoc _ _ _
  have hxO : chartPt H (some d) (schemeHomOverComp O.ι rfl xV) = schemeHomOverComp j hj x := by
    apply Subtype.ext
    simp only [chartPt, schemeHomOverComp_coe, xV, j, Category.assoc]
    rw [hx]
  have hyO : chartPt H (some d) (schemeHomOverComp O.ι rfl yV) = schemeHomOverComp j hj y := by
    apply Subtype.ext
    simp only [chartPt, schemeHomOverComp_coe, yV, j, Category.assoc]
    rw [hy]
  rw [hxO, hyO] at hmul
  refine ⟨O, j, inferInstance, ⟨z.1, z.2.trans hj.symm⟩, ⟨⟨⟨p, hd⟩, hO⟩, rfl⟩, ?_⟩
  exact Subtype.ext (congrArg Subtype.val hmul)

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
