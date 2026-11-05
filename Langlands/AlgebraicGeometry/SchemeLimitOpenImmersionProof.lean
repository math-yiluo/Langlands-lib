import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionStatement
import Langlands.AlgebraicGeometry.SchemeLimitAffineProof

/-! # Proof of open-immersion descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

open EtaleEquivalenceRelation.Action.TargetLimit

section OpenImage

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}} [IsAffine S]
  [∀ i, IsAffine (D.obj i)] (t : D ⟶ (Functor.const I).obj S)
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
  [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

private instance {i j : I} (r : i ⟶ j) :
    IsAffineHom ((diagram D t b).map r) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (diagram_map_isPullback b D t r).flip inferInstance

private instance (i : I) : CompactSpace ((diagram D t b).obj i) := by
  change CompactSpace (pullback (t.app i) b : Scheme.{u})
  infer_instance

private instance (i : I) : QuasiSeparatedSpace ((diagram D t b).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) b)

omit [IsCofiltered I] [IsAffine S] [∀ i, IsAffine (D.obj i)]
  [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b] in
private lemma opensCone_ι (i : I) (V : ((diagram D t b).obj i).Opens)
    (j : Over i) :
    (opensCone (diagram D t b) (cone D t b c p hp) i V).π.app j ≫
      (opensDiagramι (diagram D t b) i V).app j =
      ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι ≫
        (cone D t b c p hp).π.app j.left := by
  simp [opensCone, opensDiagramι]

include hc in
omit [IsAffine S] [LocallyOfFinitePresentation a] [QuasiSeparated a]
  [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b] in
lemma exists_open_image_level [IsOpenImmersion (baseChangeMap a b f w p)] :
    ∃ (i : I) (V : ((diagram D t b).obj i).Opens),
      IsCompact (V : Set ((diagram D t b).obj i)) ∧
      (cone D t b c p hp).π.app i ⁻¹ᵁ V = (baseChangeMap a b f w p).opensRange := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : CompactSpace (pullback p a : Scheme.{u}) := by infer_instance
  exact exists_preimage_eq (diagram D t b) (cone D t b c p hp)
    (isLimitCone D t b c p hp hc) (baseChangeMap a b f w p).opensRange
    (isCompact_range (baseChangeMap a b f w p).continuous)

include hc in
omit [IsAffine S] [LocallyOfFinitePresentation a] [QuasiSeparated a]
  [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b] in
lemma exists_open_image_level_full [IsOpenImmersion (baseChangeMap a b f w p)] :
    ∃ (i : I) (V : ((diagram D t b).obj i).Opens),
      IsCompact (V : Set ((diagram D t b).obj i)) ∧
      (cone D t b c p hp).π.app i ⁻¹ᵁ V = (baseChangeMap a b f w p).opensRange ∧
      baseChangeMap a b f w (t.app i) ⁻¹ᵁ V = ⊤ := by
  obtain ⟨i, V, hVc, hV⟩ := exists_open_image_level D t a b f w c hc p hp
  have htop : (cone D t a c p hp).π.app i ⁻¹ᵁ
      (baseChangeMap a b f w (t.app i) ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, cone_baseChangeMap,
      Scheme.Hom.comp_preimage, hV]
    ext x
    exact iff_true_intro ⟨x, rfl⟩
  obtain ⟨j, r, hr⟩ := exists_map_eq_top (diagram D t a)
    (cone D t a c p hp) (isLimitCone D t a c p hp hc) _ htop
  refine ⟨j, (diagram D t b).map r ⁻¹ᵁ V,
    ((diagram D t b).map r).isCompact_preimage hVc, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, (cone D t b c p hp).w, hV]
  · rwa [← Scheme.Hom.comp_preimage, ← baseChangeMap_naturality,
      Scheme.Hom.comp_preimage]

include hc in
omit [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] in
lemma exists_inverse_open_level (i : I)
    (V : ((diagram D t b).obj i).Opens)
    (hVc : IsCompact (V : Set ((diagram D t b).obj i)))
    (e : pullback p a ≅ (opensCone (diagram D t b) (cone D t b c p hp) i V).pt)
    (he : e.hom ≫ ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι =
      baseChangeMap a b f w p) :
    ∃ (j : Over i) (g : (opensDiagram (diagram D t b) i V).obj j ⟶ X),
      (opensCone (diagram D t b) (cone D t b c p hp) i V).π.app j ≫ g =
        e.inv ≫ pullback.snd p a ∧
      g ≫ a = (opensDiagramι (diagram D t b) i V).app j ≫
        pullback.snd (t.app j.left) b ≫ b ∧
      g ≫ f = (opensDiagramι (diagram D t b) i V).app j ≫
        pullback.snd (t.app j.left) b := by
  let E := opensDiagram (diagram D t b) i V
  let cE := opensCone (diagram D t b) (cone D t b c p hp) i V
  let tE : E ⟶ (Functor.const (Over i)).obj S :=
    opensDiagramι (diagram D t b) i V ≫
      Functor.whiskerLeft (Over.forget i)
        (comparison D t b ≫ (Functor.const I).map b)
  have (j : Over i) : CompactSpace (E.obj j) := by
    change CompactSpace ((diagram D t b).map j.hom ⁻¹ᵁ V : Scheme.{u})
    exact isCompact_iff_compactSpace.mp (((diagram D t b).map j.hom).isCompact_preimage hVc)
  have (j : Over i) : QuasiSeparatedSpace (E.obj j) := by
    change QuasiSeparatedSpace ((diagram D t b).map j.hom ⁻¹ᵁ V : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated
      (((diagram D t b).map j.hom ⁻¹ᵁ V).ι)
  have hcE := isLimitOpensCone (diagram D t b) (cone D t b c p hp)
    (isLimitCone D t b c p hp hc) i V
  have hei : e.inv ≫ baseChangeMap a b f w p =
      ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι := by
    rw [← he, e.inv_hom_id_assoc]
  have hbase : (e.inv ≫ pullback.snd p a) ≫ a =
      ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι ≫ pullback.snd p b ≫ b := by
    have hright : (e.inv ≫ pullback.snd p a) ≫ f =
        ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι ≫ pullback.snd p b := by
      rw [Category.assoc, ← baseChangeMap_snd a b f w p,
        ← Category.assoc, hei]
    simpa only [Category.assoc, w] using congrArg (fun z ↦ z ≫ b) hright
  obtain ⟨j, g, hg, hga⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      E tE a cE hcE (e.inv ≫ pullback.snd p a) (by
        ext j
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, comparison,
          Functor.const_map_app, tE, Category.assoc, Over.forget_obj]
        rw [← Category.assoc, opensCone_ι, Category.assoc,
          cone_π_snd_assoc]
        exact hbase.symm)
  have hgf : cE.π.app j ≫ (g ≫ f) =
      cE.π.app j ≫ ((opensDiagramι (diagram D t b) i V).app j ≫
        pullback.snd (t.app j.left) b) := by
    rw [← Category.assoc, hg, Category.assoc,
      ← baseChangeMap_snd a b f w p, ← Category.assoc, hei,
      ← Category.assoc, opensCone_ι, Category.assoc, cone_π_snd]
  obtain ⟨k, r, hr⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    E tE b cE hcE (g ≫ f)
    ((opensDiagramι (diagram D t b) i V).app j ≫ pullback.snd (t.app j.left) b)
    (by rw [Category.assoc, w, hga]) rfl hgf
  refine ⟨k, E.map r ≫ g, ?_, ?_, ?_⟩
  · rw [← Category.assoc, cE.w, hg]
  · rw [Category.assoc, hga]
    simp only [tE, NatTrans.comp_app, Functor.whiskerLeft_app,
      comparison, Functor.const_map_app, ← Category.assoc]
    rw [(opensDiagramι (diagram D t b) i V).naturality]
    simp
  · rw [Category.assoc, hr, ← Category.assoc,
      (opensDiagramι (diagram D t b) i V).naturality]
    simp

include hc hp in
omit [IsAffine S] [QuasiSeparated a] [QuasiCompact b] in
lemma exists_isOpenImmersion_baseChangeMap
    [IsOpenImmersion (baseChangeMap a b f w p)] :
    ∃ i : I, IsOpenImmersion (baseChangeMap a b f w (t.app i)) := by
  obtain ⟨i, V, hVc, hV, htop⟩ := exists_open_image_level_full D t a b f w c hc p hp
  let E := opensDiagram (diagram D t b) i V
  let cE := opensCone (diagram D t b) (cone D t b c p hp) i V
  let W : (pullback p b).Opens := (cone D t b c p hp).π.app i ⁻¹ᵁ V
  have hrange : Set.range (baseChangeMap a b f w p) = Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun U : (pullback p b).Opens ↦ (U : Set (pullback p b : Scheme.{u})))
      hV.symm
  let e : pullback p a ≅ cE.pt :=
    IsOpenImmersion.isoOfRangeEq (baseChangeMap a b f w p) W.ι hrange
  have he : e.hom ≫ ((cone D t b c p hp).π.app i ⁻¹ᵁ V).ι =
      baseChangeMap a b f w p := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨j, g, hg, hga, hgf⟩ :=
    exists_inverse_open_level D t a b f w c hc p hp i V hVc e he
  have hpre (j : Over i) :
      baseChangeMap a b f w (t.app j.left) ⁻¹ᵁ
        ((diagram D t b).map j.hom ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, ← baseChangeMap_naturality,
      Scheme.Hom.comp_preimage, htop]
    simp
  let L (j : Over i) : (diagram D t a).obj j.left ⟶ E.obj j :=
    IsOpenImmersion.lift ((opensDiagramι (diagram D t b) i V).app j)
      (baseChangeMap a b f w (t.app j.left)) (by
        change Set.range (baseChangeMap a b f w (t.app j.left)) ⊆
          Set.range (((diagram D t b).map j.hom ⁻¹ᵁ V).ι)
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ baseChangeMap a b f w (t.app j.left) ⁻¹ᵁ
            ((diagram D t b).map j.hom ⁻¹ᵁ V) := by
          rw [hpre]
          trivial
        exact hx)
  have hL (j : Over i) :
      L j ≫ (opensDiagramι (diagram D t b) i V).app j =
        baseChangeMap a b f w (t.app j.left) :=
    IsOpenImmersion.lift_fac _ _ _
  have hLn {j k : Over i} (r : j ⟶ k) :
      (diagram D t a).map r.left ≫ L k = L j ≫ E.map r := by
    rw [← cancel_mono ((opensDiagramι (diagram D t b) i V).app k)]
    rw [Category.assoc, hL, Category.assoc,
      (opensDiagramι (diagram D t b) i V).naturality,
      ← Category.assoc, hL]
    exact baseChangeMap_naturality D t a b f w r.left
  have hcone (j : Over i) :
      (cone D t a c p hp).π.app j.left ≫ L j = e.hom ≫ cE.π.app j := by
    rw [← cancel_mono ((opensDiagramι (diagram D t b) i V).app j)]
    rw [Category.assoc, hL, Category.assoc, opensCone_ι,
      ← Category.assoc, he, cone_baseChangeMap]
  have hleftlim : (cone D t a c p hp).π.app j.left ≫ (L j ≫ g) =
      (cone D t a c p hp).π.app j.left ≫ pullback.snd (t.app j.left) a := by
    rw [← Category.assoc, hcone, Category.assoc, hg,
      e.hom_inv_id_assoc, cone_π_snd]
  let tA := comparison D t a ≫ (Functor.const I).map a
  obtain ⟨k, s, hs⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D t a) tA a (cone D t a c p hp) (isLimitCone D t a c p hp hc)
    (L j ≫ g) (pullback.snd (t.app j.left) a)
    (by
      dsimp [tA, comparison]
      rw [Category.assoc, hga, ← Category.assoc, hL,
        baseChangeMap_snd_assoc, w])
    rfl hleftlim
  let m : Over i := Over.mk (s ≫ j.hom)
  let r : m ⟶ j := Over.homMk s rfl
  let gm : E.obj m ⟶ X := E.map r ≫ g
  have hgm : gm ≫ a = (opensDiagramι (diagram D t b) i V).app m ≫
      pullback.snd (t.app k) b ≫ b := by
    dsimp [gm]
    rw [Category.assoc, hga, ← Category.assoc,
      (opensDiagramι (diagram D t b) i V).naturality]
    simp [m]
  have hright : gm ≫ f = (opensDiagramι (diagram D t b) i V).app m ≫
      pullback.snd (t.app k) b := by
    dsimp [gm]
    rw [Category.assoc, hgf, ← Category.assoc,
      (opensDiagramι (diagram D t b) i V).naturality]
    simp [m]
  have hleft : L m ≫ gm = pullback.snd (t.app k) a := by
    dsimp [gm]
    rw [← Category.assoc, ← hLn, Category.assoc]
    change (diagram D t a).map s ≫ (L j ≫ g) = pullback.snd (t.app k) a
    simpa only [diagram_map_snd] using hs
  let G : E.obj m ⟶ pullback (t.app k) a :=
    pullback.lift
      ((opensDiagramι (diagram D t b) i V).app m ≫ pullback.fst (t.app k) b)
      gm (by rw [Category.assoc, pullback.condition, hgm])
  have hLG : L m ≫ G = 𝟙 _ := by
    change L m ≫ G = 𝟙 (pullback (t.app k) a)
    apply pullback.hom_ext
    · simp only [G, pullback.lift_fst, Category.assoc]
      rw [← Category.assoc, hL]
      exact baseChangeMap_fst a b f w (t.app k)
    · change (L m ≫ G) ≫ pullback.snd (t.app k) a =
        𝟙 (pullback (t.app k) a) ≫ pullback.snd (t.app k) a
      rw [Category.id_comp, Category.assoc, show G ≫ pullback.snd (t.app k) a = gm
        from pullback.lift_snd _ _ _]
      exact hleft
  have hGL : G ≫ L m = 𝟙 _ := by
    rw [← cancel_mono ((opensDiagramι (diagram D t b) i V).app m),
      Category.assoc, hL, Category.id_comp]
    change G ≫ baseChangeMap a b f w (t.app k) =
      (opensDiagramι (diagram D t b) i V).app m
    apply pullback.hom_ext
    · simp [G]
    · simpa only [Category.assoc, baseChangeMap_snd, G, pullback.lift_snd_assoc]
        using hright
  have : IsIso (L m) := ⟨G, hLG, hGL⟩
  refine ⟨k, ?_⟩
  change IsOpenImmersion (baseChangeMap a b f w (t.app m.left))
  rw [← hL m]
  infer_instance

end OpenImage

/-- Open immersion is detected at a stage for finitely presented models. -/
theorem relativeOpenImmersionDescent : RelativeOpenImmersionDescent.{u} := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  constructor
  · intro H
    let := H
    exact exists_isOpenImmersion_baseChangeMap D t a b f w c hc p hp
  · rintro ⟨i, H⟩
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (cone_baseChangeMap_isPullback a b f w D t c p hp i).flip H

end Langlands.AlgebraicGeometry.AffineLimit
