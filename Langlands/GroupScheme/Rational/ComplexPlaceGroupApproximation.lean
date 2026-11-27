import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Torus.TorusUnirationalityProof
import Langlands.GroupScheme.SimplyConnected.CoverPreimageDerived
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction
import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.GroupScheme.Rational.NumberFieldSkewValueApproximation
import Langlands.AlgebraicGeometry.PointTopology.RealApproximationOpen
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Simultaneous approximation in complex completions of a reductive group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology NumberField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem genericPoint_mem_smoothLocus_of_charZero
    {k : Type u} [Field k] [CharZero k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left] (hf : DenseRange f.left) :
    genericPoint X.left ∈ f.left.smoothLocus := by
  let x := genericPoint X.left
  let y := f.left x
  have hy : y = genericPoint Y.left := by
    have h := (genericPoint_spec X.left).image f.left.continuous
    have hd : Dense (Set.range (fun z : X.left => f.left z)) := hf
    rw [Set.image_univ, hd.closure_eq] at h
    exact h.eq (genericPoint_spec Y.left)
  let Yy := Y.left.presheaf.stalk y
  let Xx := X.left.presheaf.stalk x
  have hYfield : IsField Yy := by
    change IsField (Y.left.presheaf.stalk y)
    rw [hy]
    exact Field.toIsField Y.left.functionField
  let : Field Yy := hYfield.toField
  let : Field Xx := inferInstanceAs (Field X.left.functionField)
  let a : k →+* Yy := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.hom.appTop ≫
    Y.left.presheaf.germ ⊤ y (by trivial)).hom
  let : CharZero Yy := charZero_of_injective_ringHom a.injective
  have := LocallyOfFiniteType.stalkMap f.left x
  rw [Scheme.Hom.mem_smoothLocus]
  change (f.left.stalkMap x).hom.FormallySmooth
  algebraize [(f.left.stalkMap x).hom]
  exact Algebra.FormallySmooth.of_perfectField

private theorem exists_affine_smooth_parameter
    {k : Type u} [Field k] [CharZero k]
    {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hX : IsUnirational k X) :
    ∃ (I : Type u) (_ : Finite I)
      (P : Over (Spec (CommRingCat.of k))) (_ : IsAffine P.left) (_ : Nonempty P.left)
      (i : P ⟶ Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
      (f : P ⟶ X), IsOpenImmersion i.left ∧ Smooth f.left := by
  obtain ⟨I, hI, U, hU, f, hf⟩ := hX
  let : Finite I := hI
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let Y := openOver k A U
  change Y ⟶ X at f
  let : Nonempty U := hU.to_subtype
  let : IsIntegral Y.left := inferInstanceAs (IsIntegral U)
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType
    (U.ι ≫ (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))))
  let : LocallyOfFiniteType (f.left ≫ X.hom) := by
    rw [Over.w f]
    exact inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  have hη := genericPoint_mem_smoothLocus_of_charZero f hf
  obtain ⟨V, hV, hηV, hVs⟩ := exists_isAffineOpen_mem_and_subset hη
  let : IsAffine V := hV
  let : Nonempty V := ⟨⟨genericPoint Y.left, hηV⟩⟩
  let P := openOver k Y V
  let g : P ⟶ X := openOverι k Y V ≫ f
  have hg : Smooth g.left := by
    change Smooth (V.ι ≫ f.left)
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_unique (fun z _ => hVs z.property)
  exact ⟨I, hI, P, hV, inferInstanceAs (Nonempty V), openOverι k Y V ≫ openOverι k A U, g,
    inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι)), hg⟩

private theorem exists_two_rationalPoints_of_smooth_parameter
    {k : Type u} [Field k] [IsAlgClosed k]
    {P : Over (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IrreducibleSpace G.X.left] [LocallyOfFiniteType G.X.hom] [Nonempty P.left]
    (f : P ⟶ G.X) [Smooth f.left] (y : rationalPoints G) :
    ∃ a c : RingPoint k P k,
      (a ≫ f)⁻¹ * (c ≫ f) = (rationalPointEquiv k G.X) y := by
  let R := G.rightTranslationIso y
  let g := f ≫ R.hom
  let : IsIso R.hom.left := (Over.forget _).map_isIso R.hom
  let : Smooth g.left := inferInstanceAs (Smooth (f.left ≫ R.hom.left))
  have hf : IsOpen (Set.range f.left) := f.left.isOpenMap.isOpen_range
  have hg : IsOpen (Set.range g.left) := g.left.isOpenMap.isOpen_range
  obtain ⟨z, hz, hz'⟩ := (hg.dense (Set.range_nonempty g.left)).inter_open_nonempty
    _ hf (Set.range_nonempty f.left)
  let W : G.X.left.Opens := ⟨Set.range f.left ∩ Set.range g.left, hf.inter hg⟩
  let X := openOver k G.X W
  let : Nonempty X.left := ⟨⟨z, hz, hz'⟩⟩
  let : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ G.X.hom))
  obtain ⟨z'⟩ := nonempty_rationalPoints X
  let p : rationalPoints G := z' ≫ openOverι k G.X W
  have hp : p.left (IsLocalRing.closedPoint k) ∈ W := (z'.left (IsLocalRing.closedPoint k)).property
  obtain ⟨a₀, ha₀⟩ := exists_rationalPoint_lift_of_mem_range g.left p.left hp.2
  obtain ⟨c₀, hc₀⟩ := exists_rationalPoint_lift_of_mem_range f.left p.left hp.1
  let a : RationalPoint k P := Over.homMk a₀ (by
    rw [← Over.w g, ← Category.assoc, ha₀, Over.w])
  let c : RationalPoint k P := Over.homMk c₀ (by
    rw [← Over.w f, ← Category.assoc, hc₀, Over.w])
  have ha : a ≫ g = p := Over.OverMorphism.ext ha₀
  have hc : c ≫ f = p := Over.OverMorphism.ext hc₀
  have h : c ≫ f = (a ≫ f) * y := by
    rw [hc, ← ha, ← Category.assoc]
    exact ((G.comp_rightTranslation y (a ≫ f)).trans (by rw [constantPoint_self]))
  refine ⟨rationalPointEquiv k P a, rationalPointEquiv k P c, ?_⟩
  rw [← rationalPointEquiv_natural, ← rationalPointEquiv_natural]
  let : Group (RingPoint k G.X k) := inferInstanceAs (Group (ringTest k k ⟶ G.X))
  change (rationalPointGroupEquiv k G (a ≫ f))⁻¹ * rationalPointGroupEquiv k G (c ≫ f) =
    rationalPointGroupEquiv k G y
  rw [h, map_mul, inv_mul_cancel_left]

private theorem polynomialCoordinates_changeRing
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (I : Type u) (p : RingPoint F (ringTest F (MvPolynomial I F)) F) (i : I) :
    spectrumAlgebraPointEquiv F K (MvPolynomial I F)
        (p.changeRing (Algebra.ofId F K)) (MvPolynomial.X i) =
      algebraMap F K (spectrumAlgebraPointEquiv F F (MvPolynomial I F) p (MvPolynomial.X i)) := by
  have h :
      spectrumAlgebraPointEquiv F K (MvPolynomial I F) (p.changeRing (Algebra.ofId F K)) =
        AlgPoint.mapCoefficients (Algebra.ofId F K)
          (spectrumAlgebraPointEquiv F F (MvPolynomial I F) p) := by
    apply AlgHom.toRingHom_injective
    let p₀ : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (MvPolynomial I F)) := p.left
    change (Spec.preimage (Spec.map (CommRingCat.ofHom
      (Algebra.ofId F K).toRingHom) ≫ p₀)).hom =
      (Algebra.ofId F K).toRingHom.comp (Spec.preimage p₀).hom
    rw [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
    rfl
  rw [h]
  rfl

private theorem exists_point_mem_open_of_openPolynomialSpectrum
    {F : Type u} [Field F] [NumberField F] {I : Type u}
    {P : Over (Spec (CommRingCat.of F))} [IsAffine P.left]
    (j : P ⟶ ringTest F (MvPolynomial I F)) [IsOpenImmersion j.left]
    (s : Set (InfinitePlace F)) (hs : s.Nonempty)
    (U : ∀ w : s, Set (RingPoint F P w.val.Completion))
    (ho : ∀ w, IsOpen (U w)) (hn : ∀ w, (U w).Nonempty) :
    ∃ p : RingPoint F P F, ∀ w : s, p.changeRing (Algebra.ofId F w.val.Completion) ∈ U w := by
  classical
  let A := ringTest F (MvPolynomial I F)
  let E (K : Type u) [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] :
      RingPoint F A K ≃ₜ (I → K) :=
    (spectrumAlgebraPointHomeomorph F K _).trans
      (AlgPoint.polynomialPointHomeomorph (R := F) (S := K) I)
  let J (w : InfinitePlace F) (p : RingPoint F P w.Completion) : RingPoint F A w.Completion :=
    p ≫ j
  have hJ (w : InfinitePlace F) : IsOpenEmbedding (J w) := by
    let := infiniteCompletionNontriviallyNormedField w
    have h := isOpenEmbedding_schemePointMap F w.Completion j
    change @IsOpenEmbedding (RingPoint F P w.Completion) (RingPoint F A w.Completion)
      (schemePointTopology F P w.Completion) (schemePointTopology F A w.Completion) (J w) at h
    rw [schemePointTopology_eq_affine F P w.Completion,
      schemePointTopology_eq_affine F A w.Completion] at h
    exact h
  let V (w : InfinitePlace F) :=
    if hw : w ∈ s then E w.Completion '' (J w '' U ⟨w, hw⟩) else Set.univ
  have hVo (w : InfinitePlace F) : IsOpen (V w) := by
    by_cases hw : w ∈ s
    · simp only [V, dite_eq_left hw]
      exact (E w.Completion).isOpenMap _ ((hJ w).isOpenMap _ (ho ⟨w, hw⟩))
    · simp only [V, dite_eq_right hw]
      exact isOpen_univ
  have hVn (w : InfinitePlace F) : (V w).Nonempty := by
    by_cases hw : w ∈ s
    · simp only [V, dite_eq_left hw]
      exact ((hn ⟨w, hw⟩).image _).image _
    · simp only [V, dite_eq_right hw]
      exact Set.univ_nonempty
  obtain ⟨a, ha, _⟩ := Global.exists_numberField_vector_mem_open (F := F) ∅ V
    (fun v => (Finset.notMem_empty v.1 v.2).elim) hVo
    (fun v => (Finset.notMem_empty v.1 v.2).elim) hVn
    (fun v => (Finset.notMem_empty v.1 v.2).elim)
  let q := (spectrumAlgebraPointEquiv F F (MvPolynomial I F)).symm
    (AlgPoint.ofAlgHom (MvPolynomial.aeval a))
  have hq (w : s) :
      q.changeRing (Algebra.ofId F w.val.Completion) ∈ J w.val '' U w := by
    have ha' := ha w.val
    simp only [V, dite_eq_left w.property] at ha'
    obtain ⟨z, hz, he⟩ := ha'
    have h : z = q.changeRing (Algebra.ofId F w.val.Completion) := by
      apply (E w.val.Completion).injective
      rw [he]
      funext i
      change algebraMap F w.val.Completion (a i) =
        spectrumAlgebraPointEquiv F w.val.Completion (MvPolynomial I F)
          (q.changeRing (Algebra.ofId F w.val.Completion)) (MvPolynomial.X i)
      rw [polynomialCoordinates_changeRing]
      simp only [q, Equiv.apply_symm_apply]
      exact congrArg (algebraMap F w.val.Completion) (MvPolynomial.aeval_X a i).symm
    exact h ▸ hz
  obtain ⟨w, hw⟩ := hs
  obtain ⟨y, _, hy⟩ := hq ⟨w, hw⟩
  let a₀ := ringTestMap F (Algebra.ofId F w.Completion)
  have hsurj : Function.Surjective a₀.left := (fieldExtension_fpqc F w.Completion).1.surj
  have hq' : Set.range q.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ := hsurj z
    refine ⟨y.left z', ?_⟩
    have h := congrArg (fun p : RingPoint F A w.Completion => p.left z') hy
    change j.left (y.left z') = q.left (a₀.left z') at h
    exact h.trans (congrArg q.left hz')
  let l := IsOpenImmersion.lift j.left q.left hq'
  have hl : l ≫ j.left = q.left := IsOpenImmersion.lift_fac j.left q.left hq'
  let p : RingPoint F P F := Over.homMk l (by
    rw [← Over.w j, ← Category.assoc, hl]
    exact Over.w q)
  have hp : p ≫ j = q := Over.OverMorphism.ext hl
  refine ⟨p, fun w => ?_⟩
  obtain ⟨z, hz, he⟩ := hq w
  have h : p.changeRing (Algebra.ofId F w.val.Completion) = z := by
    apply (hJ w.val).injective
    change (ringTestMap F (Algebra.ofId F w.val.Completion) ≫ p) ≫ j = J w.val z
    rw [Category.assoc, hp]
    exact he.symm
  exact h ▸ hz

private theorem exists_point_mem_open_of_openAffineSpace
    {F : Type u} [Field F] [NumberField F] {I : Type u}
    {P : Over (Spec (CommRingCat.of F))} [IsAffine P.left]
    (i : P ⟶ Over.mk (𝔸(I; Spec (CommRingCat.of F)) ↘ Spec (CommRingCat.of F)))
    [IsOpenImmersion i.left]
    (s : Set (InfinitePlace F)) (hs : s.Nonempty)
    (U : ∀ w : s, Set (RingPoint F P w.val.Completion))
    (ho : ∀ w, IsOpen (U w)) (hn : ∀ w, (U w).Nonempty) :
    ∃ p : RingPoint F P F, ∀ w : s, p.changeRing (Algebra.ofId F w.val.Completion) ∈ U w := by
  let e : ringTest F (MvPolynomial I F) ≅
      Over.mk (𝔸(I; Spec (CommRingCat.of F)) ↘ Spec (CommRingCat.of F)) :=
    Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of F)).symm
      (AffineSpace.SpecIso_inv_over _)
  let : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  let : IsOpenImmersion (i ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (i.left ≫ e.inv.left))
  exact exists_point_mem_open_of_openPolynomialSpectrum (i ≫ e.inv) s hs U ho hn

private theorem exists_two_local_parameterPoints
    {F K : Type u} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    {P : Over (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) [Nonempty P.left]
    (f : P ⟶ G.X) [Smooth f.left] (y : RingPoint F G.X K) :
    letI : Group (RingPoint F G.X K) := inferInstanceAs (Group (ringTest F K ⟶ G.X))
    ∃ a c : RingPoint F P K, (a ≫ f)⁻¹ * (c ≫ f) = y := by
  let b := Spec.algebraMap F K
  let Gₖ := (GroupScheme.baseChange b).obj G
  let Pₖ := ringBaseChange F K P
  let fₖ : Pₖ ⟶ Gₖ.X := (Over.pullback b).map f
  let : Surjective b := (fieldExtension_fpqc F K).1
  have hp : Surjective (pullback.fst P.hom b) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  let : Nonempty Pₖ.left := hp.surj.nonempty
  have hGₖ : IsConnectedReductive Gₖ := connectedReductiveFieldExtensionStatement F K G hG
  let : Smooth Gₖ.X.hom := hGₖ.smooth
  let : IsAffineHom Gₖ.X.hom := hGₖ.isAffineHom
  let : ConnectedSpace Gₖ.X.left := hGₖ.connectedSpace
  let : IsIntegral Gₖ.X.left := CoverPreimage.isIntegral_of_smooth_connected Gₖ
  let : Smooth fₖ.left := MorphismProperty.of_isPullback (P := @Smooth)
    (RelativeIdentityComponent.overPullback_isPullback b f).flip inferInstance
  let eP := ringPointBaseChangeEquiv F K K P
  let e := ringPointBaseChangeEquiv F K K G.X
  let : Group (RingPoint F G.X K) := inferInstanceAs (Group (ringTest F K ⟶ G.X))
  let : Group (RingPoint K Gₖ.X K) := inferInstanceAs (Group (ringTest K K ⟶ Gₖ.X))
  let E : RingPoint K Gₖ.X K ≃* RingPoint F G.X K :=
    (baseChangePointsEquiv b G (ringTest K K)).trans
      { toEquiv := Iso.homCongr (ringTestRestrictScalarsIso F K K) (Iso.refl G.X)
        map_mul' := fun x z => by
          change ((ringTestRestrictScalarsIso F K K).inv ≫ (x * z)) ≫ 𝟙 G.X =
            (((ringTestRestrictScalarsIso F K K).inv ≫ x) ≫ 𝟙 G.X) *
              (((ringTestRestrictScalarsIso F K K).inv ≫ z) ≫ 𝟙 G.X)
          simp only [Category.comp_id, MonObj.comp_mul] }
  have hE (x : RingPoint K Gₖ.X K) : E x = e.symm x := by
    apply Over.OverMorphism.ext
    change (ringTestRestrictScalarsIso F K K).inv.left ≫
      (baseChangePointsEquiv b G (ringTest K K) x).left ≫ (Iso.refl G.X).hom.left = _
    simp only [ringTestRestrictScalarsIso_inv_left, Category.id_comp, Iso.refl_hom,
      Over.id_left, Category.comp_id, baseChangePointsEquiv_left]
    exact (ringPointBaseChangeEquiv_symm_left F K K G.X x).symm
  let yₖ := (rationalPointEquiv K Gₖ.X).symm (e y)
  obtain ⟨a, c, h⟩ := exists_two_rationalPoints_of_smooth_parameter fₖ yₖ
  have he (x : RingPoint K Pₖ K) : E (x ≫ fₖ) = eP.symm x ≫ f := by
    rw [hE]
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact (congrArg (fun z => z ≫ fₖ) (eP.apply_symm_apply x)).symm.trans
      (ringPointBaseChangeEquiv_natural F K K f (eP.symm x)).symm
  refine ⟨eP.symm a, eP.symm c, ?_⟩
  have hh := congrArg E h
  change E ((a ≫ fₖ)⁻¹ * (c ≫ fₖ)) = E ((rationalPointEquiv K Gₖ.X) yₖ) at hh
  rw [map_mul, map_inv, he, he, hE] at hh
  have hyₖ : (rationalPointEquiv K Gₖ.X) yₖ = e y :=
    (rationalPointEquiv K Gₖ.X).apply_symm_apply _
  rw [hyₖ, e.symm_apply_apply] at hh
  exact hh

private theorem exists_quotientNeighborhoods
    {X Y : Type u} [TopologicalSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (f : X → Y) (hf : Continuous f) (U : Set Y) (ho : IsOpen U) {a c : X}
    (hac : (f a)⁻¹ * f c ∈ U) :
    ∃ V W : Set X, IsOpen V ∧ V.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      ∀ x ∈ V, ∀ z ∈ W, (f x)⁻¹ * f z ∈ U := by
  let m : X × X → Y := fun z => (f z.1)⁻¹ * f z.2
  have hm : Continuous m := (hf.comp continuous_fst).inv.mul (hf.comp continuous_snd)
  have hn : m ⁻¹' U ∈ 𝓝 (a, c) := (ho.preimage hm).mem_nhds hac
  obtain ⟨V, W, hV, ha, hW, hc, hVW⟩ := mem_nhds_prod_iff'.mp hn
  refine ⟨V, W, hV, ⟨a, ha⟩, hW, ⟨c, hc⟩, ?_⟩
  intro x hx z hz
  exact @hVW (x, z) ⟨hx, hz⟩

/-- Points of a connected reductive group over a number field meet
simultaneously prescribed nonempty opens at a set of complex places. -/
theorem exists_reductivePoint_mem_complexCompletion_opens
    {F : Type u} [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (hG : IsConnectedReductive G)
    (s : Set (InfinitePlace F)) (hs : s.Nonempty) (hc : ∀ w : s, w.val.IsComplex)
    (U : ∀ w : s, Set (RingPoint F G.X w.val.Completion))
    (ho : ∀ w, IsOpen (U w)) (hn : ∀ w, (U w).Nonempty) :
    ∃ p : RingPoint F G.X F, ∀ w : s, p.changeRing (Algebra.ofId F w.val.Completion) ∈ U w := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsIntegral G.X.left := CoverPreimage.isIntegral_of_smooth_connected G
  have hRat := ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality G hG
  obtain ⟨I, _, P, hP, hPn, i, f, hi, hf⟩ := exists_affine_smooth_parameter hRat
  let : IsAffine P.left := hP
  let : Nonempty P.left := hPn
  let : IsOpenImmersion i.left := hi
  let : Smooth f.left := hf
  let (w : s) : Group (RingPoint F G.X w.val.Completion) :=
    inferInstanceAs (Group (ringTest F w.val.Completion ⟶ G.X))
  have hlocal (w : s) :
      ∃ V W : Set (RingPoint F P w.val.Completion), IsOpen V ∧ V.Nonempty ∧
        IsOpen W ∧ W.Nonempty ∧
        ∀ a ∈ V, ∀ c ∈ W, (a ≫ f)⁻¹ * (c ≫ f) ∈ U w := by
    let : IsAlgClosed w.val.Completion := Langlands.Analytic.isAlgClosed_of_ringEquiv
      w.val.Completion (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hc w)).symm
    obtain ⟨y, hy⟩ := hn w
    obtain ⟨a, c, hac⟩ := exists_two_local_parameterPoints hG f y
    let : IsTopologicalGroup (RingPoint F G.X w.val.Completion) :=
      affineGroupTopological_proof F w.val.Completion G
    let g (a : RingPoint F P w.val.Completion) : RingPoint F G.X w.val.Completion := a ≫ f
    have hg : Continuous g := continuous_affineSchemePointMap F w.val.Completion f
    have hm : (g a)⁻¹ * g c ∈ U w := by change (a ≫ f)⁻¹ * (c ≫ f) ∈ U w; rwa [hac]
    exact exists_quotientNeighborhoods g hg (U w) (ho w) hm
  choose V W hV hVn hW hWn hVW using hlocal
  obtain ⟨a, ha⟩ := exists_point_mem_open_of_openAffineSpace i s hs V hV hVn
  obtain ⟨c, hcp⟩ := exists_point_mem_open_of_openAffineSpace i s hs W hW hWn
  let : Group (RingPoint F G.X F) := inferInstanceAs (Group (ringTest F F ⟶ G.X))
  refine ⟨(a ≫ f)⁻¹ * (c ≫ f), fun w => ?_⟩
  change ringTestMap F (Algebra.ofId F w.val.Completion) ≫ ((a ≫ f)⁻¹ * (c ≫ f)) ∈ U w
  rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc]
  exact hVW w _ (ha w) _ (hcp w)

end Langlands.GroupScheme
