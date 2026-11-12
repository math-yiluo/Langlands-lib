import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFinitenessStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientOrbitRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleRelationQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationRelationQuotient

/-!
# Quasi-separatedness and finite presentation of action quotients over a field

This module proves `ActionQuotientFinitenessStatement`. Quasi-separatedness: the action map
`G × Z → Z ×_X Z` is surjective because the fppf quotient factors through the sheafified
point quotient, so the kernel pair `Z ×_X Z` is quasi-compact; it maps to the locally
Noetherian `Z × Z`, and quasi-compactness of the diagonal descends along the smooth surjection
`Z × Z → X × X`. Finite presentation: finitely many quasi-compact opens of an étale atlas,
whose images cover the quasi-compact `Z`, give a quasi-compact étale atlas; its surjectivity
descends along `π`.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ActionQuotientFiniteness

section Descent

variable {S : Scheme.{u}}

/-- A representable map has a scheme property `P` that descends along fppf covers as soon as
its base change along one smooth surjective scheme cover of the target has `P`. -/
theorem relative_of_isSmooth_isSurjective (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {F G : Presheaf S} {f : F ⟶ G} (hf : IsRepresentableMorphism f)
    {W V₀ : Over S} {A : (schemeYoneda S).obj W ⟶ G} (hA : IsSmooth A) (hAs : IsSurjective A)
    (b₀ : (schemeYoneda S).obj V₀ ⟶ F) (p₀ : V₀ ⟶ W)
    (h₀ : IsPullback b₀ ((schemeYoneda S).map p₀) f A) (hp₀ : P p₀.left) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) f := by
  refine ⟨hf, ?_⟩
  intro T V g b p hsq
  let Y := schemeYoneda S
  let hA' := hA.representable
  let pT := hA'.snd g
  let fT := Functor.relativelyRepresentable.fst' hA' g
  have hT : IsPullback (Y.map fT) (Y.map pT) A g :=
    Functor.relativelyRepresentable.isPullback' hA' g
  have : Smooth pT.left := hA.projection g _ pT hT
  have hpTs : Surjective pT.left := hAs.projection g _ pT hT
  let π₁ := pullback.fst p pT
  let π₂ := pullback.snd p pT
  have hsq₂ : IsPullback π₁ π₂ p pT := IsPullback.of_hasPullback p pT
  have hbig := (hsq₂.map Y).paste_horiz hsq
  rw [← hT.w] at hbig
  let k := h₀.lift (Y.map π₁ ≫ b) (Y.map π₂ ≫ Y.map fT) (by simpa using hbig.w)
  have hleft : IsPullback k (Y.map π₂) (Y.map p₀) (Y.map fT) :=
    IsPullback.of_right (by rwa [h₀.lift_fst]) (h₀.lift_snd _ _ _) h₀
  have hπ₂ : P π₂.left :=
    (MorphismProperty.relative_map (F := Y) (P := P.inverseImage (Over.forget S)) hp₀).property
      _ k π₂ hleft
  change P p.left
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (hsq₂.map (Over.forget S)).flip
    ⟨⟨hpTs, (inferInstance : Flat pT.left)⟩,
      (inferInstance : LocallyOfFinitePresentation pT.left)⟩ hπ₂

/-- Quasi-compactness descends along surjective quasi-compact scheme morphisms. -/
theorem quasiCompact_descendsAlong_surjective_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@QuasiCompact.{u}) (@Surjective.{u} ⊓ @QuasiCompact.{u}) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro T V W f g _ hf hfst
  have : Surjective f := hf.1
  have : QuasiCompact f := hf.2
  have : QuasiCompact (Limits.pullback.fst f g) := hfst
  have : QuasiCompact (Limits.pullback.snd f g ≫ g) := by
    rw [← Limits.pullback.condition]
    infer_instance
  constructor
  intro A hAo hAc
  have hc := QuasiCompact.isCompact_preimage
    (f := Limits.pullback.snd f g ≫ g) A hAo hAc
  have hi := hc.image (Limits.pullback.snd f g).continuous
  have : Surjective (Limits.pullback.snd f g) := inferInstance
  change IsCompact (Limits.pullback.snd f g ''
    (Limits.pullback.snd f g ⁻¹' (g ⁻¹' A))) at hi
  rwa [Set.image_preimage_eq _ (Limits.pullback.snd f g).surjective] at hi

/-- Quasi-compactness descends along fppf coverings. -/
theorem quasiCompact_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@QuasiCompact.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) := by
  have := quasiCompact_descendsAlong_surjective_inf_quasiCompact.{u}
  have : MorphismProperty.DescendsAlong (@QuasiCompact.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) :=
    MorphismProperty.DescendsAlong.of_le (Q := @Surjective.{u} ⊓ @QuasiCompact.{u})
      (fun _ _ _ h ↦ ⟨h.1.1, h.2⟩)
  exact
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @QuasiCompact

/-- Surjectivity descends along fppf coverings. -/
theorem surjective_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@Surjective.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
  MorphismProperty.DescendsAlong.of_le (Q := @Surjective.{u}) (fun _ _ _ h ↦ h.1.1)

/-- `prod.map (𝟙 X) f` is the base change of `f` along the second projection. -/
theorem isPullback_snd_map_id {C : Type*} [Category C] [HasBinaryProducts C]
    {A B : C} (f : A ⟶ B) (X : C) :
    IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift (s.snd ≫ prod.fst) s.fst, ?_, ?_, ?_⟩
    · simp
    · ext
      · simp
      · simp [PullbackCone.condition]
    · intro m h₁ h₂
      apply prod.hom_ext
      · simpa using congrArg (· ≫ prod.fst) h₂
      · simpa using h₁)⟩

/-- A relative scheme property stable under composition is stable under products of maps. -/
theorem relative_prod_map (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    {F G H K : Presheaf S} {f : F ⟶ G} {g : H ⟶ K}
    (hf : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) f)
    (hg : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) g) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (prod.map f g) := by
  let W := (P.inverseImage (Over.forget S)).relative (schemeYoneda S)
  have : W.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have h₁ : W (prod.map f (𝟙 H)) :=
    W.of_isPullback (IsPullback.of_prod_fst_with_id f H) hf
  have h₂ : W (prod.map (𝟙 G) g) := W.of_isPullback (isPullback_snd_map_id g G) hg
  have hw : prod.map f g = prod.map f (𝟙 H) ≫ prod.map (𝟙 G) g := by
    apply prod.hom_ext <;> simp
  rw [hw]
  exact W.comp_mem _ _ h₁ h₂

/-- A quasi-compact kernel-pair comparison for one smooth surjective scheme cover makes the
space quasi-separated. -/
theorem isQuasiSeparated_of_smooth_cover {X : AlgebraicSpace S} {U R : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsSmooth a) (hs : IsSurjective a)
    (t s : R ⟶ U)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hj : QuasiCompact (prod.lift t s).left) :
    IsQuasiSeparated X := by
  let Y := schemeYoneda S
  let j : R ⟶ U ⨯ U := prod.lift t s
  let e : Y.obj (U ⨯ U) ≅ Y.obj U ⨯ Y.obj U := PreservesLimitPair.iso Y U U
  let A : Y.obj (U ⨯ U) ⟶ X.presheaf ⨯ X.presheaf := e.hom ≫ prod.map a a
  have hAe : IsSmooth A := by
    change (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Smooth.{u}) ha ha)
  have hAs : IsSurjective A := by
    change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Surjective.{u}) hs hs)
  have hjmap : Y.map j ≫ e.hom = prod.lift (Y.map t) (Y.map s) := by
    apply prod.hom_ext <;> simp [e, PreservesLimitPair.iso_hom, j, ← Functor.map_comp]
  have hsq : IsPullback (Y.map t ≫ a) (Y.map j) (diag X.presheaf) A := by
    apply (FinitePresentationRelationQuotient.isPullback_kernel_diagonal h).of_iso'
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simpa using hjmap.symm
    · simp
    · simp [A]
  have := quasiCompact_descendsAlong_fppf.{u}
  exact relative_of_isSmooth_isSurjective (@QuasiCompact.{u})
    X.hasRepresentableDiagonal hAe hAs (Y.map t ≫ a) j hsq hj

end Descent

section Action

variable {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S} (b : SchemeAction G Z)

/-- Two points are related by the action graph exactly when one is a translate of the other. -/
theorem pointRel_iff {T : Over S} (x y : ULift.{u + 1} (T ⟶ Z)) :
    RelationQuotient.PointRel b.hom (snd G.X Z) T x y ↔
      ∃ g : T ⟶ G.X, b.act g y.down = x.down := by
  constructor
  · rintro ⟨r, hr₁, hr₂⟩
    refine ⟨r ≫ fst G.X Z, ?_⟩
    rw [← hr₁, ← hr₂, SchemeAction.act, lift_comp_fst_snd]
  · rintro ⟨g, hg⟩
    exact ⟨lift g y.down, hg, lift_snd _ _⟩

/-- Translation by points of a group scheme is an equivalence relation on points. -/
theorem pointRel_equivalence (T : Over S) :
    Equivalence (RelationQuotient.PointRel b.hom (snd G.X Z) T) := by
  refine ⟨fun x => (pointRel_iff b x x).2 ⟨1, b.act_one _⟩, ?_, ?_⟩
  · intro x y h
    obtain ⟨g, hg⟩ := (pointRel_iff b x y).1 h
    refine (pointRel_iff b y x).2 ⟨g⁻¹, ?_⟩
    rw [← hg, ← b.act_mul, inv_mul_cancel, b.act_one]
  · intro x y z h h'
    obtain ⟨g, hg⟩ := (pointRel_iff b x y).1 h
    obtain ⟨g', hg'⟩ := (pointRel_iff b y z).1 h'
    refine (pointRel_iff b x z).2 ⟨g * g', ?_⟩
    rw [b.act_mul, hg', hg]

/-- Two points with the same image in an fppf action quotient are translates of each other
on an fppf covering. -/
theorem exists_covering_act {X : FppfSheaf S} {π : (schemeSheaf S).obj Z ⟶ X}
    (hπ : IsFppfActionQuotient b π) {T : Over S} (x y : T ⟶ Z)
    (hxy : π.hom.app (op T) ⟨x⟩ = π.hom.app (op T) ⟨y⟩) :
    ∃ J ∈ fppfTopology S T, ∀ ⦃V : Over S⦄ (f : V ⟶ T), J f →
      ∃ g : V ⟶ G.X, b.act g (f ≫ y) = f ≫ x := by
  obtain ⟨w, ⟨hc⟩⟩ := hπ
  let t := b.hom
  let s := snd G.X Z
  let q : (schemeSheaf S).obj Z ⟶ RelationQuotient.quotientSheaf t s :=
    ⟨RelationQuotient.quotientMap t s⟩
  have hq : (schemeSheaf S).map b.hom ≫ q = (schemeSheaf S).map (snd G.X Z) ≫ q := by
    ext1
    exact RelationQuotient.quotientMap_w t s
  let u := Cofork.IsColimit.desc hc q hq
  have hu : π ≫ u = q := Cofork.IsColimit.π_desc hc
  have e : ∀ z : T ⟶ Z, (RelationQuotient.quotientMap t s).app (op T) ⟨z⟩ =
      u.hom.app (op T) (π.hom.app (op T) ⟨z⟩) := by
    intro z
    change q.hom.app (op T) ⟨z⟩ = _
    rw [← hu]
    rfl
  have heq : (RelationQuotient.quotientMap t s).app (op T) ⟨x⟩ =
      (RelationQuotient.quotientMap t s).app (op T) ⟨y⟩ := by
    rw [e, e, hxy]
  refine ⟨Presheaf.equalizerSieve ((RelationQuotient.quotientπ t s).app (op T) ⟨x⟩)
      ((RelationQuotient.quotientπ t s).app (op T) ⟨y⟩),
    Presheaf.equalizerSieve_mem (fppfTopology S)
      (CategoryTheory.toSheafify (fppfTopology S) (RelationQuotient.quotientPresheaf t s))
      _ _ heq, ?_⟩
  intro V f hf
  have hf' : RelationQuotient.PointRel t s V ⟨f ≫ x⟩ ⟨f ≫ y⟩ :=
    (pointRel_equivalence b V).eqvGen_iff.1 (Quot.eqvGen_exact hf)
  exact (pointRel_iff b _ _).1 hf'

/-- The action graph surjects onto the kernel pair of an fppf action quotient map. -/
theorem surjective_of_kernelPair {X : FppfSheaf S} {π : (schemeSheaf S).obj Z ⟶ X}
    (hπ : IsFppfActionQuotient b π) {R : Over S} (t s : R ⟶ Z)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) π.hom π.hom)
    (φ : G.X ⊗ Z ⟶ R) (hφt : φ ≫ t = b.hom) (hφs : φ ≫ s = snd G.X Z) :
    Surjective φ.left := by
  let Y := schemeYoneda S
  have hts : π.hom.app (op R) ⟨t⟩ = π.hom.app (op R) ⟨s⟩ := by
    have := congrArg (fun ψ => ψ.app (op R) ⟨𝟙 R⟩) h.w
    exact this
  obtain ⟨J, hJ, hloc⟩ := exists_covering_act b hπ t s hts
  have hfac : ∀ ⦃V : Over S⦄ (f : V ⟶ R), J f → ∃ k : V ⟶ G.X ⊗ Z, k ≫ φ = f := by
    intro V f hf
    obtain ⟨g, hg⟩ := hloc f hf
    refine ⟨lift g (f ≫ s), ?_⟩
    apply Y.map_injective
    apply h.hom_ext
    · rw [← Y.map_comp, ← Y.map_comp, Category.assoc, hφt]
      exact congrArg Y.map hg
    · rw [← Y.map_comp, ← Y.map_comp, Category.assoc, hφs, lift_snd]
  rw [GrothendieckTopology.mem_over_iff] at hJ
  have hJ' := Scheme.grothendieckTopology_monotone
    (P := @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) (Q := ⊤) le_top R.left hJ
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology (P := ⊤) hJ'
  constructor
  intro r
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq r
  have hi := h𝒰 (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)
  rw [Sieve.overEquiv_iff] at hi
  obtain ⟨k, hk⟩ := hfac _ hi
  refine ⟨k.left z, ?_⟩
  have hk' := congrArg (fun m => m.left) hk
  simp only [Over.comp_left, Over.homMk_left] at hk'
  rw [← hz, ← Scheme.Hom.comp_apply, hk']
  rfl

end Action

section FinitePresentation

variable {k : Type u} [Field k]

/-- An algebraic space over a field, locally of finite type, that receives a smooth
surjective map from a quasi-compact scheme is of finite presentation. -/
theorem finitePresentation_of_smooth_cover {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    {Z : Over (Spec (CommRingCat.of k))} [CompactSpace Z.left]
    (π : (schemeYoneda _).obj Z ⟶ X.presheaf) (hπ : IsSmooth π) (hπs : IsSurjective π)
    (hX : LocallyOfFiniteTypeOverBase X) : FinitePresentationOverRing k X := by
  obtain ⟨U, a, ha, has, hU⟩ := hX
  have : LocallyOfFiniteType U.hom := hU
  let Y := schemeYoneda (Spec (CommRingCat.of k))
  let hr := ha.representable
  let W := hr.pullback π
  let p : W ⟶ Z := hr.snd π
  let q : W ⟶ U := Functor.relativelyRepresentable.fst' hr π
  have sq : IsPullback (Y.map q) (Y.map p) a π := Functor.relativelyRepresentable.isPullback' hr π
  have : Etale p.left := ha.projection π _ p sq
  have hps : Surjective p.left := has.projection π _ p sq
  have : Smooth q.left := hπ.projection a _ q sq.flip
  have hnbhd : ∀ w : W.left, ∃ V : W.left.Opens, IsCompact (V : Set W.left) ∧ w ∈ V := by
    intro w
    obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset (x := w) (U := ⊤) trivial
    exact ⟨V, hV.isCompact, hwV⟩
  choose V hVc hVw using hnbhd
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun w => p.left '' (V w))
    (fun w => p.left.isOpenMap _ (V w).isOpen) (by
      intro z _
      obtain ⟨w, rfl⟩ := hps.surj z
      exact Set.mem_iUnion.2 ⟨w, w, hVw w, rfl⟩)
  let O : U.left.Opens := ⨆ w ∈ t, ⟨q.left '' (V w), q.left.isOpenMap _ (V w).isOpen⟩
  have hOc : IsCompact (O : Set U.left) := by
    simp only [O, TopologicalSpace.Opens.coe_iSup]
    exact t.isCompact_biUnion fun w _ => (hVc w).image q.left.continuous
  have : CompactSpace O := isCompact_iff_compactSpace.mp hOc
  let U' : Over (Spec (CommRingCat.of k)) := Over.mk (O.ι ≫ U.hom)
  let incl : U' ⟶ U := Over.homMk O.ι
  let a' := Y.map incl ≫ a
  have ha' : IsEtale a' := (isEtale_map incl (inferInstanceAs (Etale O.ι))).comp ha
  have has' : IsSurjective a' := by
    have hsq₀ : IsPullback (Y.map (pullback.snd q incl)) (Y.map (pullback.fst q incl ≫ p)) a' π := by
      rw [Y.map_comp]
      exact ((IsPullback.of_hasPullback q incl).flip.map Y).paste_vert sq
    have hsurj₀ : Surjective (pullback.fst q incl ≫ p).left := by
      constructor
      intro z
      obtain ⟨w, hz⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ z))
      obtain ⟨hwt, hz⟩ := Set.mem_iUnion.1 hz
      obtain ⟨w', hw'V, rfl⟩ := hz
      have hmem : q.left w' ∈ O := by
        simp only [O, TopologicalSpace.Opens.mem_iSup]
        exact ⟨w, hwt, w', hw'V, rfl⟩
      have hsq := (IsPullback.of_hasPullback q incl).map (Over.forget _)
      obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback hsq w'
        (⟨q.left w', hmem⟩ : O) rfl
      exact ⟨v, by simpa using congrArg p.left hv⟩
    have := surjective_descendsAlong_fppf.{u}
    exact relative_of_isSmooth_isSurjective (@Surjective.{u})
      (X.representable_from_scheme a') hπ hπs _ _ hsq₀ hsurj₀
  refine ⟨U', a', ha', has', ?_, ?_⟩
  · change LocallyOfFinitePresentation (O.ι ≫ U.hom)
    infer_instance
  · change QuasiCompact (O.ι ≫ U.hom)
    infer_instance

end FinitePresentation


variable {S : Scheme.{u}}

/-- Quasi-separatedness of an action quotient over a field with smooth surjective quotient
map. -/
theorem isQuasiSeparated {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {Z : Over (Spec (CommRingCat.of k))} (b : SchemeAction G Z)
    [QuasiCompact G.X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} {π : (schemeSheaf _).obj Z ⟶ X.toSheaf}
    (hπ : IsFppfActionQuotient b π) (hπS : IsSmooth π.hom) (hπs : IsSurjective π.hom) :
    IsQuasiSeparated X := by
  let Y := schemeYoneda (Spec (CommRingCat.of k))
  let p : Y.obj Z ⟶ X.presheaf := π.hom
  let hr := hπS.representable
  let R := hr.pullback p
  let s : R ⟶ Z := hr.snd p
  let t : R ⟶ Z := Y.preimage (hr.fst p)
  have hsq : IsPullback (Y.map t) (Y.map s) p p := by
    rw [Y.map_preimage]
    exact hr.isPullback p
  have : Smooth s.left := hπS.projection p (hr.fst p) s (hr.isPullback p)
  have hw : Y.map b.hom ≫ p = Y.map (snd G.X Z) ≫ p := congrArg (fun φ ↦ φ.hom) hπ.1
  let orbitMap : G.X ⊗ Z ⟶ R := Y.preimage (hsq.lift (Y.map b.hom) (Y.map (snd G.X Z)) hw)
  have hγt : orbitMap ≫ t = b.hom :=
    Y.map_injective (by rw [Y.map_comp, Y.map_preimage, hsq.lift_fst])
  have hγs : orbitMap ≫ s = snd G.X Z :=
    Y.map_injective (by rw [Y.map_comp, Y.map_preimage, hsq.lift_snd])
  have hγ : Function.Surjective orbitMap.left := by
    intro r
    have hxy : π.hom.app (op R) ⟨t⟩ = π.hom.app (op R) ⟨s⟩ :=
      (app_eq_iff_of_isPullback p t s hsq t s).2 ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
    obtain ⟨V, f, ⟨g, hg⟩, v, hv⟩ := ActionQuotientOrbitRelation.exists_mem_range_of_mem
      (ActionQuotientOrbitRelation.orbitSieve_mem b hπ t s hxy) r
    have hfac : lift g (f ≫ s) ≫ orbitMap = f := by
      apply Y.map_injective
      apply hsq.hom_ext
      · simp only [← Functor.map_comp, Category.assoc, hγt]
        congr 1
        rw [hg]
        rfl
      · simp only [← Functor.map_comp, Category.assoc, hγs, lift_snd]
    refine ⟨(lift g (f ≫ s)).left v, ?_⟩
    calc orbitMap.left ((lift g (f ≫ s)).left v) = (lift g (f ≫ s) ≫ orbitMap).left v := rfl
      _ = f.left v := by rw [hfac]
      _ = r := hv
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : CompactSpace (G.X ⊗ Z).left :=
    inferInstanceAs (CompactSpace ↑(CategoryTheory.Limits.pullback (C := Scheme.{u}) G.X.hom Z.hom))
  have : CompactSpace R.left := by
    constructor
    have hc := (isCompact_univ (X := (G.X ⊗ Z).left)).image orbitMap.left.continuous
    rwa [Set.image_univ_of_surjective hγ] at hc
  have : LocallyOfFiniteType R.hom := by
    rw [← Over.w s]
    infer_instance
  have : IsLocallyNoetherian R.left := LocallyOfFiniteType.isLocallyNoetherian R.hom
  have : IsNoetherian R.left := ⟨⟩
  exact isQuasiSeparated_of_smooth_cover p hπS hπs t s hsq inferInstance

/-- If a presheaf `Y` has an étale surjective map `a` from a scheme `U` and a surjective map
`c` from a quasi-compact scheme, then `a` restricted to a finite disjoint union of affine
opens of `U` is still étale and surjective. -/
theorem exists_affine_atlas_of_compactSpace {Y : Presheaf S} {U V : Over S}
    [CompactSpace V.left]
    (a : (schemeYoneda S).obj U ⟶ Y) (ha : IsEtale a) (has : IsSurjective a)
    (c : (schemeYoneda S).obj V ⟶ Y) (hc : IsSurjective c) :
    ∃ (U₀ : Over S) (j : U₀ ⟶ U), IsAffine U₀.left ∧ Etale j.left ∧
      IsEtale ((schemeYoneda S).map j ≫ a) ∧ IsSurjective ((schemeYoneda S).map j ≫ a) := by
  let hr := ha.representable
  have hP := hr.isPullback c
  obtain ⟨π, hπ⟩ := (schemeYoneda S).map_surjective (hr.fst c)
  rw [← hπ] at hP
  let ρ := hr.snd c
  have : Etale ρ.left := ha.projection c _ _ hP
  have : Surjective ρ.left := has.projection c _ _ hP
  let 𝒰 := U.left.affineCover
  let G : 𝒰.I₀ → Set V.left := fun x => ρ.left '' (π.left ⁻¹' Set.range (𝒰.f x))
  have hG : ∀ x, IsOpen (G x) := fun x =>
    ρ.left.isOpenMap _ ((𝒰.f x).isOpenEmbedding.isOpen_range.preimage π.left.continuous)
  have hcov : Set.univ ⊆ ⋃ x, G x := by
    intro v _
    obtain ⟨p, rfl⟩ := Surjective.surj (f := ρ.left) v
    exact Set.mem_iUnion.2 ⟨𝒰.idx (π.left p), p, 𝒰.covers (π.left p), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hG hcov
  let g : t → Scheme.{u} := fun i => 𝒰.X i
  let J : ∐ g ⟶ U.left := Sigma.desc fun i => 𝒰.f i
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  let U₀ : Over S := Over.mk (J ≫ U.hom)
  let j : U₀ ⟶ U := Over.homMk J
  have he : IsEtale ((schemeYoneda S).map j ≫ a) := (isEtale_map j hJ).comp ha
  refine ⟨U₀, j, inferInstanceAs (IsAffine (∐ g)), hJ, he, ?_⟩
  have hW := IsPullback.of_hasPullback j π
  have hsq := (hW.map (schemeYoneda S)).paste_vert hP
  rw [← Functor.map_comp] at hsq
  refine isSurjective_of_isPullback he.representable hc hsq ⟨fun v => ?_⟩
  obtain ⟨i, hi, hv⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
  obtain ⟨p, ⟨y, hy⟩, rfl⟩ := hv
  obtain ⟨z, -, hz⟩ := exists_preimage_of_isPullback hW (Sigma.ι g ⟨i, hi⟩ y) p (by
    change (Sigma.ι g ⟨i, hi⟩ ≫ J) y = π.left p
    rw [Sigma.ι_comp_desc, hy])
  refine ⟨z, ?_⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply, hz]

/-- An algebraic space locally of finite type over a field with a surjective map from a
quasi-compact scheme is of finite presentation over the field. -/
theorem finitePresentationOverRing {k : Type u} [Field k] {V : Over (Spec (CommRingCat.of k))}
    [QuasiCompact V.hom] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    (c : (schemeYoneda _).obj V ⟶ X.presheaf) (hc : IsSurjective c)
    (hX : LocallyOfFiniteTypeOverBase X) : FinitePresentationOverRing k X := by
  obtain ⟨U, a, ha, has, hU⟩ := hX.exists_atlas
  have : LocallyOfFiniteType U.hom := hU
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  obtain ⟨U₀, j, hU₀, hj, he, hs⟩ := exists_affine_atlas_of_compactSpace a ha has c hc
  refine HasAtlasProperty.of_atlas _ he hs ⟨?_, ?_⟩
  · have : LocallyOfFiniteType U₀.hom := by
      rw [← Over.w j]
      infer_instance
    exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 this
  · infer_instance

end ActionQuotientFiniteness

/-- Action quotients over a field with smooth surjective quotient map are quasi-separated
and of finite presentation. -/
theorem actionQuotientFiniteness : ActionQuotientFinitenessStatement.{u} := by
  intro k _ G Z b _ _ _ X π hπ hπS hπs hX
  exact ⟨ActionQuotientFiniteness.isQuasiSeparated b hπ hπS hπs,
    ActionQuotientFiniteness.finitePresentationOverRing π.hom hπs hX⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
