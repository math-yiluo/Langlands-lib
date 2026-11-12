import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitInduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationRelationQuotient
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # The reduced closed subspace of a finite cover on a closed subscheme -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspace

section Schemes

variable {X : Scheme.{u}}

/-- On a reduced scheme, the vanishing ideal of a closed set containing the range of `g` lies in
the kernel of `g`. No quasi-compactness of `g` is needed. -/
theorem vanishingIdeal_le_ker {T : Scheme.{u}} [_root_.AlgebraicGeometry.IsReduced T]
    (g : T ⟶ X) (Z : Closeds X) (h : Set.range g ⊆ Z) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U s hs
  rw [RingHom.mem_ker]
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at hs
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]
  ext t
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro ht
  have htU : g t ∈ (U : X.Opens) := X.basicOpen_le s ht
  have hfrom := U.2.fromSpec_primeIdealOf ⟨g t, htU⟩
  have hZ : U.2.primeIdealOf ⟨g t, htU⟩ ∈ U.2.fromSpec ⁻¹' (Z : Set X) := by
    show U.2.fromSpec (U.2.primeIdealOf ⟨g t, htU⟩) ∈ (Z : Set X)
    rw [hfrom]
    exact h ⟨t, rfl⟩
  have hsp := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hs _ hZ
  have hb : U.2.primeIdealOf ⟨g t, htU⟩ ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    change U.2.fromSpec (U.2.primeIdealOf ⟨g t, htU⟩) ∈ X.basicOpen s
    rw [hfrom]
    exact ht
  rw [U.2.fromSpec_preimage_basicOpen] at hb
  exact hb hsp

/-- A morphism from a reduced scheme with range in a closed set factors through the reduced
induced closed subscheme on that set. -/
theorem exists_lift_vanishingIdeal {T : Scheme.{u}} [_root_.AlgebraicGeometry.IsReduced T]
    (g : T ⟶ X) (Z : Closeds X) (h : Set.range g ⊆ Z) :
    ∃ g' : T ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      g' ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = g :=
  ⟨g.toImage ≫ Scheme.IdealSheafData.inclusion (vanishingIdeal_le_ker g Z h), by
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]⟩

/-- A morphism from a reduced scheme whose range lies in the range of a closed immersion factors
through the closed immersion. -/
theorem exists_lift_isClosedImmersion {A T : Scheme.{u}} [_root_.AlgebraicGeometry.IsReduced T]
    (j : A ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion j] (g : T ⟶ X)
    (h : Set.range g ⊆ Set.range j) : ∃ g' : T ⟶ A, g' ≫ j = g := by
  let Z : Closeds X := ⟨Set.range j, j.isClosedEmbedding.isClosed_range⟩
  have hj : j.ker ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
    refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
    intro x hx
    change x ∈ (j.ker.support : Set X)
    rw [Scheme.Hom.support_ker]
    exact subset_closure hx
  exact ⟨IsClosedImmersion.lift j g (hj.trans (vanishingIdeal_le_ker g Z h)),
    IsClosedImmersion.lift_fac _ _ _⟩

end Schemes

section Category

variable {C : Type*} [Category C]

/-- A monomorphism on the top edge of a pullback square can be moved to the right edge. -/
theorem isPullback_of_comp_mono {P X X' Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {m : X ⟶ X'}
    [Mono m] {f : X' ⟶ Z} {g : Y ⟶ Z} (h : IsPullback (fst ≫ m) snd f g) :
    IsPullback fst snd (m ≫ f) g := by
  have w : fst ≫ m ≫ f = snd ≫ g := by simpa only [Category.assoc] using h.w
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun c => h.lift (c.fst ≫ m) c.snd (by simpa only [Category.assoc] using c.condition))
    (fun c => ?_) (fun c => h.lift_snd _ _ _) (fun c l hl₁ hl₂ => ?_))
  · rw [← cancel_mono m, Category.assoc, h.lift_fst]
  · apply h.hom_ext
    · rw [h.lift_fst, ← Category.assoc, hl₁]
    · rw [h.lift_snd, hl₂]

/-- A common monomorphism can be cancelled from the right and bottom edges of a pullback
square. -/
theorem isPullback_of_comp_mono_right {P X Y Z Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} {i : Z ⟶ Z'} [Mono i] (h : IsPullback fst snd (f ≫ i) (g ≫ i)) :
    IsPullback fst snd f g := by
  have w : fst ≫ f = snd ≫ g := by
    rw [← cancel_mono i]
    simpa only [Category.assoc] using h.w
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun c => h.lift c.fst c.snd (by rw [← Category.assoc, c.condition, Category.assoc]))
    (fun c => h.lift_fst _ _ _) (fun c => h.lift_snd _ _ _) (fun c l hl₁ hl₂ => ?_))
  apply h.hom_ext
  · rw [h.lift_fst, hl₁]
  · rw [h.lift_snd, hl₂]

end Category

section Presheaves

variable {S : Scheme.{u}}

theorem over_comp_apply {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (x : A.left) :
    (f ≫ g).left x = g.left (f.left x) := by
  rw [Over.comp_left, Scheme.Hom.comp_apply]

/-- A morphism from a reduced scheme over `S` with range in a closed set factors through the
reduced induced closed subscheme over `S`. -/
theorem exists_lift_reducedOver {V T : Over S} [_root_.AlgebraicGeometry.IsReduced T.left]
    (g : T ⟶ V) (Z : Closeds V.left) (h : Set.range g.left ⊆ Z) :
    ∃ g' : T ⟶ reducedOver V Z, g' ≫ reducedOverι V Z = g := by
  obtain ⟨g', hg'⟩ := exists_lift_vanishingIdeal g.left Z h
  refine ⟨Over.homMk g' ?_, ?_⟩
  · change g' ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ V.hom = T.hom
    rw [← Category.assoc, hg', Over.w g]
  · apply Over.OverMorphism.ext
    exact hg'

/-- A morphism from a reduced scheme over `S` whose range lies in the range of a closed immersion
over `S` factors through it. -/
theorem exists_lift_isClosedImmersion_over {A T X : Over S}
    [_root_.AlgebraicGeometry.IsReduced T.left] (j : A ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion j.left] (g : T ⟶ X)
    (h : Set.range g.left ⊆ Set.range j.left) : ∃ g' : T ⟶ A, g' ≫ j = g := by
  obtain ⟨g', hg'⟩ := exists_lift_isClosedImmersion j.left g.left h
  refine ⟨Over.homMk g' ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, hg', Over.w g]
  · apply Over.OverMorphism.ext
    exact hg'

/-- Lifting through a pullback square of represented presheaves. -/
theorem exists_lift_of_isPullback {W U V : Over S} {Y : Presheaf S} {φ : W ⟶ U} {p : W ⟶ V}
    {F : (schemeYoneda S).obj U ⟶ Y} {G : (schemeYoneda S).obj V ⟶ Y}
    (h : IsPullback ((schemeYoneda S).map φ) ((schemeYoneda S).map p) F G) {T : Over S}
    (x : T ⟶ U) (y : T ⟶ V)
    (w : (schemeYoneda S).map x ≫ F = (schemeYoneda S).map y ≫ G) :
    ∃ r : T ⟶ W, r ≫ φ = x ∧ r ≫ p = y := by
  obtain ⟨r, hr⟩ := (schemeYoneda S).map_surjective (h.lift _ _ w)
  refine ⟨r, (schemeYoneda S).map_injective ?_, (schemeYoneda S).map_injective ?_⟩
  · rw [Functor.map_comp, hr, h.lift_fst]
  · rw [Functor.map_comp, hr, h.lift_snd]

/-- Restricting a represented kernel pair to a subscheme `ι : V_T ⟶ V`: if `R_T` is the
pullback of `s` along `ι` and `t` maps `R_T` into `V_T`, then `R_T` represents the kernel pair
of `h_ι ≫ a`. -/
theorem isPullback_restrict {V VT R RT : Over S} {X : Presheaf S}
    {aY : (schemeYoneda S).obj V ⟶ X} {t s : R ⟶ V}
    (hR : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) aY aY)
    (ι : VT ⟶ V) [Mono ((schemeYoneda S).map ι)]
    {ιR : RT ⟶ R} {sT tT : RT ⟶ VT} (hRT : IsPullback ιR sT s ι) (htT : tT ≫ ι = ιR ≫ t) :
    IsPullback ((schemeYoneda S).map tT) ((schemeYoneda S).map sT)
      ((schemeYoneda S).map ι ≫ aY) ((schemeYoneda S).map ι ≫ aY) := by
  have h := (hRT.map (schemeYoneda S)).paste_horiz hR
  rw [← Functor.map_comp, ← htT, Functor.map_comp] at h
  exact isPullback_of_comp_mono h

/-- In a represented kernel pair, the first projection is étale if the second one is. -/
theorem etale_of_isPullback_symm {V R : Over S} {X : Presheaf S}
    {b : (schemeYoneda S).obj V ⟶ X} {t s : R ⟶ V}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b)
    (hs : Etale s.left) : Etale t.left := by
  let e := (schemeYoneda S).preimageIso (h.flip.isoIsPullback _ _ h)
  have he : e.hom ≫ s = t := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    exact h.flip.isoIsPullback_hom_snd _ _ h
  rw [← he, Over.comp_left]
  have : Etale s.left := hs
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  infer_instance

end Presheaves

section Main

variable {S : Scheme.{u}}

/-- For a quasi-separated algebraic space, the morphism from a represented kernel pair of a map
from a scheme to the product of two copies of the scheme is quasi-compact. -/
theorem quasiCompact_prodLift_of_isQuasiSeparated {X : AlgebraicSpace S}
    (hX : IsQuasiSeparated X) {U R : Over S} {a : (schemeYoneda S).obj U ⟶ X.presheaf}
    {t s : R ⟶ U} (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a) :
    QuasiCompact (prod.lift t s).left := by
  let Y := schemeYoneda S
  let j : R ⟶ U ⨯ U := prod.lift t s
  let e : Y.obj (U ⨯ U) ≅ Y.obj U ⨯ Y.obj U := PreservesLimitPair.iso Y U U
  let A : Y.obj (U ⨯ U) ⟶ X.presheaf ⨯ X.presheaf := e.hom ≫ prod.map a a
  have hjmap : Y.map j ≫ e.hom = prod.lift (Y.map t) (Y.map s) := by
    apply prod.hom_ext <;> simp [e, PreservesLimitPair.iso_hom, j, ← Functor.map_comp]
  have hsq : IsPullback (Y.map t ≫ a) (Y.map j) (diag X.presheaf) A := by
    apply (FinitePresentationRelationQuotient.isPullback_kernel_diagonal h).of_iso'
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simpa using hjmap.symm
    · simp
    · simp [A]
  exact hX.2 A _ j hsq

/-- In a pullback square of represented presheaves over `F` and an atlas `a_Y` with represented
kernel pair `(t, s)`, the relation maps the image of `p_T` into itself. -/
theorem mem_range_of_isPullback {UT WT V R : Over S} {X : Presheaf S}
    {F : (schemeYoneda S).obj UT ⟶ X} {aY : (schemeYoneda S).obj V ⟶ X}
    {φT : WT ⟶ UT} {pT : WT ⟶ V}
    (hW : IsPullback ((schemeYoneda S).map φT) ((schemeYoneda S).map pT) F aY) {t s : R ⟶ V}
    (hR : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) aY aY) (r : R.left)
    (hr : s.left r ∈ Set.range pT.left) : t.left r ∈ Set.range pT.left := by
  obtain ⟨w, hw⟩ := hr
  obtain ⟨z, hz₁, hz₂⟩ :=
    exists_preimage_of_isPullback (IsPullback.of_hasPullback pT s) w r hw
  obtain ⟨ψ, -, hψ₂⟩ := exists_lift_of_isPullback hW (pullback.fst pT s ≫ φT)
    (pullback.snd pT s ≫ t) (by
      simp only [Functor.map_comp, Category.assoc, hW.w]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, pullback.condition,
        Functor.map_comp_assoc, Functor.map_comp_assoc, hR.w])
  refine ⟨ψ.left z, ?_⟩
  rw [← over_comp_apply, hψ₂, over_comp_apply, hz₂]

/-- Points of `U_T` have the same image under `f_T` exactly when their images under the closed
immersion `j` have the same image under `F`, if `f_T` followed by a monomorphism `i` is
`h_j ≫ F`. -/
theorem sameImage_iff_of_mono {UT U : Over S} {X X' : Presheaf S} (j : UT ⟶ U)
    [_root_.AlgebraicGeometry.IsClosedImmersion j.left]
    (fT : (schemeYoneda S).obj UT ⟶ X) (i : X ⟶ X') [Mono i]
    (F : (schemeYoneda S).obj U ⟶ X') (h : fT ≫ i = (schemeYoneda S).map j ≫ F)
    (x x' : UT.left) : SameImage fT x x' ↔ SameImage F (j.left x) (j.left x') := by
  constructor
  · rintro ⟨T, g, g', τ, hg, rfl, rfl⟩
    refine ⟨T, g ≫ j, g' ≫ j, τ, ?_, over_comp_apply _ _ _, over_comp_apply _ _ _⟩
    simp only [Functor.map_comp, Category.assoc, ← h]
    rw [reassoc_of% hg]
  · rintro ⟨T, g, g', τ, hg, hgx, hgx'⟩
    let k := T.left.fromSpecResidueField τ
    let T' : Over S := Over.mk (k ≫ T.hom)
    let κ : T' ⟶ T := Over.homMk k
    have hκ : ∀ y, κ.left y = τ := fun y => Scheme.fromSpecResidueField_apply _ _
    have hrange : ∀ (g₀ : T ⟶ U) (x₀ : UT.left), g₀.left τ = j.left x₀ →
        Set.range (κ ≫ g₀).left ⊆ Set.range j.left := by
      rintro g₀ x₀ hx₀ _ ⟨y, rfl⟩
      exact ⟨x₀, by rw [over_comp_apply, hκ, hx₀]⟩
    have : _root_.AlgebraicGeometry.IsReduced T'.left :=
      inferInstanceAs (_root_.AlgebraicGeometry.IsReduced (Spec (T.left.residueField τ)))
    have : Inhabited T'.left :=
      ⟨(inferInstance : Unique (Spec (T.left.residueField τ))).default⟩
    obtain ⟨l, hl⟩ := exists_lift_isClosedImmersion_over j (κ ≫ g) (hrange g x hgx)
    obtain ⟨l', hl'⟩ := exists_lift_isClosedImmersion_over j (κ ≫ g') (hrange g' x' hgx')
    have hpt : ∀ (l₀ : T' ⟶ UT) (g₀ : T ⟶ U) (x₀ : UT.left), l₀ ≫ j = κ ≫ g₀ →
        g₀.left τ = j.left x₀ → l₀.left default = x₀ := by
      intro l₀ g₀ x₀ hl₀ hx₀
      apply j.left.isClosedEmbedding.injective
      rw [← over_comp_apply, hl₀, over_comp_apply, hκ, hx₀]
    refine ⟨T', l, l', default, ?_, hpt l g x hl hgx, hpt l' g' x' hl' hgx'⟩
    rw [← cancel_mono i, Category.assoc, Category.assoc, h, ← Functor.map_comp_assoc, hl,
      ← Functor.map_comp_assoc, hl', Functor.map_comp_assoc, Functor.map_comp_assoc, hg]

/-- The represented transformation of a finite morphism of schemes over `S` is finite. -/
theorem isFinite_map {U V : Over S} (φ : U ⟶ V) (hφ : _root_.AlgebraicGeometry.IsFinite φ.left) :
    IsFinite ((schemeYoneda S).map φ) := by
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)).IsStableUnderBaseChange :=
    isStableUnderBaseChange_inverseImage_forget
  exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u}) (Over.forget S)) hφ

set_option backward.isDefEq.respectTransparency.types false in
/-- Finite transformations of presheaves are stable under composition. -/
theorem IsFinite.comp {F G H : Presheaf S} {f : F ⟶ G} {g : G ⟶ H} (hf : IsFinite f)
    (hg : IsFinite g) : IsFinite (f ≫ g) :=
  MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u}) (Over.forget S)).relative (schemeYoneda S)) f g hf hg

set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness of morphisms of schemes descends along fppf covers. -/
theorem descendsAlong_isFinite : MorphismProperty.DescendsAlong
    (@_root_.AlgebraicGeometry.IsFinite.{u})
    (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
  inferInstance

end Main

/-- Let `f : U ⟶ Y` be finite and surjective onto a quasi-compact quasi-separated algebraic space
and let `j : U_T ⟶ U` be a closed immersion from a reduced scheme. Then `U_T` is a finite
surjective cover of a quasi-compact quasi-separated algebraic space `Y_T`, which is a
subsheaf of `Y`; in particular points of `U_T` have the same image in `Y_T` exactly when their
images in `U` have the same image in `Y`. -/
theorem reducedClosedSubspace : ReducedClosedSubspaceStatement.{u} := by
  intro S U Y f hYc hYs hf _ UT j hj hred _
  obtain ⟨V, aY, haYe, haYs, hVc⟩ := hYc
  obtain ⟨R, t, s, hR, -, hsE⟩ := exists_kernelPair haYe
  -- The composite `F : h_{U_T} ⟶ Y` and its base change along the atlas `a_Y`.
  obtain ⟨F, hF⟩ : ∃ F : (schemeYoneda S).obj UT ⟶ Y.presheaf,
      F = (schemeYoneda S).map j ≫ hom f := ⟨_, rfl⟩
  have hjF : IsFinite F := hF ▸ IsFinite.comp (isFinite_map j inferInstance) hf
  obtain ⟨WT, φT, pT, hWT⟩ : ∃ (WT : Over S) (φT : WT ⟶ UT) (pT : WT ⟶ V),
      IsPullback ((schemeYoneda S).map φT) ((schemeYoneda S).map pT) F aY := by
    let hr := hjF.representable
    obtain ⟨φT, hφT⟩ := (schemeYoneda S).map_surjective (hr.fst aY)
    refine ⟨_, φT, hr.snd aY, ?_⟩
    rw [hφT]
    exact hr.isPullback aY
  have : _root_.AlgebraicGeometry.IsFinite pT.left := hjF.projection aY _ pT hWT
  have : Etale φT.left := haYe.projection F _ φT hWT.flip
  have : Surjective φT.left := haYs.projection F _ φT hWT.flip
  have : _root_.AlgebraicGeometry.IsReduced WT.left :=
    SmoothReducedBase.isReduced_of_smooth_of_isReduced φT.left
  -- The reduced closed subscheme `V_T` of `V` on the image of `p_T`.
  obtain ⟨VT, ι, hιc, hVTr, hιr⟩ : ∃ (VT : Over S) (ι : VT ⟶ V),
      _root_.AlgebraicGeometry.IsClosedImmersion ι.left ∧
        _root_.AlgebraicGeometry.IsReduced VT.left ∧ Set.range ι.left = Set.range pT.left :=
    ⟨reducedOver V ⟨_, pT.left.isClosedMap.isClosed_range⟩, reducedOverι _ _, inferInstance,
      inferInstance, range_reducedOverι _ _⟩
  obtain ⟨qT, hqT⟩ := exists_lift_isClosedImmersion_over ι pT hιr.symm.subset
  have hqTF : _root_.AlgebraicGeometry.IsFinite qT.left := by
    refine MorphismProperty.of_postcomp (W := @_root_.AlgebraicGeometry.IsFinite)
      (W' := @_root_.AlgebraicGeometry.IsSeparated) qT.left ι.left inferInstance ?_
    rw [← Over.comp_left, hqT]
    infer_instance
  have hqTS : Surjective qT.left := by
    refine ⟨fun w => ?_⟩
    obtain ⟨x, hx⟩ : ι.left w ∈ Set.range pT.left := hιr ▸ ⟨w, rfl⟩
    refine ⟨x, ι.left.isClosedEmbedding.injective ?_⟩
    rw [← over_comp_apply, hqT, hx]
  -- The restriction `R_T` of the relation to `V_T`.
  obtain ⟨RT, ιR, sT, hRT⟩ : ∃ (RT : Over S) (ιR : RT ⟶ R) (sT : RT ⟶ VT),
      IsPullback ιR sT s ι := ⟨_, _, _, IsPullback.of_hasPullback s ι⟩
  have hRTs : IsPullback ιR.left sT.left s.left ι.left := hRT.map (Over.forget S)
  have hsTE : Etale sT.left := MorphismProperty.of_isPullback (P := @Etale) hRTs hsE
  have : _root_.AlgebraicGeometry.IsClosedImmersion ιR.left :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsClosedImmersion) hRTs.flip hιc
  have : _root_.AlgebraicGeometry.IsReduced RT.left :=
    SmoothReducedBase.isReduced_of_smooth_of_isReduced sT.left
  obtain ⟨tT, htT⟩ := exists_lift_isClosedImmersion_over ι (ιR ≫ t) (by
    rintro _ ⟨r, rfl⟩
    rw [hιr, over_comp_apply]
    apply mem_range_of_isPullback hWT hR
    rw [← over_comp_apply, hRT.w, over_comp_apply, ← hιr]
    exact ⟨_, rfl⟩)
  have : Mono ι := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono ι.left))
  have : Mono ((schemeYoneda S).map ι) := inferInstance
  have hkp := isPullback_restrict hR ι hRT htT
  have htTE := etale_of_isPullback_symm hkp hsTE
  -- The quotient `Q` of `V_T` by `R_T`.
  obtain ⟨Q, a, ha, has, hQ⟩ : ∃ (Q : AlgebraicSpace S)
      (a : (schemeYoneda S).obj VT ⟶ Q.presheaf), IsEtale a ∧ IsSurjective a ∧
        IsPullback ((schemeYoneda S).map tT) ((schemeYoneda S).map sT) a a := by
    let E := EtaleEquivalenceRelation.ofKernelPair tT sT ((schemeYoneda S).map ι ≫ aY) hkp
      htTE hsTE
    have hb : E.t ≫ VT.hom = E.s ≫ VT.hom := by
      change tT.left ≫ VT.hom = sT.left ≫ VT.hom
      rw [Over.w tT, Over.w sT]
    obtain ⟨Q, a, ha, has, hQ⟩ := etaleEquivalenceRelationAlgebraicSpaceQuotient S E VT.hom hb
    let eR : Over.mk (tT.left ≫ VT.hom) ≅ RT :=
      Over.isoMk (Iso.refl RT.left) (by simp [Over.w tT])
    have e₁ : (Over.homMk E.t : Over.mk (E.t ≫ VT.hom) ⟶ Over.mk VT.hom) = eR.hom ≫ tT :=
      Over.OverMorphism.ext (by simp [eR]; rfl)
    have e₂ : (Over.homMk E.s hb.symm : Over.mk (E.t ≫ VT.hom) ⟶ Over.mk VT.hom) =
        eR.hom ≫ sT :=
      Over.OverMorphism.ext (by simp [eR]; rfl)
    refine ⟨Q, a, ha, has, hQ.of_iso ((schemeYoneda S).mapIso eR) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_⟩
    · exact (Category.comp_id _).trans
        ((congrArg (schemeYoneda S).map e₁).trans (Functor.map_comp _ _ _))
    · exact (Category.comp_id _).trans
        ((congrArg (schemeYoneda S).map e₂).trans (Functor.map_comp _ _ _))
    · exact (Category.id_comp a).symm
    · exact (Category.id_comp a).symm
  have haL := isLocallySurjective_of_isEtale a ha has
  -- The monomorphism `i : Q ⟶ Y`.
  obtain ⟨i, hai⟩ : ∃ i : Q.presheaf ⟶ Y.presheaf, a ≫ i = (schemeYoneda S).map ι ≫ aY :=
    KernelPairDescent.exists_desc (F := Q.toSheaf) (G := Y.toSheaf) a haL hQ
      ((schemeYoneda S).map ι ≫ aY) hkp.w
  have : Mono i := by
    have : ∀ T, Mono (i.app T) := fun T => (mono_iff_injective _).mpr
      (KernelPairDescent.injective_of_isPullback a haL hQ i (hai ▸ hkp) T)
    exact NatTrans.mono_of_mono_app i
  -- The map `f_T : U_T ⟶ Q`, descended along `φ_T`.
  have hφL := isLocallySurjective_map φT
  obtain ⟨fT, hfT⟩ : ∃ fT : (schemeYoneda S).obj UT ⟶ Q.presheaf,
      (schemeYoneda S).map φT ≫ fT = (schemeYoneda S).map qT ≫ a :=
    KernelPairDescent.exists_desc (F := (schemeSheaf S).obj UT)
      (G := Q.toSheaf) ((schemeYoneda S).map φT) hφL
      ((IsPullback.of_hasPullback φT φT).map (schemeYoneda S)) ((schemeYoneda S).map qT ≫ a) (by
        rw [← cancel_mono i]
        simp only [Category.assoc, hai]
        simp only [← Functor.map_comp_assoc, hqT]
        rw [Functor.map_comp_assoc, Functor.map_comp_assoc, ← hWT.w, ← Functor.map_comp_assoc,
          ← Functor.map_comp_assoc, pullback.condition])
  have hfTi : fT ≫ i = F := by
    have h : (schemeYoneda S).map φT ≫ fT ≫ i = (schemeYoneda S).map φT ≫ F := by
      rw [← Category.assoc, hfT, Category.assoc, hai, ← Functor.map_comp_assoc, hqT, hWT.w]
    exact KernelPairDescent.hom_ext_of_isLocallySurjective (F := (schemeSheaf S).obj UT)
      (G := Y.toSheaf) ((schemeYoneda S).map φT) hφL h
  have h₀ : IsPullback ((schemeYoneda S).map φT) ((schemeYoneda S).map qT) fT a := by
    have h₁ := hWT.flip
    rw [← hqT, Functor.map_comp] at h₁
    have h₂ := isPullback_of_comp_mono h₁
    rw [← hai, ← hfTi] at h₂
    exact (isPullback_of_comp_mono_right h₂).flip
  have : CompactSpace VT.left := ι.left.isClosedEmbedding.compactSpace
  -- Quasi-separatedness of `Q` from that of `Y`.
  have hjqc : QuasiCompact (prod.lift tT sT).left := by
    have hcomm : prod.lift tT sT ≫ prod.map ι ι = ιR ≫ prod.lift t s := by
      apply prod.hom_ext
      · simp [htT]
      · simp [hRT.w]
    have : QuasiCompact (prod.lift t s).left := quasiCompact_prodLift_of_isQuasiSeparated hYs hR
    have : QuasiCompact ((prod.lift tT sT).left ≫ (prod.map ι ι).left) := by
      rw [← Over.comp_left, hcomm, Over.comp_left]
      infer_instance
    exact QuasiCompact.of_comp _ (prod.map ι ι).left
  have := descendsAlong_isFinite.{u}
  refine ⟨Q, AlgebraicSpace.homMk fT, IsQuasiCompact.of_atlas a ha has inferInstance,
    FinitePresentationRelationQuotient.isQuasiSeparated_of_atlas a ha has tT sT hQ hjqc,
    relative_of_isEtale_isSurjective (@_root_.AlgebraicGeometry.IsFinite)
      (Q.representable_from_scheme fT) ha has ((schemeYoneda S).map φT) qT h₀ hqTF,
    isSurjective_of_isPullback (Q.representable_from_scheme fT) has h₀ hqTS,
    sameImage_iff_of_mono j fT i (hom f) (hfTi.trans hF)⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspace
