import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocusInvariant
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedDenseAffineOpenStatement
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements
import Langlands.AlgebraicGeometry.Morphisms.FiniteFlatSourceDescent

/-! # Dense affine open subspaces, assuming 03BM and 03JE

The dense affine open statement for separated algebraic spaces over a field follows from the
affine quotient statement for finite locally free equivalence relations (Stacks 03BM) and the
finite-set invariant affine open statement (Stacks 03JE).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open AtlasRelation FiniteLocus OpenSubfunctorLifting AffineOpenSubfunctors

set_option backward.isDefEq.respectTransparency.types false

/-- An affine scheme locally of finite type over a field is a Noetherian space. -/
theorem noetherianSpace_of_isAffine_of_locallyOfFiniteType {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    NoetherianSpace X := by
  have hft : (f.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv k
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appTop).hom]
  have : IsNoetherianRing Γ(X, ⊤) := Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) Γ(X, ⊤)
  exact noetherianSpace_of_isAffine

variable {k : Type u} [Field k]

local notation "𝕊" => Spec (CommRingCat.of k)

/-- The dense affine open statement with the additional conclusion that the affine open
subspace is locally of finite type over the field. -/
def SeparatedDenseAffineOpenLFTProp : Prop :=
  ∀ (k : Type u) [Field k] (X : FppfSheaf (Spec (CommRingCat.of k))),
    IsAlgebraicSpace (Spec (CommRingCat.of k)) X →
    IsClosedImmersion (Limits.diag X.obj) →
    ∀ (U : Over (Spec (CommRingCat.of k)))
      (a : (schemeYoneda (Spec (CommRingCat.of k))).obj U ⟶ X.obj),
      IsEtale a → IsSurjective a → IsAffine U.left → LocallyOfFiniteType U.hom →
      ∃ (V W : Over (Spec (CommRingCat.of k)))
        (i : (schemeYoneda (Spec (CommRingCat.of k))).obj V ⟶ X.obj) (p : W ⟶ U)
        (b : (schemeYoneda (Spec (CommRingCat.of k))).obj W ⟶
          (schemeYoneda (Spec (CommRingCat.of k))).obj V),
        IsAffine V.left ∧ LocallyOfFiniteType V.hom ∧ IsOpenImmersion i ∧
          IsPullback b ((schemeYoneda (Spec (CommRingCat.of k))).map p) i a ∧
          Dense (Set.range p.left)

/-- The dense affine open statement with a locally finite type affine open, assuming the
statements of Stacks 03BM and 03JE and the invariance of the finite locus. -/
theorem separatedDenseAffineOpenLFT_of
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u})
    (h03JE : FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u})
    (hfl : FiniteLocusInvariantProp.{u}) :
    SeparatedDenseAffineOpenLFTProp.{u} := by
  intro k _ X hX hd U a ha _ hUa hU
  let Y := schemeYoneda (Spec (CommRingCat.of k))
  -- (A) the kernel pair
  have hr : IsRepresentableMorphism a := Functor.relativelyRepresentable.of_diag hX.1 a
  obtain ⟨R, t, s, hpb, hrel⟩ := AtlasRelation.exists_kernelPair a hr
  have hRa : IsAffine R.left := isAffine_of_isPullback_of_closedDiagonal hd a a t s hpb
  have : Etale s.left := ha.projection a _ s hpb
  have : Etale t.left := ha.projection a _ t hpb.flip
  have : LocallyQuasiFinite s.left := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  have : LocallyQuasiFinite t.left := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  have hRt : t.left ≫ U.hom = R.hom := Over.w t
  have hRs : s.left ≫ U.hom = R.hom := Over.w s
  -- (B) the finite locus of `s`, which is invariant and contains all generic points
  let W := finiteLocus s.left
  have hWfin : _root_.AlgebraicGeometry.IsFinite (s.left ∣_ W) := isFinite_restrict_finiteLocus s.left
  have hinv : s.left ⁻¹ᵁ W = t.left ⁻¹ᵁ W := hfl _ _ _ _ hrel inferInstance inferInstance inferInstance
  have hEW : genericPoints U.left ⊆ W := genericPoints_subset_finiteLocus s.left
  have : NoetherianSpace U.left := noetherianSpace_of_isAffine_of_locallyOfFiniteType U.hom
  have hEfin : (genericPoints U.left).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have hsat : ∀ r : R.left, s.left r ∈ genericPoints U.left → t.left r ∈ genericPoints U.left := by
    intro r hr
    have hR : r ∈ genericPoints R.left :=
      GenericPointAvoidance.mem_genericPoints_of_isDiscrete_fibre s.left.continuous
        s.left.isDiscrete_preimage_singleton hr
    exact GenericPointAvoidance.mem_genericPoints_of_generalizingMap
      (Flat.generalizingMap t.left) hR
  obtain ⟨f, hEf, hfW⟩ := GenericPointAvoidance.exists_basicOpen_of_finite hEfin hEW
  -- (C) the relation on `W` and an invariant affine open `V'` of `W` from 03JE
  have hrelW := hrel.restrict W hinv
  obtain ⟨φ, hφ⟩ := hrel.exists_iso_restrictT W hinv
  have hsWF : _root_.AlgebraicGeometry.IsFinite (s.left ∣_ W) := hWfin
  have htWF : _root_.AlgebraicGeometry.IsFinite (restrictT t.left s.left W hinv) := by
    rw [← hφ]; infer_instance
  have htWe : Etale (restrictT t.left s.left W hinv) := by
    rw [← hφ]; infer_instance
  have hW'a : IsAffineOpen (W.ι ⁻¹ᵁ U.left.basicOpen f) :=
    ((isAffineOpen_top U.left).basicOpen f).preimage_of_isOpenImmersion W.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact hfW)
  have hE'fin : (W.ι ⁻¹' genericPoints U.left).Finite :=
    hEfin.preimage W.ι.isOpenEmbedding.injective.injOn
  have hsι : ∀ r : (s.left ⁻¹ᵁ W).toScheme,
      W.ι ((s.left ∣_ W) r) = s.left ((s.left ⁻¹ᵁ W).ι r) := by
    intro r
    rw [← Scheme.Hom.comp_apply, restrictS_ι, Scheme.Hom.comp_apply]
  have htι : ∀ r : (s.left ⁻¹ᵁ W).toScheme,
      W.ι ((restrictT t.left s.left W hinv) r) = t.left ((s.left ⁻¹ᵁ W).ι r) := by
    intro r
    rw [← Scheme.Hom.comp_apply, restrictT_ι, Scheme.Hom.comp_apply]
  have hE'sat : ∀ r : (s.left ⁻¹ᵁ W).toScheme, (s.left ∣_ W) r ∈ W.ι ⁻¹' genericPoints U.left →
      (restrictT t.left s.left W hinv) r ∈ W.ι ⁻¹ᵁ U.left.basicOpen f := by
    intro r hr
    change W.ι _ ∈ U.left.basicOpen f
    rw [htι]
    apply hEf
    apply hsat
    rw [← hsι]
    exact hr
  obtain ⟨V', hV'a, hEV', hV'inv⟩ := h03JE W (s.left ⁻¹ᵁ W) (restrictT t.left s.left W hinv)
    (s.left ∣_ W) hrelW.mono hrelW.refl hrelW.symm hrelW.trans htWF inferInstance inferInstance
    hsWF inferInstance inferInstance _ _ hE'fin hW'a hE'sat
  -- (D) its image `V` in `U`: affine, invariant, inside `W`, containing all generic points
  let V := W.ι ''ᵁ V'
  have hVa : IsAffineOpen V := hV'a.image_of_isOpenImmersion W.ι
  have hVW : V ≤ W := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hEV : genericPoints U.left ⊆ V := by
    intro η hη
    exact ⟨⟨η, hEW hη⟩, hEV' hη, rfl⟩
  have hVinv : s.left ⁻¹ᵁ V = t.left ⁻¹ᵁ V := by
    have key : ∀ r : R.left, s.left r ∈ V → t.left r ∈ V := by
      intro r hr
      have hrW : r ∈ s.left ⁻¹ᵁ W := hVW hr
      let r' : (s.left ⁻¹ᵁ W).toScheme := ⟨r, hrW⟩
      have hr' : (s.left ∣_ W) r' ∈ V' := by
        obtain ⟨x, hx, hxe⟩ := hr
        have : (s.left ∣_ W) r' = x := by
          apply W.ι.isOpenEmbedding.injective
          rw [hsι]
          exact hxe.symm
        rw [this]
        exact hx
      have ht' : (restrictT t.left s.left W hinv) r' ∈ V' := by
        have : r' ∈ (s.left ∣_ W) ⁻¹ᵁ V' := hr'
        rw [hV'inv] at this
        exact this
      exact ⟨_, ht', htι r'⟩
    obtain ⟨σ, hσt, hσs, -⟩ := hrel.exists_swap
    ext r
    constructor
    · exact key r
    · intro hr
      have := key (σ r)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσs, hσt] at this
      exact this hr
  -- (E) the affine quotient of the relation on `V` (03BM)
  have hrelV := hrel.restrict V hVinv
  obtain ⟨φV, hφV⟩ := hrel.exists_iso_restrictT V hVinv
  have hsVF : _root_.AlgebraicGeometry.IsFinite (s.left ∣_ V) :=
    isFinite_restrict_of_le s.left hVW hWfin
  have htVF : _root_.AlgebraicGeometry.IsFinite (restrictT t.left s.left V hVinv) := by
    rw [← hφV]; infer_instance
  have htVe : Etale (restrictT t.left s.left V hVinv) := by
    rw [← hφV]; infer_instance
  have : IsAffine V := hVa
  obtain ⟨M, q, hMa, hpbq, hqF, hqFl, hqL, hqS⟩ := h03BM V (s.left ⁻¹ᵁ V)
    (restrictT t.left s.left V hVinv) (s.left ∣_ V) hrelV.mono hrelV.refl hrelV.symm hrelV.trans
    htVF inferInstance inferInstance hsVF inferInstance inferInstance inferInstance
  -- (F) the open subspace with atlas `V`
  let Vo : Over (Spec (CommRingCat.of k)) := Over.mk (V.ι ≫ U.hom)
  let p : Vo ⟶ U := Over.homMk V.ι
  have : _root_.AlgebraicGeometry.IsOpenImmersion p.left :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.ι)
  let aV := Y.map p ≫ a
  have haV : IsEtale aV := (isEtale_map p inferInstance).comp ha
  let Q := (Subfunctor.range aV).sheafify (fppfTopology (Spec (CommRingCat.of k)))
  have hQo : IsOpenImmersion Q.ι := OpenSubfunctorImages.sheafify_range_open aV haV
  have hQsh := OpenSubfunctorImages.sheafify_range_isSheaf aV haV X.property
  let b' := Subfunctor.toRangeSheafify (fppfTopology (Spec (CommRingCat.of k))) aV
  have hb'ls : CategoryTheory.Presheaf.IsLocallySurjective
      (fppfTopology (Spec (CommRingCat.of k))) b' := inferInstance
  have : EffectiveEpi q := inferInstance
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ V.ι ≫ U.hom = g₂ ≫ V.ι ≫ U.hom := by
    intro Z g₁ g₂ h
    have h₁ := hpbq.lift_fst g₁ g₂ h
    have h₂ := hpbq.lift_snd g₁ g₂ h
    have e₁ : restrictT t.left s.left V hVinv ≫ V.ι ≫ U.hom = (s.left ⁻¹ᵁ V).ι ≫ R.hom := by
      rw [← Category.assoc, restrictT_ι, Category.assoc, hRt]
    have e₂ : s.left ∣_ V ≫ V.ι ≫ U.hom = (s.left ⁻¹ᵁ V).ι ≫ R.hom := by
      rw [← Category.assoc, restrictS_ι, Category.assoc, hRs]
    calc g₁ ≫ V.ι ≫ U.hom
        = (hpbq.lift g₁ g₂ h ≫ restrictT t.left s.left V hVinv) ≫ V.ι ≫ U.hom := by rw [h₁]
      _ = hpbq.lift g₁ g₂ h ≫ (s.left ⁻¹ᵁ V).ι ≫ R.hom := by rw [Category.assoc, e₁]
      _ = (hpbq.lift g₁ g₂ h ≫ s.left ∣_ V) ≫ V.ι ≫ U.hom := by rw [Category.assoc, e₂]
      _ = g₂ ≫ V.ι ≫ U.hom := by rw [h₂]
  let Mo : Over (Spec (CommRingCat.of k)) := Over.mk (EffectiveEpi.desc q (V.ι ≫ U.hom) hdesc)
  let qo : Vo ⟶ Mo := Over.homMk q (EffectiveEpi.fac q (V.ι ≫ U.hom) hdesc)
  have : Flat qo.left := hqFl
  have : LocallyOfFinitePresentation qo.left := hqL
  have : Surjective qo.left := hqS
  -- points of the kernel pair
  have hlift : ∀ {T : Over (Spec (CommRingCat.of k))} (g₁ g₂ : T ⟶ U),
      Y.map g₁ ≫ a = Y.map g₂ ≫ a → ∃ r : T ⟶ R, r ≫ t = g₁ ∧ r ≫ s = g₂ := by
    intro T g₁ g₂ w
    refine ⟨Y.preimage (hpb.lift (Y.map g₁) (Y.map g₂) w), ?_, ?_⟩
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, hpb.lift_fst]
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, hpb.lift_snd]
  have happ : ∀ {T : Over (Spec (CommRingCat.of k))} (g₁ g₂ : T ⟶ U),
      a.app (op T) ⟨g₁⟩ = a.app (op T) ⟨g₂⟩ ↔ Y.map g₁ ≫ a = Y.map g₂ ≫ a := by
    intro T g₁ g₂
    rw [← uliftYonedaEquiv.injective.eq_iff, uliftYonedaEquiv_comp, uliftYonedaEquiv_comp,
      uliftYonedaEquiv_uliftYoneda_map, uliftYonedaEquiv_uliftYoneda_map]
  -- a test point identified with a point of `V` lies in `V`
  have hfactor : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ U) (v : T ⟶ Vo),
      Y.map (v ≫ p) ≫ a = Y.map g ≫ a → ∃ v' : T ⟶ Vo, v' ≫ p = g := by
    intro T g v w
    obtain ⟨r, hr₁, hr₂⟩ := hlift g (v ≫ p) w.symm
    have hsub : Set.range g.left ⊆ Set.range V.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hrx : r.left x ∈ s.left ⁻¹ᵁ V := by
        change s.left (r.left x) ∈ V
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr₂, Over.comp_left, Scheme.Hom.comp_apply]
        exact ((v.left x)).2
      rw [hVinv] at hrx
      have : t.left (r.left x) = g.left x := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr₁]
      rw [← this]
      exact hrx
    let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift V.ι g.left hsub
    have hl : l ≫ V.ι = g.left := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk l (by
      change l ≫ V.ι ≫ U.hom = T.hom
      rw [← Category.assoc, hl, Over.w]), Over.OverMorphism.ext hl⟩
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (w₁ w₂ : T ⟶ Vo),
      b'.app (op T) ⟨w₁⟩ = b'.app (op T) ⟨w₂⟩ ↔ w₁ ≫ qo = w₂ ≫ qo := by
    intro T w₁ w₂
    have hb' : ∀ w : T ⟶ Vo, (b'.app (op T) ⟨w⟩).1 = a.app (op T) ⟨w ≫ p⟩ := fun _ ↦ rfl
    rw [Subtype.ext_iff, hb', hb', happ]
    constructor
    · intro w
      obtain ⟨r, hr₁, hr₂⟩ := hlift _ _ w
      obtain ⟨r'', hr''⟩ := exists_lift_preimage s.left V r.left (fun x ↦ by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr₂, Over.comp_left, Scheme.Hom.comp_apply]
        exact (w₂.left x).2)
      have e₁ : r'' ≫ restrictT t.left s.left V hVinv = w₁.left := by
        rw [← cancel_mono V.ι, Category.assoc, restrictT_ι, ← Category.assoc, hr'', ← Over.comp_left,
          hr₁]
        rfl
      have e₂ : r'' ≫ s.left ∣_ V = w₂.left := by
        rw [← cancel_mono V.ι, Category.assoc, restrictS_ι, ← Category.assoc, hr'', ← Over.comp_left,
          hr₂]
        rfl
      apply Over.OverMorphism.ext
      change w₁.left ≫ q = w₂.left ≫ q
      rw [← e₁, ← e₂, Category.assoc, Category.assoc, hpbq.w]
    · intro h
      have h' : w₁.left ≫ q = w₂.left ≫ q := congrArg CommaMorphism.left h
      let r'' := hpbq.lift w₁.left w₂.left h'
      have hr₁ : r'' ≫ restrictT t.left s.left V hVinv = w₁.left := hpbq.lift_fst _ _ _
      have hr₂ : r'' ≫ s.left ∣_ V = w₂.left := hpbq.lift_snd _ _ _
      let r₀ := r'' ≫ (s.left ⁻¹ᵁ V).ι
      have hr₀t : r₀ ≫ t.left = w₁.left ≫ V.ι := by
        rw [Category.assoc, ← restrictT_ι t.left s.left V hVinv, ← Category.assoc, hr₁]
      have hr₀s : r₀ ≫ s.left = w₂.left ≫ V.ι := by
        rw [Category.assoc, ← restrictS_ι s.left V, ← Category.assoc, hr₂]
      have hr₀ : r₀ ≫ R.hom = T.hom := by
        rw [← hRs, ← Category.assoc, hr₀s, Category.assoc]
        exact Over.w w₂
      let rh : T ⟶ R := Over.homMk r₀ hr₀
      have e₁ : rh ≫ t = w₁ ≫ p := Over.OverMorphism.ext hr₀t
      have e₂ : rh ≫ s = w₂ ≫ p := Over.OverMorphism.ext hr₀s
      rw [← e₁, ← e₂, Y.map_comp, Y.map_comp, Category.assoc, Category.assoc, hpb.w]
  obtain ⟨e, he⟩ := exists_iso_of_locallySurjective_of_same_kernel
    (F := ⟨Q.toFunctor, hQsh⟩) b' qo hb'ls (isLocallySurjective_schemeYoneda_map qo) hker
  -- (G) the open immersion, the pullback square and density
  let i := e.hom ≫ Q.ι
  have hi : IsOpenImmersion i := IsOpenImmersion.iso_comp e hQo
  have hsqw : Y.map qo ≫ i = Y.map p ≫ a := by
    change Y.map qo ≫ e.hom ≫ Q.ι = aV
    rw [← Category.assoc, he]
    rfl
  have hiinj : ∀ (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ), Function.Injective (i.app T) := by
    intro T x y hxy
    have h₁ : e.hom.app T x = e.hom.app T y := Subtype.ext hxy
    have hinv : ∀ z, e.inv.app T (e.hom.app T z) = z := fun z ↦
      ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id T) z
    rw [← hinv x, ← hinv y, h₁]
  have hBo : IsOpenImmersion (Subfunctor.range (Y.map p)).ι :=
    range_open (Y.map p) (isOpenImmersion_schemeYoneda_map p inferInstance)
  have : Mono p := Over.mono_of_mono_left p
  have hMlft : LocallyOfFiniteType Mo.hom := by
    have : LocallyOfFiniteType (q ≫ Mo.hom) := by
      change LocallyOfFiniteType (q ≫ EffectiveEpi.desc q (V.ι ≫ U.hom) hdesc)
      rw [EffectiveEpi.fac]
      infer_instance
    exact FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
      q Mo.hom
  refine ⟨Mo, Vo, i, p, Y.map qo, hMa, hMlft, hi, ?_, ?_⟩
  · apply isPullback_of_elements
    · intro T z
      exact congrArg (fun φ : Y.obj Vo ⟶ X.obj ↦ φ.app T z) hsqw
    · rintro T ⟨v⟩ ⟨v'⟩ - h₂
      have : v ≫ p = v' ≫ p := congrArg ULift.down h₂
      rw [(cancel_mono p).mp this]
    · intro T m g hmg
      have hmem : a.app T g ∈ Q.obj T := by
        rw [← hmg]
        exact (e.hom.app T m).2
      have hg : g ∈ (Subfunctor.range (Y.map p)).obj T := by
        apply OpenSubfunctorImages.mem_of_coveringSieve hBo g
        apply (fppfTopology (Spec (CommRingCat.of k))).superset_covering ?_ hmem
        intro T' f hf
        obtain ⟨⟨v⟩, hv⟩ := hf
        have hv' : a.app (op T') ⟨v ≫ p⟩ = a.app (op T') ⟨f ≫ g.down⟩ := by
          refine hv.trans ?_
          exact (a.naturality_apply f.op g).symm
        obtain ⟨v', hv'p⟩ := hfactor (f ≫ g.down) v ((happ _ _).mp hv')
        exact ⟨⟨v'⟩, congrArg ULift.up hv'p⟩
      obtain ⟨z, hz⟩ := hg
      refine ⟨z, ?_, hz⟩
      apply hiinj T
      rw [hmg, ← hz]
      exact congrArg (fun φ : Y.obj Vo ⟶ X.obj ↦ φ.app T z) hsqw
  · change Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    exact (dense_iff_closure_eq.mpr genericPoints.closure).mono hEV

/-- The dense affine open statement, assuming the statements of Stacks 03BM and 03JE and the
invariance of the finite locus. -/
theorem separatedDenseAffineOpen_of
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u})
    (h03JE : FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u})
    (hfl : FiniteLocusInvariantProp.{u}) :
    SeparatedDenseAffineOpenStatement.{u} := by
  intro k _ X hX hd U a ha hs hUa hU
  obtain ⟨V, W, i, p, b, hV, -, hi, hpb, hdense⟩ :=
    separatedDenseAffineOpenLFT_of h03BM h03JE hfl k X hX hd U a ha hs hUa hU
  exact ⟨V, W, i, p, b, hV, hi, hpb, hdense⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
