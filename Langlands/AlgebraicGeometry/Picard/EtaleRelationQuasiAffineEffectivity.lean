import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotient
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Effective cartesian descent from an invariant quasi-affine cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.EtaleRelationQuasiAffineEffectivity

variable {S U : Scheme.{u}} {p : U ⟶ S} {E : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ U}

/-- Relation points are determined by their target and the base coordinate of their source. -/
lemma rel_ext (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) {T : Scheme.{u}} {r r' : T ⟶ E.R}
    (ht : r ≫ E.t = r' ≫ E.t) (hs : r ≫ E.s ≫ f = r' ≫ E.s ≫ f) : r = r' :=
  hcart.hom_ext ht hs

/-- The cartesian square restricted to the inverse image of an open of the chart. -/
lemma isPullback_restrict (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens) :
    IsPullback (E.t ∣_ W) ((E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f) ((W.ι ≫ f) ≫ p) p := by
  simpa only [Category.assoc] using (isPullback_morphismRestrict E.t W).paste_vert hcart

/-- The source map on the inverse image of an invariant open. -/
def sRestr (W : E.U.Opens) (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    (E.t ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  (E.R.isoOfEq hW).inv ≫ (E.s ∣_ W)

@[reassoc (attr := simp)]
lemma sRestr_ι (W : E.U.Opens) (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    sRestr W hW ≫ W.ι = (E.t ⁻¹ᵁ W).ι ≫ E.s := by
  simp [sRestr, morphismRestrict_ι]

/-- The descent datum on an invariant open: a point `(w, u)` goes to the source of the unique
relation point with target `w` whose source lies over `u`. -/
def sigma (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) : pullback ((W.ι ≫ f) ≫ p) p ⟶ W.toScheme :=
  (isPullback_restrict hcart W).isoPullback.inv ≫ sRestr W hW

lemma sigma_snd (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    sigma hcart W hW ≫ W.ι ≫ f = pullback.snd _ _ := by
  simp [sigma, IsPullback.isoPullback_inv_snd]

@[reassoc]
lemma sigma_ι (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    sigma hcart W hW ≫ W.ι = (isPullback_restrict hcart W).isoPullback.inv ≫
      (E.t ⁻¹ᵁ W).ι ≫ E.s := by
  simp [sigma]

@[reassoc]
lemma iso_inv_ι_t (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens) :
    (isPullback_restrict hcart W).isoPullback.inv ≫ (E.t ⁻¹ᵁ W).ι ≫ E.t =
      pullback.fst _ _ ≫ W.ι := by
  rw [← morphismRestrict_ι, IsPullback.isoPullback_inv_fst_assoc]

@[reassoc]
lemma iso_inv_ι_s_f (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens) :
    (isPullback_restrict hcart W).isoPullback.inv ≫ (E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f =
      pullback.snd _ _ := by
  rw [IsPullback.isoPullback_inv_snd]

/-- The graph of the structure map is a section of the descent datum. -/
lemma sigma_section (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    pullback.lift (𝟙 W.toScheme) (W.ι ≫ f) (by simp) ≫ sigma hcart W hW = 𝟙 W.toScheme := by
  obtain ⟨r₀, hr₀t, hr₀s⟩ := E.refl W.toScheme W.ι
  let r₀' : W.toScheme ⟶ (E.t ⁻¹ᵁ W).toScheme :=
    (isPullback_morphismRestrict E.t W).lift (𝟙 _) r₀ (by simp [hr₀t])
  have hr₀' : r₀' ≫ (E.t ⁻¹ᵁ W).ι = r₀ := (isPullback_morphismRestrict E.t W).lift_snd _ _ _
  have hlift : pullback.lift (𝟙 W.toScheme) (W.ι ≫ f) (by simp) =
      r₀' ≫ (isPullback_restrict hcart W).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      exact ((isPullback_morphismRestrict E.t W).lift_fst _ _ _).symm
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd,
        reassoc_of% hr₀', reassoc_of% hr₀s]
  rw [← cancel_mono W.ι, Category.assoc, sigma_ι, hlift, Category.assoc, Iso.hom_inv_id_assoc,
    reassoc_of% hr₀', hr₀s, Category.id_comp]

/-- The cocycle identity of the descent datum, from transitivity of the relation. -/
lemma sigma_cocycle (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) :
    UnramifiedFunctor.CompletionDescent.firstLift p (W.ι ≫ f) ≫ sigma hcart W hW =
      UnramifiedFunctor.CompletionDescent.secondLift p (W.ι ≫ f) (sigma hcart W hW)
        (sigma_snd hcart W hW) ≫ sigma hcart W hW := by
  open UnramifiedFunctor.CompletionDescent in
  let ρ := (isPullback_restrict hcart W).isoPullback.inv
  let L1 := firstLift p (W.ι ≫ f)
  let L2 := secondLift p (W.ι ≫ f) (sigma hcart W hW) (sigma_snd hcart W hW)
  let fst₂ := pullback.fst (pullback.snd ((W.ι ≫ f) ≫ p) p ≫ p) p
  let r1 := fst₂ ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι
  let r2 := L2 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι
  let r3 := L1 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι
  have h12 : r1 ≫ E.s = r2 ≫ E.t := by
    change fst₂ ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.s = L2 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.t
    rw [iso_inv_ι_t hcart W, secondLift_fst_assoc, sigma_ι hcart W hW]
  obtain ⟨r'', hr''t, hr''s⟩ := E.trans _ r1 r2 h12
  have h3 : r3 = r'' := by
    apply rel_ext hcart
    · rw [hr''t]
      change L1 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.t = fst₂ ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.t
      rw [iso_inv_ι_t hcart W, firstLift_fst_assoc]
    · rw [reassoc_of% hr''s]
      change L1 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f = L2 ≫ ρ ≫ (E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f
      rw [iso_inv_ι_s_f hcart W, firstLift_snd, secondLift_snd]
  have key : L1 ≫ sigma hcart W hW ≫ W.ι = L2 ≫ sigma hcart W hW ≫ W.ι := by
    rw [sigma_ι hcart W hW]
    change r3 ≫ E.s = r2 ≫ E.s
    rw [h3, hr''s]
  rw [← Category.assoc L1, ← Category.assoc L2] at key
  exact (cancel_mono W.ι).mp key

/-- Local effectivity on an invariant quasi-affine open: the restricted relation has an fppf
quotient, obtained as the descent of the open along `p`. -/
theorem exists_local_quotient [IsAffine S] [IsAffine U] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (W : E.U.Opens)
    (hW : E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W) [W.toScheme.IsQuasiAffine] :
    ∃ (Y : Scheme.{u}) (π : W.toScheme ⟶ Y),
      (E.s ∣_ W) ≫ π = ((E.R.isoOfEq hW).hom ≫ (E.t ∣_ W)) ≫ π ∧
      Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsPullback (E.s ∣_ W) ((E.R.isoOfEq hW).hom ≫ (E.t ∣_ W)) π π := by
  obtain ⟨V, w, π, hpb, hco⟩ :=
    UnramifiedFunctor.CompletionDescent.exists_isPullback_of_isQuasiAffine p (W.ι ≫ f)
      (sigma hcart W hW) (sigma_snd hcart W hW) (sigma_section hcart W hW)
      (sigma_cocycle hcart W hW)
  have e1 : (E.t ∣_ W) = (isPullback_restrict hcart W).isoPullback.hom ≫ pullback.fst _ _ :=
    (IsPullback.isoPullback_hom_fst _).symm
  have e2 : sRestr W hW = (isPullback_restrict hcart W).isoPullback.hom ≫ sigma hcart W hW := by
    simp [sigma]
  have hco' : sRestr W hW ≫ π = (E.t ∣_ W) ≫ π := by
    rw [e1, e2, Category.assoc, Category.assoc (isPullback_restrict hcart W).isoPullback.hom
      (pullback.fst _ _) π, hco]
  have hkp : IsPullback (sRestr W hW) (E.t ∣_ W) π π := by
    refine IsPullback.of_right ?_ hco' hpb.flip
    have h1 : sRestr W hW ≫ W.ι ≫ f = (E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f := by simp
    rw [h1, hpb.w]
    exact (isPullback_restrict hcart W).flip
  have es : (E.s ∣_ W) = (E.R.isoOfEq hW).hom ≫ sRestr W hW := by simp [sRestr]
  refine ⟨V, π, ?_, MorphismProperty.of_isPullback hpb.flip ‹Flat p›,
    MorphismProperty.of_isPullback hpb.flip ‹LocallyOfFinitePresentation p›,
    MorphismProperty.of_isPullback hpb.flip ‹Surjective p›, ?_⟩
  · rw [es, Category.assoc, Category.assoc, hco']
  · rw [es]
    exact hkp.of_iso (E.R.isoOfEq hW).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

/-- Effective cartesian descent from a cover of the chart by invariant quasi-affine opens. -/
theorem exists_effective_of_invariantQuasiAffine [IsAffine S] [IsAffine U] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p]
    (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p)
    (hcov : ∀ x : E.U, ∃ W : E.U.Opens, x ∈ W ∧ E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W ∧
      W.toScheme.IsQuasiAffine) :
    ∃ (N : Over S) (q : E.U ⟶ N.left), IsPullback q f N.hom p ∧ E.t ≫ q = E.s ≫ q := by
  choose W hxW hinv hqa using hcov
  obtain ⟨Y, q, w, hflat, hlfp, hsurj, hkp, ⟨hcolim⟩⟩ :=
    FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict E.s E.t W hxW hinv
      (fun x => by
        have := hqa x
        exact exists_local_quotient hcart (W x) (hinv x))
  have hfp : E.s ≫ f ≫ p = E.t ≫ f ≫ p := by
    rw [← Category.assoc, ← hcart.w]
  obtain ⟨h, hqh⟩ : ∃ h : Y ⟶ S, q ≫ h = f ≫ p :=
    ⟨Cofork.IsColimit.desc hcolim (f ≫ p) hfp, Cofork.IsColimit.π_desc hcolim⟩
  refine ⟨Over.mk h, q, ?_, w.symm⟩
  change IsPullback q f h p
  -- the comparison map to the fibre product is an isomorphism, by fppf descent
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c : E.U ⟶ pullback h p, c ≫ pullback.fst h p = q ∧
      c ≫ pullback.snd h p = f :=
    ⟨pullback.lift q f hqh, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let f₀ := pullback.snd q (pullback.fst h p)
  have hfstw : E.t ≫ q = (E.s ≫ c) ≫ pullback.fst h p := by
    rw [Category.assoc, hc₁, w]
  obtain ⟨fst, hfst₁, hfst₂⟩ : ∃ fst : E.R ⟶ pullback q (pullback.fst h p),
      fst ≫ pullback.fst q (pullback.fst h p) = E.t ∧ fst ≫ f₀ = E.s ≫ c :=
    ⟨pullback.lift E.t (E.s ≫ c) hfstw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hA : IsPullback fst E.s f₀ c := by
    refine (IsPullback.of_bot ?_ hfst₂.symm (IsPullback.of_hasPullback q _).flip).flip
    rw [hfst₁, hc₁]
    exact hkp
  have hZ : IsPullback (f₀ ≫ pullback.snd h p) (pullback.fst q (pullback.fst h p)) p (f ≫ p) := by
    have := (IsPullback.of_hasPullback q (pullback.fst h p)).flip.paste_horiz
      (IsPullback.of_hasPullback h p).flip
    rwa [hqh] at this
  have hfst : IsIso fst := by
    have : fst = (hZ.isoIsPullback _ _ hcart.flip).inv := by
      apply hZ.hom_ext
      · rw [IsPullback.isoIsPullback_inv_fst, ← Category.assoc, hfst₂, Category.assoc, hc₂]
      · rw [IsPullback.isoIsPullback_inv_snd, hfst₁]
    rw [this]
    infer_instance
  have hc : IsIso c :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hA
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst
  exact IsPullback.of_iso_pullback ⟨hqh⟩ (asIso c) hc₁ hc₂

end Langlands.AlgebraicGeometry.EtaleRelationQuasiAffineEffectivity
