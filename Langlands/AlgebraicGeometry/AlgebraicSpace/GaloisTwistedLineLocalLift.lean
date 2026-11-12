import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineLocus
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Zariski-local lifts over `K'`-schemes

Let `W` be a scheme over `Spec K` whose structure map factors through `Spec K'`. Every point of
the Galois-twisted line over `W` lifts to the line Zariski-locally on `W`. The pullback `P` of
the atlas along the point splits into two open pieces, according to whether the lifted point
uses the given `K'`-structure of `W` or its conjugate (the idempotent `splitIdem`). On each piece
the lifts over a common point of `W` are unique, so each piece maps to `W` by an étale
monomorphism, hence by an open immersion. These open immersions cover `W`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

open RelationQuotient KernelPair

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

/-! ### Ring-level facts -/

section Ring

variable {Γ Γ' : Type*} [CommRing Γ] [CommRing Γ']

theorem splitIdem_map (f : Γ →+* Γ') (μ₁ μ₂ : K' →+* Γ) :
    f (splitIdem D μ₁ μ₂) = splitIdem D (f.comp μ₁) (f.comp μ₂) := by
  simp [splitIdem]

/-- Two related points with the same restriction to `K'` are equal. -/
theorem comp_tStar_eq_of_restrict_eq (φ : RelationRing K' →+* Γ)
    (h : (φ.comp tStar).comp C = (φ.comp (sStar D)).comp C) :
    φ.comp tStar = φ.comp (sStar D) := by
  have he : φ (1, 0) = 1 := by
    rw [pairIdem_of_hom D φ, pairIdem, ← h]
    exact pairIdem_self (D := D) (x := φ.comp tStar)
  have h0 : φ (0, 1) = 0 := by
    rw [← one_sub_hom_one_zero, he, sub_self]
  refine RingHom.ext fun a => ?_
  have : tStar a - sStar D a = (0, 1) * (tStar a - sStar D a) := by
    ext <;> simp [tStar, sStar]
  have h1 : φ (tStar a - sStar D a) = 0 := by rw [this, map_mul, h0, zero_mul]
  rw [map_sub, sub_eq_zero] at h1
  exact h1

end Ring

/-! ### The pullback of the atlas along a point -/

section Pullback

variable {W : Over (Spec (CommRingCat.of K))} (x : (space D).presheaf.obj (op W))

/-- The map of presheaves given by a point. -/
abbrev ptMap : (schemeYoneda _).obj W ⟶ (space D).presheaf := uliftYonedaEquiv.{u + 1}.symm x

/-- The atlas is representable. -/
abbrev atlasRep : IsRepresentableMorphism (atlas D) := (atlas_isEtale D).representable

/-- The pullback of the atlas along `x`. -/
abbrev liftP : Over (Spec (CommRingCat.of K)) := (atlasRep D).pullback (ptMap D x)

/-- The projection of the pullback to `W`. -/
abbrev liftSnd : liftP D x ⟶ W := (atlasRep D).snd (ptMap D x)

/-- The projection of the pullback to the line. -/
def liftFst : liftP D x ⟶ lineOver K K' :=
  (schemeYoneda _).preimage ((atlasRep D).fst (ptMap D x))

theorem map_liftFst :
    (schemeYoneda _).map (liftFst D x) = (atlasRep D).fst (ptMap D x) :=
  (schemeYoneda _).map_preimage _

theorem isPullback_liftP :
    IsPullback ((schemeYoneda _).map (liftFst D x)) ((schemeYoneda _).map (liftSnd D x))
      (atlas D) (ptMap D x) := by
  rw [map_liftFst]
  exact (atlasRep D).isPullback _

theorem atlas_liftFst {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ liftP D x) :
    (atlas D).app (op T) ⟨k ≫ liftFst D x⟩ =
      (space D).presheaf.map (k ≫ liftSnd D x).op x := by
  have h := congrArg (fun φ => φ.app (op T) ⟨k⟩) (isPullback_liftP D x).w
  change (atlas D).app (op T) ⟨k ≫ liftFst D x⟩ =
    (ptMap D x).app (op T) ⟨k ≫ liftSnd D x⟩ at h
  rw [h, schemeYoneda_app_up, Equiv.apply_symm_apply]

theorem liftP_hom_ext {T : Over (Spec (CommRingCat.of K))} {h h' : T ⟶ liftP D x}
    (h₁ : h ≫ liftSnd D x = h' ≫ liftSnd D x) (h₂ : h ≫ liftFst D x = h' ≫ liftFst D x) :
    h = h' := by
  apply (schemeYoneda _).map_injective
  apply (isPullback_liftP D x).hom_ext
  · rw [← Functor.map_comp, ← Functor.map_comp, h₂]
  · rw [← Functor.map_comp, ← Functor.map_comp, h₁]

theorem etale_liftSnd : Etale (liftSnd D x).left :=
  (atlas_isEtale D).projection _ _ _ (isPullback_liftP D x)

theorem surjective_liftSnd : Surjective (liftSnd D x).left :=
  (atlas_isSurjective D).projection _ _ _ (isPullback_liftP D x)

end Pullback

/-! ### Units on basic opens -/

theorem ofSpec_precomp {T T' : Scheme.{u}} {R : Type u} [CommRing R] (f : T' ⟶ T)
    (g : T ⟶ Spec (CommRingCat.of R)) : ofSpec (f ≫ g) = f.appTop.hom.comp (ofSpec g) := by
  unfold ofSpec
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem isUnit_appTop_of_mem {T X : Scheme.{u}} (f : T ⟶ X) (e : Γ(X, ⊤))
    (h : ∀ t, f t ∈ X.basicOpen e) : IsUnit (f.appTop e) := by
  apply RingedSpace.isUnit_of_isUnit_germ T.toRingedSpace ⊤ _
  intro t _
  have ht : t ∈ T.basicOpen (f.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    exact h t
  exact (T.mem_basicOpen_top _ t).mp ht

theorem mem_basicOpen_or {X : Scheme.{u}} (e : Γ(X, ⊤)) (p : X) :
    p ∈ X.basicOpen e ∨ p ∈ X.basicOpen (1 - e) := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
  apply IsLocalRing.isUnit_or_isUnit_of_add_one
  rw [← map_add, add_sub_cancel, map_one]

/-! ### The two pieces of the pullback -/

section KStructure

variable {W : Over (Spec (CommRingCat.of K))} (q : W.left ⟶ Spec (CommRingCat.of K'))
  (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap K K')) = W.hom)
  (x : (space D).presheaf.obj (op W))

include hq in
theorem base_agree {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ W) (τ : T ⟶ lineOver K K')
    (c : K) : ofSpec (k.left ≫ q) (algebraMap K K' c) = ofSpec τ.left (C (algebraMap K K' c)) := by
  have e1 : (ofSpec (k.left ≫ q)).comp (algebraMap K K') = ofSpec T.hom := by
    rw [← ofSpec_comp, Category.assoc, hq, Over.w k]
  have e2 : (ofSpec τ.left).comp (algebraMap K K'[X]) = ofSpec T.hom := by
    rw [← ofSpec_comp]
    congr 1
    exact Over.w τ
  exact (congrArg (fun f => f c) e1).trans (congrArg (fun f => f c) e2).symm

/-- The idempotent on the pullback recording the type of the lifted point. -/
def liftIdem : Γ((liftP D x).left, ⊤) :=
  splitIdem D (ofSpec ((liftSnd D x).left ≫ q)) ((ofSpec (liftFst D x).left).comp C)

/-- On an open piece where the lifts over a common point of `W` have equal restrictions to `K'`,
the projection to `W` is a monomorphism. -/
theorem mono_of_restrict (O : (liftP D x).left.Opens)
    (hO : ∀ {T : Scheme.{u}} (h h' : T ⟶ O),
      h ≫ O.ι ≫ (liftSnd D x).left = h' ≫ O.ι ≫ (liftSnd D x).left →
      (ofSpec (h ≫ O.ι ≫ (liftFst D x).left)).comp C =
        (ofSpec (h' ≫ O.ι ≫ (liftFst D x).left)).comp C) :
    Mono (O.ι ≫ (liftSnd D x).left) := by
  constructor
  intro T h h' e
  have hw : (h' ≫ O.ι) ≫ (liftP D x).hom = (h ≫ O.ι) ≫ (liftP D x).hom := by
    rw [← Over.w (liftSnd D x)]
    have := congrArg (· ≫ W.hom) e
    simpa using this.symm
  let Tₒ : Over (Spec (CommRingCat.of K)) := Over.mk ((h ≫ O.ι) ≫ (liftP D x).hom)
  let k : Tₒ ⟶ liftP D x := Over.homMk (h ≫ O.ι) rfl
  let k' : Tₒ ⟶ liftP D x := Over.homMk (h' ≫ O.ι) hw
  have hs : k ≫ liftSnd D x = k' ≫ liftSnd D x := by
    ext1
    change (h ≫ O.ι) ≫ (liftSnd D x).left = (h' ≫ O.ι) ≫ (liftSnd D x).left
    simpa using e
  have ha : (atlas D).app (op Tₒ) ⟨k ≫ liftFst D x⟩ = (atlas D).app (op Tₒ) ⟨k' ≫ liftFst D x⟩ := by
    rw [atlas_liftFst, atlas_liftFst, hs]
  obtain ⟨r, hr₁, hr₂⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback (isPullback_atlas D)
    (k ≫ liftFst D x) (k' ≫ liftFst D x) (map_comp_eq_of_app_eq (atlas D) ha)
  have ht : (ofSpec r.left).comp tStar = ofSpec (k ≫ liftFst D x).left := by
    rw [← ofSpec_comp_tMap, ← hr₁]
    rfl
  have hs' : (ofSpec r.left).comp (sStar D) = ofSpec (k' ≫ liftFst D x).left := by
    rw [← ofSpec_comp_sMap, ← hr₂]
    rfl
  have hrestr := hO h h' e
  have heq := comp_tStar_eq_of_restrict_eq D (ofSpec r.left) (by
    rw [ht, hs']
    simpa [k, k'] using hrestr)
  rw [ht, hs'] at heq
  have hτ : k ≫ liftFst D x = k' ≫ liftFst D x := by
    ext1
    exact ofSpec_injective heq
  have hk := liftP_hom_ext D x hs hτ
  have : h ≫ O.ι = h' ≫ O.ι := congrArg CommaMorphism.left hk
  exact (cancel_mono O.ι).mp this

include hq in
/-- On the basic open of the idempotent, the lifted point uses the given `K'`-structure. -/
theorem restrict_on_basicOpen (O : (liftP D x).left.Opens)
    (hO : O ≤ (liftP D x).left.basicOpen (liftIdem D q x)) {T : Scheme.{u}} (g : T ⟶ O) :
    (ofSpec (g ≫ O.ι ≫ (liftFst D x).left)).comp C =
      ofSpec (g ≫ O.ι ≫ (liftSnd D x).left ≫ q) := by
  have hagree : ∀ c : K, (ofSpec ((liftSnd D x).left ≫ q)) (algebraMap K K' c) =
      ((ofSpec (liftFst D x).left).comp C) (algebraMap K K' c) :=
    fun c => base_agree q hq (liftSnd D x) (liftFst D x) c
  let ρ := (g ≫ O.ι).appTop.hom
  have hunit : IsUnit (ρ (liftIdem D q x)) :=
    isUnit_appTop_of_mem _ _ fun t => hO (g t).2
  have hidem : IsIdempotentElem (ρ (liftIdem D q x)) :=
    (splitIdem_isIdempotentElem (D := D) hagree).map ρ
  have h1 : ρ (liftIdem D q x) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hidem
  rw [liftIdem, splitIdem_map] at h1
  have e1 : ofSpec (g ≫ O.ι ≫ (liftFst D x).left) = ρ.comp (ofSpec (liftFst D x).left) := by
    rw [← Category.assoc, ofSpec_precomp]
  have e2 : ofSpec (g ≫ O.ι ≫ (liftSnd D x).left ≫ q) =
      ρ.comp (ofSpec ((liftSnd D x).left ≫ q)) := by
    rw [show g ≫ O.ι ≫ (liftSnd D x).left ≫ q = (g ≫ O.ι) ≫ ((liftSnd D x).left ≫ q) by
      simp only [Category.assoc], ofSpec_precomp]
  rw [e1, e2]
  refine RingHom.ext fun α => ?_
  have := splitIdem_mul (D := D) (μ₁ := ρ.comp (ofSpec ((liftSnd D x).left ≫ q)))
    (μ₂ := ρ.comp ((ofSpec (liftFst D x).left).comp C)) (fun c => congrArg ρ (hagree c)) α
  rw [h1, one_mul, sub_eq_zero] at this
  exact this

include hq in
/-- On the basic open of `1 - e`, the lifted point uses the conjugate `K'`-structure. -/
theorem restrict_on_basicOpen_conj (O : (liftP D x).left.Opens)
    (hO : O ≤ (liftP D x).left.basicOpen (1 - liftIdem D q x)) {T : Scheme.{u}} (g : T ⟶ O) :
    (ofSpec (g ≫ O.ι ≫ (liftFst D x).left)).comp C =
      (ofSpec (g ≫ O.ι ≫ (liftSnd D x).left ≫ q)).comp D.σ.toRingHom := by
  have hagree : ∀ c : K, (ofSpec ((liftSnd D x).left ≫ q)) (algebraMap K K' c) =
      ((ofSpec (liftFst D x).left).comp C) (algebraMap K K' c) :=
    fun c => base_agree q hq (liftSnd D x) (liftFst D x) c
  let ρ := (g ≫ O.ι).appTop.hom
  have hunit : IsUnit (ρ (1 - liftIdem D q x)) :=
    isUnit_appTop_of_mem _ _ fun t => hO (g t).2
  have hidem : IsIdempotentElem (ρ (1 - liftIdem D q x)) :=
    ((splitIdem_isIdempotentElem (D := D) hagree).one_sub).map ρ
  have h1 : ρ (1 - liftIdem D q x) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hidem
  rw [map_sub, map_one, liftIdem, splitIdem_map] at h1
  have e1 : ofSpec (g ≫ O.ι ≫ (liftFst D x).left) = ρ.comp (ofSpec (liftFst D x).left) := by
    rw [← Category.assoc, ofSpec_precomp]
  have e2 : ofSpec (g ≫ O.ι ≫ (liftSnd D x).left ≫ q) =
      ρ.comp (ofSpec ((liftSnd D x).left ≫ q)) := by
    rw [show g ≫ O.ι ≫ (liftSnd D x).left ≫ q = (g ≫ O.ι) ≫ ((liftSnd D x).left ≫ q) by
      simp only [Category.assoc], ofSpec_precomp]
  rw [e1, e2]
  refine RingHom.ext fun α => ?_
  have := one_sub_splitIdem_mul (D := D) (μ₁ := ρ.comp (ofSpec ((liftSnd D x).left ≫ q)))
    (μ₂ := ρ.comp ((ofSpec (liftFst D x).left).comp C)) (fun c => congrArg ρ (hagree c)) α
  rw [h1, one_mul, sub_eq_zero] at this
  exact this

include hq in
theorem mono_piece : Mono (((liftP D x).left.basicOpen (liftIdem D q x)).ι ≫
    (liftSnd D x).left) := by
  apply mono_of_restrict D x
  intro T h h' e
  rw [restrict_on_basicOpen D q hq x _ le_rfl h, restrict_on_basicOpen D q hq x _ le_rfl h']
  have := congrArg (· ≫ q) e
  simp only [Category.assoc] at this
  rw [this]

include hq in
theorem mono_piece_conj : Mono (((liftP D x).left.basicOpen (1 - liftIdem D q x)).ι ≫
    (liftSnd D x).left) := by
  apply mono_of_restrict D x
  intro T h h' e
  rw [restrict_on_basicOpen_conj D q hq x _ le_rfl h,
    restrict_on_basicOpen_conj D q hq x _ le_rfl h']
  have := congrArg (· ≫ q) e
  simp only [Category.assoc] at this
  rw [this]

theorem lift_of_openImmersion (O : (liftP D x).left.Opens)
    [_root_.AlgebraicGeometry.IsOpenImmersion (O.ι ≫ (liftSnd D x).left)] {p : (liftP D x).left} (hp : p ∈ O) :
    ∃ (V : W.left.Opens), (liftSnd D x).left p ∈ V ∧
      ∃ τ : Over.mk (V.ι ≫ W.hom) ⟶ lineOver K K',
        (atlas D).app (op _) ⟨τ⟩ =
          (space D).presheaf.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ W.hom) ⟶ W).op x := by
  let f := O.ι ≫ (liftSnd D x).left
  refine ⟨f.opensRange, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  let e := f.isoOpensRange
  have he : e.inv ≫ f = f.opensRange.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  let j : Over.mk (f.opensRange.ι ≫ W.hom) ⟶ liftP D x :=
    Over.homMk (e.inv ≫ O.ι) (by
      change (e.inv ≫ O.ι) ≫ (liftP D x).hom = f.opensRange.ι ≫ W.hom
      rw [← Over.w (liftSnd D x), ← he]
      simp only [f, Category.assoc])
  have hj : j ≫ liftSnd D x = Over.homMk f.opensRange.ι rfl := by
    ext1
    change (e.inv ≫ O.ι) ≫ (liftSnd D x).left = f.opensRange.ι
    rw [← he, Category.assoc]
  refine ⟨j ≫ liftFst D x, ?_⟩
  rw [atlas_liftFst, hj]

include hq in
/-- **Zariski-local lifts.** Over a scheme with a `K'`-structure compatible with its structure
over `K`, every point of the Galois-twisted line lifts to the line on an open neighbourhood of
each point. -/
theorem exists_local_lift (w : W.left) :
    ∃ (V : W.left.Opens), w ∈ V ∧
      ∃ τ : Over.mk (V.ι ≫ W.hom) ⟶ lineOver K K',
        (atlas D).app (op _) ⟨τ⟩ =
          (space D).presheaf.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ W.hom) ⟶ W).op x := by
  have := surjective_liftSnd D x
  obtain ⟨p, rfl⟩ := (liftSnd D x).left.surjective w
  have := etale_liftSnd D x
  rcases mem_basicOpen_or (liftIdem D q x) p with h1 | h2
  · have := mono_piece D q hq x
    have : _root_.AlgebraicGeometry.IsOpenImmersion
        (((liftP D x).left.basicOpen (liftIdem D q x)).ι ≫ (liftSnd D x).left) :=
      _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono _
    exact lift_of_openImmersion D x _ h1
  · have := mono_piece_conj D q hq x
    have : _root_.AlgebraicGeometry.IsOpenImmersion
        (((liftP D x).left.basicOpen (1 - liftIdem D q x)).ι ≫ (liftSnd D x).left) :=
      _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono _
    exact lift_of_openImmersion D x _ h2

end KStructure

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
