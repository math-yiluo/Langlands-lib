import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionPoints

/-! # Abel classes of the divisor scheme and the classification of linear systems -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist

section General

variable {S X : Scheme.{u}} (f : X ⟶ S)

lemma mapX_congr {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {h h' : T' ⟶ T} (e : h = h')
    (w : h ≫ s = s') (w' : h' ≫ s = s') : mapX f h w = mapX f h' w' := by
  subst e
  rfl

/-- `(relativeSpace f).map k` in terms of the comparison maps of the families `X ×_S T`. -/
lemma relativeSpace_map_sym {T T' : Over S} (k : T' ⟶ T) :
    (relativeSpace f).map k ≫ (sym f T).hom = (sym f T').hom ≫ mapX f k.left (Over.w k) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, sym_hom_fst, mapX_fst, sym_hom_fst,
      relativeSpace_map_snd]
  · rw [Category.assoc, Category.assoc, sym_hom_snd, mapX_snd, ← Category.assoc (sym f T').hom,
      sym_hom_snd]
    exact (relativeProjection f).naturality k

/-- `X ×_S T' ≅ (X ×_S T) ×_T T'` for a morphism `h : T' ⟶ T` of `S`-schemes. -/
abbrev bcIso {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    pullback f s' ≅ pullback (pullback.snd f s) h :=
  (isPullback_mapX f h w).isoPullback

@[reassoc (attr := simp)]
lemma bcIso_hom_fst {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    (bcIso f h w).hom ≫ pullback.fst (pullback.snd f s) h = mapX f h w :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma bcIso_hom_snd {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    (bcIso f h w).hom ≫ pullback.snd (pullback.snd f s) h = pullback.snd f s' :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
lemma bcIso_inv_snd {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    (bcIso f h w).inv ≫ pullback.snd f s' = pullback.snd (pullback.snd f s) h :=
  IsPullback.isoPullback_inv_snd _

@[reassoc]
lemma bcIso_inv_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    (bcIso f h w).inv ≫ mapX f h w = pullback.fst (pullback.snd f s) h :=
  IsPullback.isoPullback_inv_fst _

/-- The comparison maps of the linear-system statement in terms of those of `X ×_S -`. -/
lemma bcIso_hom_map {B T Λ : Scheme.{u}} {sB : B ⟶ S} {s : T ⟶ S} (l : Λ ⟶ B)
    (x : T ⟶ B) (wx : x ≫ sB = s) (k : T ⟶ Λ) (hk : k ≫ l = x) (wk : k ≫ l ≫ sB = s)
    (p₁ : pullback.snd f sB ≫ 𝟙 B = 𝟙 _ ≫ pullback.snd f sB) (p₂ : x ≫ 𝟙 B = k ≫ l) :
    (bcIso f x wx).hom ≫
        pullback.map (pullback.snd f sB) x (pullback.snd f sB) l (𝟙 _) k (𝟙 B) p₁ p₂ =
      mapX f k wk ≫ (bcIso f l rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, bcIso_hom_fst, Category.assoc,
      bcIso_hom_fst, mapX_comp]
    exact mapX_congr f hk.symm _ _
  · rw [Category.assoc, pullback.lift_snd, bcIso_hom_snd_assoc, Category.assoc, bcIso_hom_snd,
      mapX_snd]

lemma comap_injective_of_iso {Y Y' : Scheme.{u}} (e : Y' ≅ Y) {I J : Y.IdealSheafData}
    (h : I.comap e.hom = J.comap e.hom) : I = J := by
  have := congrArg (fun K => K.comap e.inv) h
  simp only [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
    Scheme.IdealSheafData.comap_id] at this
  exact this

lemma comap_preimage_ι_self {Y Z : Scheme.{u}} {V : Z.Opens} (a : Y ⟶ V) :
    (a ≫ V.ι) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

lemma eq_top_of_preimage_eq_top {Y Z : Scheme.{u}} (p : Y ⟶ Z) [Surjective p] (V : Z.Opens)
    (h : p ⁻¹ᵁ V = ⊤) : V = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨y, rfl⟩ := p.surjective z
  have hy : y ∈ p ⁻¹ᵁ V := h ▸ trivial
  exact hy

lemma range_subset_of_preimage_eq_top {Y Z : Scheme.{u}} (y : Y ⟶ Z) (V : Z.Opens)
    (h : y ⁻¹ᵁ V = ⊤) : Set.range y ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ y ⁻¹ᵁ V := h ▸ trivial
  exact ht

/-- A sieve on `T` over `S` containing a single flat, surjective, locally finitely presented
arrow is an fppf covering sieve. -/
lemma mem_fppf_over {T : Over S} (Sv : Sieve T) {V : Scheme.{u}} (p : V ⟶ T.left) [Flat p]
    [Surjective p] [LocallyOfFinitePresentation p]
    (h : Sv (Over.homMk p : Over.mk (p ≫ T.hom) ⟶ T)) :
    Sv ∈ Scheme.fppfTopology.over S T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck p.singleton_mem_fppfPrecoverage)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  exact (Sieve.overEquiv_iff _ _).2 h

end General

section Data

variable {S X : Scheme.{u}} (f : X ⟶ S) (𝓛X : X.Modules)
  (h𝓛X : Scheme.Modules.IsInvertible 𝓛X) {D : Scheme.{u}} (d : D ⟶ S)
  (W : RelativeEffectiveDivisor (pullback.snd f d)) (m : ℕ)

/-- The class of the pullback of `𝓛X` to `X ×_S T`. -/
def cP {T : Scheme.{u}} (s : T ⟶ S) : Group (pullback f s) :=
  Group.pullback (pullback.fst f s) (icl 𝓛X h𝓛X)

lemma pb_mapX_cP {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    Group.pullback (mapX f h w) (cP f 𝓛X h𝓛X s) = cP f 𝓛X h𝓛X s' :=
  pb_mapX_fst f h w _

/-- The class `[O(W)] - m [𝓛X]` on `X ×_S D`. -/
def cLW : Group (pullback f d) := dcl W.ideal W.2.1 - m • cP f 𝓛X h𝓛X d

/-- An invertible module `L_W` on `X ×_S D` with class `[O(W)] - m [𝓛X]`. -/
def LW : (pullback f d).Modules :=
  (Group.lineBundleRepresentative _ (cLW f 𝓛X h𝓛X d W m)).obj

lemma isInvertible_LW : Scheme.Modules.IsInvertible (LW f 𝓛X h𝓛X d W m) :=
  isInvertible_lineBundle _

lemma icl_LW (h : Scheme.Modules.IsInvertible (LW f 𝓛X h𝓛X d W m)) :
    icl (LW f 𝓛X h𝓛X d W m) h = cLW f 𝓛X h𝓛X d W m :=
  (icl_lineBundle _ _).trans (Group.classOf_lineBundleRepresentative _ _)

/-- The class of a point `y : T ⟶ D`: the pullback of `[L_W]` to `X ×_S T`. -/
def pt {T : Scheme.{u}} {s : T ⟶ S} (y : T ⟶ D) (w : y ≫ d = s) : Group (pullback f s) :=
  Group.pullback (mapX f y w) (cLW f 𝓛X h𝓛X d W m)

lemma pt_congr {T : Scheme.{u}} {s : T ⟶ S} {y y' : T ⟶ D} (e : y = y') (w : y ≫ d = s)
    (w' : y' ≫ d = s) : pt f 𝓛X h𝓛X d W m y w = pt f 𝓛X h𝓛X d W m y' w' := by
  subst e
  rfl

lemma pb_mapX_pt {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') (y : T ⟶ D) (wy : y ≫ d = s) :
    Group.pullback (mapX f h w) (pt f 𝓛X h𝓛X d W m y wy) =
      pt f 𝓛X h𝓛X d W m (h ≫ y) (by rw [Category.assoc, wy, w]) := by
  rw [pt, pt, ← pb_comp_apply, mapX_comp]

lemma icl_twist_pt {T : Scheme.{u}} {s : T ⟶ S} (y : T ⟶ D) (w : y ≫ d = s)
    (h : Scheme.Modules.IsInvertible (twist ((Scheme.Modules.pullback (mapX f y w)).obj
      (LW f 𝓛X h𝓛X d W m)) ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m)) :
    icl _ h = pt f 𝓛X h𝓛X d W m y w + m • cP f 𝓛X h𝓛X s := by
  rw [pt, cP, icl_twist (isInvertible_pullback _ (isInvertible_LW f 𝓛X h𝓛X d W m))
      (isInvertible_pullback _ h𝓛X) m h, icl_pullback _ _ (isInvertible_LW f 𝓛X h𝓛X d W m),
    icl_pullback _ _ h𝓛X, icl_LW]

lemma dcl_eq_icl {Y : Scheme.{u}} (I : Y.IdealSheafData) (hI : IsEffectiveCartierIdeal I) :
    dcl I hI = icl (EffectiveCartierDivisor.lineBundle ⟨I, hI⟩).obj (isInvertible_lineBundle _) :=
  (icl_lineBundle _ _).symm

/-- The divisor class of the pullback of the universal divisor along a point `y`. -/
lemma dcl_comap_mapX (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u}) {T : Scheme.{u}}
    {s : T ⟶ S} (y : T ⟶ D) (w : y ≫ d = s)
    (hJ : IsEffectiveCartierIdeal (W.ideal.comap (mapX f y w))) :
    dcl (W.ideal.comap (mapX f y w)) hJ = pt f 𝓛X h𝓛X d W m y w + m • cP f 𝓛X h𝓛X s := by
  obtain ⟨hJ', e⟩ := divBC f hbc y w W.ideal W.2
  rw [show dcl (W.ideal.comap (mapX f y w)) hJ = dcl (W.ideal.comap (mapX f y w)) hJ'.1 from rfl,
    e, pt, cLW, map_sub, map_nsmul, ← pb_mapX_cP f 𝓛X h𝓛X y w, sub_add_cancel]

/-- The universal property of the divisor scheme, as in the divisor statement. -/
def Classifies : Prop :=
  ∀ (T : Scheme.{u}) (s : T ⟶ S),
    (∀ (g : T ⟶ D) (hg : g ≫ d = s),
      IsRelativeEffectiveCartierIdeal (pullback.snd f s)
        (W.ideal.comap (pullback.map f s f d (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])))) ∧
    ∀ I : (pullback f s).IdealSheafData,
      IsRelativeEffectiveCartierIdeal (pullback.snd f s) I →
        ∃! g : T ⟶ D, ∃ hg : g ≫ d = s,
          W.ideal.comap (pullback.map f s f d (𝟙 X) g (𝟙 _) (by simp) (by simp [hg])) = I

lemma classifies_rel (hcl : Classifies f d W) {T : Scheme.{u}} {s : T ⟶ S} (y : T ⟶ D)
    (w : y ≫ d = s) :
    IsRelativeEffectiveCartierIdeal (pullback.snd f s) (W.ideal.comap (mapX f y w)) :=
  (hcl T s).1 y w

lemma classifies_eq (hcl : Classifies f d W) {T : Scheme.{u}} {s : T ⟶ S} (y y' : T ⟶ D)
    (w : y ≫ d = s) (w' : y' ≫ d = s)
    (h : W.ideal.comap (mapX f y w) = W.ideal.comap (mapX f y' w')) : y = y' := by
  obtain ⟨g, -, huniq⟩ := (hcl T s).2 _ ((hcl T s).1 y w)
  exact (huniq y ⟨w, rfl⟩).trans (huniq y' ⟨w', h.symm⟩).symm

/-- A divisor of a linear system of `M` on `(X ×_S T) ×_T Λ` is classified by a point of `D`,
whose class is that of `M` up to a class from `Λ`. -/
lemma linsys_classify (hcl : Classifies f d W)
    (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u}) {T Λ : Scheme.{u}} {s : T ⟶ S}
    (l : Λ ⟶ T) (WΛ : RelativeEffectiveDivisor (pullback.snd (pullback.snd f s) l))
    (M : (pullback f s).Modules) (hM : Scheme.Modules.IsInvertible M) (NΛ : Λ.Modules)
    (hN : Scheme.Modules.IsInvertible NΛ)
    (e : WΛ.toEffectiveCartierDivisor.lineBundle.obj ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd f s) l)).obj M ⊗
        (Scheme.Modules.pullback (pullback.snd (pullback.snd f s) l)).obj NΛ) :
    ∃ (y : Λ ⟶ D) (wy : y ≫ d = l ≫ s),
      W.ideal.comap (mapX f y wy) = WΛ.ideal.comap (bcIso f l rfl).hom ∧
      pt f 𝓛X h𝓛X d W m y wy + m • cP f 𝓛X h𝓛X (l ≫ s) =
        Group.pullback (mapX f l rfl) (icl M hM) +
          Group.pullback (pullback.snd f (l ≫ s)) (icl NΛ hN) := by
  obtain ⟨h1, hd1⟩ := flat_comap (bcIso f l rfl).hom (pullback.snd (pullback.snd f s) l)
    WΛ.ideal WΛ.2
  have h1' : IsRelativeEffectiveCartierIdeal (pullback.snd f (l ≫ s))
      (WΛ.ideal.comap (bcIso f l rfl).hom) := by
    rw [← bcIso_hom_snd f l rfl]
    exact h1
  obtain ⟨y, ⟨wy, hy⟩, -⟩ := (hcl Λ (l ≫ s)).2 _ h1'
  have hy' : W.ideal.comap (mapX f y wy) = WΛ.ideal.comap (bcIso f l rfl).hom := hy
  refine ⟨y, wy, hy', ?_⟩
  have hdc := dcl_comap_mapX f 𝓛X h𝓛X d W m hbc y wy (hy' ▸ h1.1)
  rw [← hdc, dcl_congr hy' _ h1.1, hd1]
  have hT := isInvertible_tensor (isInvertible_pullback
    (pullback.fst (pullback.snd f s) l) hM) (isInvertible_pullback
      (pullback.snd (pullback.snd f s) l) hN)
  have hW : dcl WΛ.ideal WΛ.2.1 = icl _ hT := by
    rw [dcl_eq_icl]
    exact (icl_eq_iff _ _ _ _).2 ⟨e⟩
  rw [hW, icl_tensor _ _ (isInvertible_pullback _ hM) (isInvertible_pullback _ hN),
    icl_pullback _ _ hM, icl_pullback _ _ hN, map_add, ← pb_comp_apply, ← pb_comp_apply,
    bcIso_hom_fst, bcIso_hom_snd]

section Opens

variable {κ : Type}
  (U : ∀ (T : Scheme.{u}) (s : T ⟶ S), (pullback f s).Modules → κ → ℕ → T.Opens)

/-- Invariance of the opens under twisting by invertible modules from the base, as in the
statement. -/
def HU1 : Prop :=
  ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ S)
    (L L' : (pullback f s).Modules) (N : T.Modules),
    Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
    Scheme.Modules.IsInvertible N →
    Nonempty (L ≅ L' ⊗ (Scheme.Modules.pullback (pullback.snd f s)).obj N) →
    ∀ (c : κ) (m : ℕ), U T s L c m = U T s L' c m

/-- Base change of the opens, as in the statement. -/
def HU2 : Prop :=
  ∀ (T T' : Scheme.{u}) [IsLocallyNoetherian T] [IsLocallyNoetherian T']
    (s : T ⟶ S) (h : T' ⟶ T) (L : (pullback f s).Modules),
    Scheme.Modules.IsInvertible L → ∀ (c : κ) (m : ℕ),
      U T' (h ≫ s) ((Scheme.Modules.pullback
          (pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) (by simp) (by simp))).obj L) c m =
        h ⁻¹ᵁ U T s L c m

/-- The open of an invertible module whose class is that of a point `y` of `D`, up to classes
from the base, is the preimage of the open `Z₀` of `L_W`. -/
lemma U_eq_preimage (hU1 : HU1 f U) (hU2 : HU2 f U) [IsLocallyNoetherian D] {T : Scheme.{u}}
    [IsLocallyNoetherian T] {s : T ⟶ S} (y : T ⟶ D) (w : y ≫ d = s)
    (L : (pullback f s).Modules) (hL : Scheme.Modules.IsInvertible L) (n : Group T)
    (hn : icl L hL = pt f 𝓛X h𝓛X d W m y w + Group.pullback (pullback.snd f s) n) (c : κ) :
    U T s L c m = y ⁻¹ᵁ U D d (LW f 𝓛X h𝓛X d W m) c m := by
  obtain ⟨N, hN, rfl⟩ := exists_icl n
  have hL' := isInvertible_pullback (mapX f y w) (isInvertible_LW f 𝓛X h𝓛X d W m)
  rw [hU1 T s L _ N hL hL' hN (nonempty_iso_tensor_of_icl hL hL' (isInvertible_pullback _ hN)
    (by rw [icl_pullback _ _ (isInvertible_LW f 𝓛X h𝓛X d W m), icl_pullback _ _ hN, icl_LW]
        exact hn)) c m]
  subst w
  exact hU2 D T d y _ (isInvertible_LW f 𝓛X h𝓛X d W m) c m

end Opens

/-- The Abel class of a point `y : T.left ⟶ D` on `T ×_S X`. -/
def ab (T : Over S) (y : T.left ⟶ D) (w : y ≫ d = T.hom) : Group ((relativeSpace f).obj T) :=
  Group.pullback (sym f T).hom (pt f 𝓛X h𝓛X d W m y w)

lemma pb_ab {T T' : Over S} (k : T' ⟶ T) (y : T.left ⟶ D) (w : y ≫ d = T.hom) :
    Group.pullback ((relativeSpace f).map k) (ab f 𝓛X h𝓛X d W m T y w) =
      ab f 𝓛X h𝓛X d W m T' (k.left ≫ y) (by rw [Category.assoc, w, Over.w k]) := by
  rw [ab, ab, ← pb_comp_apply, relativeSpace_map_sym, pb_comp_apply, pb_mapX_pt]

end Data

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
