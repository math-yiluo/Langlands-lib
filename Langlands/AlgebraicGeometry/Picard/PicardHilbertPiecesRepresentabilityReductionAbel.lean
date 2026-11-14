import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionSetup

/-! # The Abel map of an open of the divisor scheme and its image sheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist

lemma cancel_add_right {Y : Scheme.{u}} {a b c e : Group Y} (h : a + c = b + c + e) :
    a = b + e := by
  rw [add_assoc, group_add_comm c e, ← add_assoc] at h
  exact add_right_cancel h

section BaseChange

variable {S X : Scheme.{u}} (f : X ⟶ S) {κ : Type}
  {U : ∀ (T : Scheme.{u}) (s : T ⟶ S), (pullback f s).Modules → κ → ℕ → T.Opens}

/-- Base change of the opens along a morphism of `S`-schemes with an arbitrary structure map. -/
lemma hU2' (hU2 : HU2 f U) {T T' : Scheme.{u}} [IsLocallyNoetherian T] [IsLocallyNoetherian T']
    {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') (L : (pullback f s).Modules)
    (hL : Scheme.Modules.IsInvertible L) (c : κ) (n : ℕ) :
    U T' s' ((Scheme.Modules.pullback (mapX f h w)).obj L) c n = h ⁻¹ᵁ U T s L c n := by
  subst w
  exact hU2 T T' s h L hL c n

end BaseChange

section Abel

variable {S X : Scheme.{u}} (f : X ⟶ S) (𝓛X : X.Modules)
  (h𝓛X : Scheme.Modules.IsInvertible 𝓛X) {D : Scheme.{u}} (d : D ⟶ S)
  (W : RelativeEffectiveDivisor (pullback.snd f d)) (m : ℕ)

/-- An open `Z₀` of the divisor scheme as a scheme over `S`. -/
abbrev Zo (Z₀ : D.Opens) : Over S := Over.mk (Z₀.ι ≫ d)

/-- The Abel map `Z₀ ⟶ Pic`: a point `y` of `Z₀` goes to the class of `L_W` pulled back
along `y`. -/
def abelMap (Z₀ : D.Opens) :
    uliftYoneda.{u + 1}.obj (Zo d Z₀) ⟶ RelativePicard.classSheafPresheaf f :=
  uliftYonedaEquiv.symm (scl f (Zo d Z₀) (ab f 𝓛X h𝓛X d W m (Zo d Z₀) Z₀.ι rfl))

lemma abelMap_app (Z₀ : D.Opens) (T : Over S) (x : T ⟶ Zo d Z₀) :
    (abelMap f 𝓛X h𝓛X d W m Z₀).app (op T) (ULift.up x) =
      scl f T (ab f 𝓛X h𝓛X d W m T (x.left ≫ Z₀.ι) ((Category.assoc _ _ _).trans (Over.w x))) := by
  change (RelativePicard.classSheafPresheaf f).map x.op
    (scl f (Zo d Z₀) (ab f 𝓛X h𝓛X d W m (Zo d Z₀) Z₀.ι rfl)) = _
  rw [map_scl, pb_ab]

/-- The class equation of a divisor of the linear system of a twist `L(m)`. -/
lemma linsys_class (hcl : Classifies f d W)
    (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u}) {T Λ : Scheme.{u}} {s : T ⟶ S}
    (l : Λ ⟶ T) (WΛ : RelativeEffectiveDivisor (pullback.snd (pullback.snd f s) l))
    (L : (pullback f s).Modules) (hL : Scheme.Modules.IsInvertible L) (NΛ : Λ.Modules)
    (hN : Scheme.Modules.IsInvertible NΛ)
    (e : WΛ.toEffectiveCartierDivisor.lineBundle.obj ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd f s) l)).obj
          (twist L ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m) ⊗
        (Scheme.Modules.pullback (pullback.snd (pullback.snd f s) l)).obj NΛ) :
    ∃ (y : Λ ⟶ D) (wy : y ≫ d = l ≫ s),
      W.ideal.comap (mapX f y wy) = WΛ.ideal.comap (bcIso f l rfl).hom ∧
      pt f 𝓛X h𝓛X d W m y wy =
        Group.pullback (mapX f l rfl) (icl L hL) +
          Group.pullback (pullback.snd f (l ≫ s)) (icl NΛ hN) := by
  have hM := isInvertible_twist hL (isInvertible_pullback (pullback.fst f s) h𝓛X) m
  obtain ⟨y, wy, h1, h2⟩ := linsys_classify f 𝓛X h𝓛X d W m hcl hbc l WΛ _ hM NΛ hN e
  refine ⟨y, wy, h1, cancel_add_right (c := m • cP f 𝓛X h𝓛X (l ≫ s)) ?_⟩
  rw [h2, icl_twist hL (isInvertible_pullback _ h𝓛X) m hM, map_add, map_nsmul,
    icl_pullback _ _ h𝓛X, pb_mapX_fst]
  rfl

/-- The module on `X ×_S T` transported from a line bundle on `T ×_S X`. -/
abbrev tr (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    (pullback f T.hom).Modules :=
  (Scheme.Modules.pullback (sym f T).inv).obj L.obj

lemma isInvertible_tr (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    Scheme.Modules.IsInvertible (tr f T L) :=
  isInvertible_pullback _ (isInvertible_lineBundle L)

lemma icl_tr (T : Over S) (L : LineBundle ((relativeSpace f).obj T))
    (h : Scheme.Modules.IsInvertible (tr f T L)) :
    icl (tr f T L) h = Group.pullback (sym f T).inv L.classOf := by
  rw [icl_pullback _ _ (isInvertible_lineBundle L), icl_lineBundle]

lemma pb_relativeSpace_map {T T' : Over S} (k : T' ⟶ T) (L : LineBundle ((relativeSpace f).obj T))
    (h : Scheme.Modules.IsInvertible (tr f T L)) :
    Group.pullback ((relativeSpace f).map k) L.classOf =
      Group.pullback (sym f T').hom
        (Group.pullback (mapX f k.left (Over.w k)) (icl (tr f T L) h)) := by
  rw [← pb_comp_apply, ← relativeSpace_map_sym, pb_comp_apply, icl_tr, pb_iso_hom_inv]

section Opens

variable {κ : Type}
  (U : ∀ (T : Scheme.{u}) (s : T ⟶ S), (pullback f s).Modules → κ → ℕ → T.Opens)

/-- If a line bundle on `T ×_S X`, pulled back along `k : T' ⟶ T`, has the class of the Abel
class of a point `y` of `D`, then the preimage of its open is the preimage of `Z₀` under `y`. -/
lemma class_open [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (hε : ∃ ε : S ⟶ X, ε ≫ f = 𝟙 S) (hU1 : HU1 f U) (hU2 : HU2 f U) [IsLocallyNoetherian D]
    {T T' : Over S} [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left] (k : T' ⟶ T)
    (L : LineBundle ((relativeSpace f).obj T)) (y : T'.left ⟶ D) (wy : y ≫ d = T'.hom)
    (h : scl f T' (Group.pullback ((relativeSpace f).map k) L.classOf) =
      scl f T' (ab f 𝓛X h𝓛X d W m T' y wy)) (c : κ) :
    k.left ⁻¹ᵁ U T.left T.hom (tr f T L) c m = y ⁻¹ᵁ U D d (LW f 𝓛X h𝓛X d W m) c m := by
  have hL := isInvertible_tr f T L
  rw [← hU2' f hU2 k.left (Over.w k) _ hL c m]
  rw [pb_relativeSpace_map f k L hL, ab, scl_sym_eq_iff f hε] at h
  obtain ⟨n, hn⟩ := h
  exact U_eq_preimage f 𝓛X h𝓛X d W m U hU1 hU2 y wy _ (isInvertible_pullback _ hL) n
    (by rw [icl_pullback _ _ hL]; exact hn) c

end Opens

end Abel

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
