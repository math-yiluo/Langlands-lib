/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# The dual-number thickening is a base change

For a morphism of schemes `f : X ⟶ Y`, the square

```
X[ε] ──f[ε]──▶ Y[ε]
 │              │
 p              p
 ▼              ▼
 X ─────f─────▶ Y
```

is cartesian: a morphism `T ⟶ X[ε]` is a morphism `T ⟶ X` together with a square-zero global
function on `T` (the image of `ε`). In particular, for a scheme `X` over a field `k`, the
thickening `X[ε]` is `X ×_k Spec k[ε]`.

The morphism `T ⟶ T[ε]` attached to a square-zero function `t` is the identity on points and
`a + εb ↦ a + tb` on functions.

## Main statements

- `AlgebraicGeometry.Scheme.isPullback_dualNumbersProj`: the square above is a pullback square.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TrivSqZeroExt Opposite Limits

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- Evaluation `a + εb ↦ a + tb` at a square-zero element `t`. -/
private def evalSqZero {A : Type*} [CommRing A] (t : A) (ht : t * t = 0) : DualNumber A →+* A where
  toFun x := x.fst + t * x.snd
  map_one' := by simp
  map_mul' x y := by
    simp only [fst_mul, snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    linear_combination (-(x.snd * y.snd)) * ht
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add, snd_add]
    ring

private lemma mapRingHom_eps {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    DualNumber.mapRingHom φ (inr 1) = inr 1 := by
  ext
  · rw [DualNumber.fst_mapRingHom, fst_inr, fst_inr, map_zero]
  · rw [DualNumber.snd_mapRingHom, snd_inr, snd_inr, map_one]

private lemma evalSqZero_mapRingHom {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (t : A) (ht : t * t = 0) (t' : B) (ht' : t' * t' = 0) (h : φ t = t') (x : DualNumber A) :
    evalSqZero t' ht' (DualNumber.mapRingHom φ x) = φ (evalSqZero t ht x) := by
  subst h
  change (DualNumber.mapRingHom φ x).fst + φ t * (DualNumber.mapRingHom φ x).snd =
    φ (x.fst + t * x.snd)
  rw [DualNumber.fst_mapRingHom, DualNumber.snd_mapRingHom, map_add, map_mul]

/-- Two morphisms of schemes with the same underlying map are equal if they agree on sections,
in the form of `Scheme.Hom.appLE`. -/
private lemma hom_ext_appLE {f g : X ⟶ Y} (hb : f.base = g.base)
    (h : ∀ (U : Y.Opens) (V : X.Opens) (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U),
      f.appLE U V e₁ = g.appLE U V e₂) : f = g := by
  refine Scheme.Hom.ext hb fun U ↦ ?_
  rw [← Hom.appLE_eq_app, Hom.appLE_map]
  exact (h U _ _ le_rfl).trans (Hom.appLE_eq_app g)

private lemma appLE_comp_appLE_apply {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (V : X.Opens) (e₁ : W ≤ g ⁻¹ᵁ U) (e₂ : V ≤ f ⁻¹ᵁ W)
    (e : V ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (f ≫ g).appLE U V e a = f.appLE W V e₂ (g.appLE U W e₁ a) := by
  rw [← Hom.appLE_comp_appLE f g U W V e₁ e₂]
  rfl

private lemma appLE_map_apply (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : op V ⟶ op V') (a : Γ(Y, U)) :
    X.presheaf.map i (f.appLE U V e a) = f.appLE U V' (i.unop.le.trans e) a := by
  rw [← CommRingCat.comp_apply, Hom.appLE_map]

private lemma map_appLE_apply (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : op U' ⟶ op U) (a : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map i a) =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) a := by
  rw [← CommRingCat.comp_apply, Hom.map_appLE]

private lemma dualNumbersProj_appLE (U : X.Opens) (V : X.Opens)
    (e : V ≤ X.dualNumbersProj ⁻¹ᵁ U) (a : Γ(X, U)) :
    X.dualNumbersProj.appLE U V e a = inl (X.presheaf.map (homOfLE e).op a) := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom (inl a) = _
  ext
  · exact DualNumber.fst_mapRingHom _ _
  · exact (DualNumber.snd_mapRingHom _ _).trans (map_zero _)

private lemma dualNumbers_appLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f.dualNumbers ⁻¹ᵁ U) (x : Γ(Y.dualNumbers, U)) :
    f.dualNumbers.appLE U V e x = DualNumber.mapRingHom (f.appLE U V e).hom x := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom
    (DualNumber.mapRingHom (f.app U).hom x) = _
  exact (RingHom.congr_fun (DualNumber.mapRingHom_comp (f.app U).hom
    (X.presheaf.map (homOfLE e).op).hom) x).symm

/-- The restriction of a global function to an open. -/
private abbrev restrictTop' (t : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op t

private lemma restrictTop'_mul_self {t : Γ(X, ⊤)} (ht : t * t = 0) (U : X.Opens) :
    restrictTop' t U * restrictTop' t U = 0 := by
  rw [← map_mul, ht, map_zero]

private lemma presheaf_map_restrictTop' (t : Γ(X, ⊤)) {U V : X.Opens} (i : op U ⟶ op V) :
    X.presheaf.map i (restrictTop' t U) = restrictTop' t V := by
  rw [restrictTop', ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable (X) in
/-- The morphism `X ⟶ X[ε]` attached to a square-zero global function `t`: the identity on points
and `a + εb ↦ a + tb` on functions. -/
private noncomputable def liftSqZero (t : Γ(X, ⊤)) (ht : t * t = 0) : X ⟶ X.dualNumbers where
  base := 𝟙 _
  c := { app U := CommRingCat.ofHom (evalSqZero (restrictTop' t U.unop)
            (restrictTop'_mul_self ht U.unop))
         naturality U V i := by
          ext x
          exact evalSqZero_mapRingHom (X.presheaf.map i).hom _
            (restrictTop'_mul_self ht U.unop) _ (restrictTop'_mul_self ht V.unop)
            (presheaf_map_restrictTop' t i) x } ≫ (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    let U' : X.Opens := U
    let g' : DualNumber Γ(X, U') := g
    have hxU' : x ∈ U' := hxU
    change IsUnit (X.presheaf.germ U' x hxU' (g'.fst + restrictTop' t U' * g'.snd)) at hs
    refine (X.presheaf.isUnit_germ_dualNumber_iff x U' hxU' g').2 ?_
    rw [map_add] at hs
    have h0 : restrictTop' t U' * restrictTop' t U' = 0 := restrictTop'_mul_self ht U'
    have hn : IsNilpotent (-X.presheaf.germ U' x hxU' (restrictTop' t U' * g'.snd)) := by
      refine ⟨2, ?_⟩
      rw [neg_sq, ← map_pow, mul_pow, sq, h0, zero_mul, map_zero]
    simpa using hn.isUnit_add_right_of_commute hs (Commute.all _ _)

private lemma liftSqZero_appLE (t : Γ(X, ⊤)) (ht : t * t = 0) (U : X.Opens) (V : X.Opens)
    (e : V ≤ X.liftSqZero t ht ⁻¹ᵁ U) (x : DualNumber Γ(X, U)) :
    (X.liftSqZero t ht).appLE U V e x =
      X.presheaf.map (homOfLE e).op x.fst +
        restrictTop' t V * X.presheaf.map (homOfLE e).op x.snd := by
  change X.presheaf.map (homOfLE e).op (x.fst + restrictTop' t U * x.snd) = _
  erw [map_add, map_mul, presheaf_map_restrictTop']

private lemma liftSqZero_comp_proj (t : Γ(X, ⊤)) (ht : t * t = 0) :
    X.liftSqZero t ht ≫ X.dualNumbersProj = 𝟙 X := by
  refine hom_ext_appLE rfl fun U V e₁ e₂ ↦ ?_
  ext a
  rw [appLE_comp_appLE_apply (X.liftSqZero t ht) X.dualNumbersProj U U V le_rfl e₁]
  erw [dualNumbersProj_appLE, liftSqZero_appLE]
  change X.presheaf.map _ (X.presheaf.map _ a) + restrictTop' t V * X.presheaf.map _ 0 =
    X.presheaf.map (homOfLE e₂).op a
  rw [map_zero, mul_zero, add_zero, ← CommRingCat.comp_apply]
  erw [← Functor.map_comp]
  rfl

/-- The square-zero function `h^♯(ε)` attached to a morphism `h : T ⟶ S[ε]`. -/
private noncomputable def sqZeroParam (h : X ⟶ Y.dualNumbers) : Γ(X, ⊤) :=
  h.appTop (inr 1 : DualNumber Γ(Y, ⊤))

private lemma sqZeroParam_mul_self (h : X ⟶ Y.dualNumbers) :
    sqZeroParam h * sqZeroParam h = 0 := by
  exact (map_mul h.appTop.hom _ _).symm.trans ((congrArg _ (inr_mul_inr _ _ _)).trans
    (map_zero _))

/-- A morphism `h : T ⟶ S[ε]` is `T ⟶ T[ε] ⟶ S[ε]`, `ε ↦ h^♯(ε)` followed by `(h ≫ p)[ε]`. -/
private lemma eq_liftSqZero_comp_dualNumbers (h : X ⟶ Y.dualNumbers) :
    h = X.liftSqZero (sqZeroParam h) (sqZeroParam_mul_self h) ≫
      (h ≫ Y.dualNumbersProj).dualNumbers := by
  refine hom_ext_appLE rfl fun U V e₁ e₂ ↦ ?_
  ext y
  let U' : Y.Opens := U
  let y' : DualNumber Γ(Y, U') := y
  let g := h ≫ Y.dualNumbersProj
  let t := sqZeroParam h
  let φ : Γ(Y, U') →+* Γ(X, g ⁻¹ᵁ U') := (g.app U').hom
  let ψ : DualNumber Γ(Y, U') →+* Γ(X, g ⁻¹ᵁ U') := (h.app U).hom
  have hφ (a : Γ(Y, U')) : φ a = ψ (inl a) := rfl
  have hy : y' = inl y'.fst + inl y'.snd * inr 1 := by
    ext <;> simp
  have ht : restrictTop' t (g ⁻¹ᵁ U') = ψ (inr 1) := by
    have hn := ConcreteCategory.congr_hom (h.naturality (homOfLE le_top : U ⟶ ⊤).op)
      (inr 1 : DualNumber Γ(Y, ⊤))
    exact hn.symm.trans (congrArg ψ (mapRingHom_eps _))
  have key : ψ y' = φ y'.fst + restrictTop' t (g ⁻¹ᵁ U') * φ y'.snd := by
    rw [hφ, hφ, ht, mul_comm, ← map_mul, ← map_add, ← hy]
  change X.presheaf.map (homOfLE e₁).op (ψ y') = X.presheaf.map (homOfLE e₂).op
    ((DualNumber.mapRingHom φ y').fst +
      restrictTop' t (g ⁻¹ᵁ U') * (DualNumber.mapRingHom φ y').snd)
  rw [key, DualNumber.fst_mapRingHom, DualNumber.snd_mapRingHom]
  rfl

private lemma liftSqZero_congr {t t' : Γ(X, ⊤)} (ht : t * t = 0) (ht' : t' * t' = 0)
    (h : t = t') : X.liftSqZero t ht = X.liftSqZero t' ht' := by
  subst h
  rfl

private lemma dualNumbers_appTop_inr_one (f : X ⟶ Y) :
    f.dualNumbers.appTop (inr 1 : DualNumber Γ(Y, ⊤)) = (inr 1 : DualNumber Γ(X, ⊤)) := by
  change DualNumber.mapRingHom (f.appTop).hom (inr 1) = inr 1
  ext <;> simp

private lemma sqZeroParam_comp_dualNumbers {T : Scheme.{u}} (h : T ⟶ X.dualNumbers)
    (f : X ⟶ Y) : sqZeroParam (h ≫ f.dualNumbers) = sqZeroParam h := by
  change h.appTop (f.dualNumbers.appTop (inr 1 : DualNumber Γ(Y, ⊤))) = h.appTop (inr 1)
  exact congrArg h.appTop (dualNumbers_appTop_inr_one f)

/-- **The thickening is a base change.** For `f : X ⟶ Y`, the thickening `X[ε]` is the base
change of `p : Y[ε] ⟶ Y` along `f`: a morphism `T ⟶ X[ε]` is a morphism `T ⟶ X` together with a
square-zero function on `T`. -/
theorem isPullback_dualNumbersProj (f : X ⟶ Y) :
    IsPullback X.dualNumbersProj f.dualNumbers f Y.dualNumbersProj := by
  refine IsPullback.flip (IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (Hom.dualNumbers_comp_proj f)
    (fun s ↦ s.pt.liftSqZero (sqZeroParam s.fst) (sqZeroParam_mul_self s.fst) ≫
      s.snd.dualNumbers) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)))
  · rw [Category.assoc, ← Hom.dualNumbers_comp, ← s.condition]
    exact (eq_liftSqZero_comp_dualNumbers s.fst).symm
  · rw [Category.assoc, Hom.dualNumbers_comp_proj, ← Category.assoc, liftSqZero_comp_proj,
      Category.id_comp]
  · rw [eq_liftSqZero_comp_dualNumbers m, h₂]
    congr 1
    apply liftSqZero_congr
    rw [← h₁, sqZeroParam_comp_dualNumbers]

/-- Rescaling the infinitesimal commutes with the functoriality of the thickening:
`f[ε] ∘ (ε ↦ f^♯(c) ε) = (ε ↦ c ε) ∘ f[ε]`. -/
theorem dualNumbersScale_comp_dualNumbers (f : X ⟶ Y) (c : Γ(Y, ⊤)) :
    X.dualNumbersScale (f.appTop c) ≫ f.dualNumbers = f.dualNumbers ≫ Y.dualNumbersScale c := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  let U' : Y.Opens := U
  let a' : DualNumber Γ(Y, U') := a
  change DualNumber.scale (X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U' ⟶ ⊤).op (f.appTop c))
      (DualNumber.mapRingHom (f.app U').hom a') =
    DualNumber.mapRingHom (f.app U').hom
      (DualNumber.scale (Y.presheaf.map (homOfLE le_top : U' ⟶ ⊤).op c) a')
  have hc : X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U' ⟶ ⊤).op (f.appTop c) =
      f.app U' (Y.presheaf.map (homOfLE le_top : U' ⟶ ⊤).op c) :=
    (ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : U' ⟶ ⊤).op) c).symm
  ext
  · simp [DualNumber.fst_mapRingHom]
  · simp only [DualNumber.snd_scale, DualNumber.snd_mapRingHom, map_mul, hc]

end AlgebraicGeometry.Scheme
