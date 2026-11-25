/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
public import WeilConjectures.RingTheory.MvPolynomial.QuotientBasis
public import WeilConjectures.RingTheory.MvPolynomial.QuotientSpan
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# The Hilbert functor of points of an affine space

For an affine scheme `S` and a type `n`, the Hilbert functor `Hilb^d` of the affine space
`𝔸(n; S) ⟶ S` is representable (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, Step 4).
For a family `w` of `d` polynomials with coefficients in `R = Γ(S, ⊤)`, the subfunctor `F_w` of
those `Z` for which the images of the `w l` form a basis of `𝒪_Z` is represented by the spectrum of
the universal ring `MvPolynomial.QuotientBasisRing w`; these subfunctors are open, and they cover
`Hilb^d` since locally `𝒪_Z` has a basis of monomials.

## Main statements

- `AlgebraicGeometry.isRepresentable_hilbertPresheaf_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

section Algebra

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']

/-- A ring map is finite, flat, of finite presentation and of rank `d` at every prime. -/
private def HilbCond (d : ℕ) (f : A →+* B) : Prop :=
  f.Finite ∧ f.Flat ∧ f.FinitePresentation ∧ ∀ p, f.finrank p = d

/-- `HilbCond` is preserved by composing with a ring isomorphism. -/
private lemma HilbCond.ringEquiv_comp {d : ℕ} {f : A →+* B} (h : HilbCond d f) (e : B ≃+* B') :
    HilbCond d (e.toRingHom.comp f) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨(RingHom.Finite.of_surjective _ e.surjective).comp h₁,
    h₂.comp (RingHom.Flat.of_bijective e.bijective),
    (RingHom.FinitePresentation.of_surjective _ e.surjective ?_).comp h₃, fun p ↦ ?_⟩
  · rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).1 e.injective]
    exact Submodule.fg_bot
  · rw [RingHom.finrank_comp_left_of_bijective _ _ e.bijective h₁ h₂, h₄]

/-- `HilbCond` is invariant under composing with a ring isomorphism. -/
private lemma hilbCond_ringEquiv_comp_iff {d : ℕ} (f : A →+* B) (e : B ≃+* B') :
    HilbCond d (e.toRingHom.comp f) ↔ HilbCond d f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.ringEquiv_comp e⟩
  convert h.ringEquiv_comp e.symm
  ext
  simp

/-- `HilbCond` of an algebra map, in terms of the module and algebra structure. -/
private lemma hilbCond_algebraMap_iff {d : ℕ} [Algebra A B] :
    HilbCond d (algebraMap A B) ↔ Module.Finite A B ∧ Module.Flat A B ∧
      Algebra.FinitePresentation A B ∧ ∀ p, Module.rankAtStalk (R := A) B p = d := by
  rw [HilbCond, RingHom.finite_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.finitePresentation_algebraMap, RingHom.finrank_algebraMap]

/-- A quotient of `A[n]` with a basis of `d` elements is finite, flat, finitely presented of
rank `d`. -/
private lemma hilbCond_of_isQuotientBasis {R : Type u} [CommRing R] {n : Type u} {d : ℕ}
    {w : Fin d → MvPolynomial n R} [Algebra R A] {I : Ideal (MvPolynomial n A)}
    (hI : MvPolynomial.IsQuotientBasis w I) :
    HilbCond d (algebraMap A (MvPolynomial n A ⧸ I)) := by
  let b := Module.Basis.mk hI.1 hI.2.ge
  have : Module.Free A (MvPolynomial n A ⧸ I) := .of_basis b
  have : Module.Finite A (MvPolynomial n A ⧸ I) := .of_basis b
  have : Module.FinitePresentation A (MvPolynomial n A ⧸ I) := 
    Module.finitePresentation_of_projective _ _
  rw [hilbCond_algebraMap_iff]
  refine ⟨inferInstance, inferInstance, .of_finitePresentation _ _, fun p ↦ ?_⟩
  have : Nontrivial A := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Module.finrank_eq_card_basis b,
    Fintype.card_fin, Nat.cast_id]

/-- Transport of the Hilbert condition along `A[n] ≃ B`. -/
private lemma hilbCond_quotient_iff {n : Type*} {d : ℕ} (E : MvPolynomial n A ≃+* B)
    (σ : A →+* B) (hσ : E.toRingHom.comp MvPolynomial.C = σ) (K : Ideal B) :
    HilbCond d ((Ideal.Quotient.mk K).comp σ) ↔
      HilbCond d (algebraMap A (MvPolynomial n A ⧸ K.comap E)) := by
  let e := Ideal.quotientEquiv (K.comap E) K E (Ideal.map_comap_of_surjective _ E.surjective K).symm
  rw [← hilbCond_ringEquiv_comp_iff _ e]
  congr! 1
  ext a
  simp [e, ← hσ]

end Algebra

section Dictionary

variable {n : Type u} {S : Scheme.{u}} {d : ℕ}

/-- The ideal of `Γ(T)[n]` of a point of the Hilbert functor of `𝔸(n; S)` over an affine `T`. -/
private noncomputable def hilbIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) : Ideal (MvPolynomial n Γ(T.left, ⊤)) :=
  (x.1.ideal ⟨⊤, isAffineOpen_top _⟩).comap (AffineSpace.toΓPullback n T.hom)

/-- `toΓPullback` as a ring isomorphism. -/
private noncomputable def toΓPullbackEquiv (T : Over S) [IsAffine T.left] :
    MvPolynomial n Γ(T.left, ⊤) ≃+* Γ(pullback (𝔸(n; S) ↘ S) T.hom, ⊤) :=
  RingEquiv.ofBijective _ (AffineSpace.toΓPullback_bijective (n := n) T.hom)

/-- `toΓPullback` restricted to the constants is the pullback of `𝔸(n; S) ×[S] T ⟶ T`. -/
private lemma toΓPullbackEquiv_comp_C (T : Over S) [IsAffine T.left] :
    (toΓPullbackEquiv (n := n) T).toRingHom.comp MvPolynomial.C =
      (pullback.snd (𝔸(n; S) ↘ S) T.hom).appTop.hom := by
  ext a
  simp [toΓPullbackEquiv, AffineSpace.toΓPullback]

/-- Over an affine base, a point of the Hilbert functor is determined by its ideal. -/
private lemma hilbIdeal_injective {T : Over S} [IsAffine T.left] :
    Function.Injective (hilbIdeal (n := n) (d := d) (T := T)) := by
  intro x y h
  refine Subtype.ext (Scheme.IdealSheafData.ext_of_isAffine ?_)
  exact Ideal.comap_injective_of_surjective _
    (AffineSpace.toΓPullback_bijective (n := n) T.hom).2 h

/-- The quotient by the ideal of a point is finite flat finitely presented of rank `d`. -/
private lemma hilbCond_hilbIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) :
    HilbCond d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ hilbIdeal x)) := by
  have h := (isHilbertSubscheme_iff_of_isAffine _ d T x.1).1 x.2
  exact (hilbCond_quotient_iff (toΓPullbackEquiv T) _ (toΓPullbackEquiv_comp_C T) _).1 h

/-- The point of the Hilbert functor with a given ideal of `Γ(T)[n]`. -/
private noncomputable def ofHilbIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : HilbCond d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T) :=
  ⟨.ofIdealTop (K.map (toΓPullbackEquiv T)), by
    rw [isHilbertSubscheme_iff_of_isAffine, Scheme.IdealSheafData.ideal_top_ofIdealTop]
    refine (hilbCond_quotient_iff (toΓPullbackEquiv T) _ (toΓPullbackEquiv_comp_C T) _).2 ?_
    rwa [Ideal.comap_map_of_bijective _ (toΓPullbackEquiv T).bijective]⟩

/-- The ideal of `ofHilbIdeal K` is `K`. -/
private lemma hilbIdeal_ofHilbIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : HilbCond d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    hilbIdeal (ofHilbIdeal K hK) = K := by
  rw [hilbIdeal, ofHilbIdeal, Scheme.IdealSheafData.ideal_top_ofIdealTop]
  exact Ideal.comap_map_of_bijective _ (toΓPullbackEquiv T).bijective

/-- Naturality of `hilbIdeal`: pulling back a point extends its ideal. -/
private lemma hilbIdeal_map {T W : Over S} [IsAffine T.left] [IsAffine W.left] (a : W ⟶ T)
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) :
    hilbIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x) =
      (hilbIdeal x).map (MvPolynomial.map a.left.appTop.hom) := by
  have hT : x.1.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (hilbIdeal x).map (AffineSpace.toΓPullback n T.hom) :=
    (Ideal.map_comap_of_surjective _ (AffineSpace.toΓPullback_bijective n T.hom).2 _).symm
  generalize hilbIdeal x = K at hT
  rw [hilbIdeal]
  refine Eq.trans ?_
    (Ideal.comap_map_of_bijective _ (AffineSpace.toΓPullback_bijective n W.hom))
  congr 1
  refine (Scheme.IdealSheafData.ideal_top_comap_of_isAffine _ _).trans ?_
  rw [hT, Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  exact AffineSpace.appTop_pullbackMap_toΓPullback (n := n) T.hom W.hom a.left (Over.w a) p

end Dictionary

section Universal

variable {n : Type u} {S : Scheme.{u}} [IsAffine S] {d : ℕ}

/-- The `S`-scheme `Spec` of the universal ring of `w`-adapted ideals. -/
private noncomputable abbrev univObj (w : Fin d → MvPolynomial n Γ(S, ⊤)) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w))) ≫
    S.isoSpec.inv)

/-- The structure morphism of `univObj w`. -/
private lemma univObj_hom (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    (univObj w).hom = Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w))) ≫ S.isoSpec.inv :=
  rfl

/-- `univObj w` is affine. -/
private instance (w : Fin d → MvPolynomial n Γ(S, ⊤)) : IsAffine (univObj w).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The inverse of `X.isoSpec` on global sections. -/
private lemma isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  rw [← Iso.hom_comp_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom,
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]

/-- The ring map `QuotientBasisRing w ⟶ Γ(W)` of an `S`-morphism `W ⟶ univObj w`. -/
private noncomputable def univHom {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    (b : W ⟶ univObj w) : MvPolynomial.QuotientBasisRing w →+* Γ(W.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing w))).inv ≫
    b.left.appTop).hom

/-- `univHom b` is a map of `Γ(S)`-algebras. -/
private lemma univHom_comp_algebraMap {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    (b : W ⟶ univObj w) :
    (univHom b).comp (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w)) =
      W.hom.appTop.hom := by
  have h : CommRingCat.ofHom (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing w))).inv ≫
        b.left.appTop = (b.left ≫ (univObj w).hom).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, univObj_hom, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop, isoSpec_inv_appTop, Category.assoc]
    rfl
  rw [← Over.w b, ← h]
  rfl

/-- An `S`-morphism to `univObj w` is determined by its ring map. -/
private lemma univHom_injective {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S} :
    Function.Injective (univHom (w := w) (W := W)) := by
  intro b b' h
  refine Over.OverMorphism.ext (ext_of_isAffine ((cancel_epi
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing w))).inv).1 ?_))
  exact CommRingCat.hom_ext h

/-- Every map of `Γ(S)`-algebras `QuotientBasisRing w ⟶ Γ(W)` comes from an `S`-morphism. -/
private lemma exists_univHom_eq {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    (φ : MvPolynomial.QuotientBasisRing w →+* Γ(W.left, ⊤))
    (hφ : φ.comp (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w)) = W.hom.appTop.hom) :
    ∃ b : W ⟶ univObj w, univHom b = φ := by
  have h : CommRingCat.ofHom (algebraMap Γ(S, ⊤) (MvPolynomial.QuotientBasisRing w)) ≫
      (CommRingCat.ofHom φ : CommRingCat.of _ ⟶ Γ(W.left, ⊤)) = W.hom.appTop :=
    CommRingCat.hom_ext hφ
  have hb : (W.left.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom φ : CommRingCat.of _ ⟶ Γ(W.left, ⊤))) ≫ (univObj w).hom = W.hom := by
    rw [univObj_hom, Category.assoc, ← Spec.map_comp_assoc, h,
      ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  refine ⟨Over.homMk _ hb, ?_⟩
  simp only [univHom, Over.homMk_left, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality (S := Γ(W.left, ⊤)) (CommRingCat.ofHom φ), Iso.inv_hom_id_assoc,
    CommRingCat.hom_ofHom]

/-- Functoriality of `univHom`. -/
private lemma univHom_comp {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W W' : Over S} (a : W' ⟶ W)
    (b : W ⟶ univObj w) : univHom (a ≫ b) = a.left.appTop.hom.comp (univHom b) := by
  rw [univHom, univHom, Over.comp_left, Scheme.Hom.comp_appTop, ← Category.assoc,
    CommRingCat.hom_comp]

/-- Extensions of the universal ideal along algebra maps are `w`-adapted. -/
private lemma isQuotientBasis_map_quotientBasisIdeal {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    (φ : MvPolynomial.QuotientBasisRing w →+* A)
    (hφ : φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A) :
    MvPolynomial.IsQuotientBasis w
      ((MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ)) :=
  (MvPolynomial.quotientBasisEquiv w A ⟨φ, fun r ↦ RingHom.congr_fun hφ r⟩).2

/-- An algebra map is determined by the extension of the universal ideal along it. -/
private lemma eq_of_map_quotientBasisIdeal_eq {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    {φ ψ : MvPolynomial.QuotientBasisRing w →+* A}
    (hφ : φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A)
    (hψ : ψ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A)
    (h : (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ) =
      (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map ψ)) : φ = ψ := by
  have := (MvPolynomial.quotientBasisEquiv w A).injective
    (a₁ := ⟨φ, fun r ↦ RingHom.congr_fun hφ r⟩) (a₂ := ⟨ψ, fun r ↦ RingHom.congr_fun hψ r⟩)
    (Subtype.ext h)
  exact congrArg AlgHom.toRingHom this

/-- Every `w`-adapted ideal is an extension of the universal ideal. -/
private lemma exists_map_quotientBasisIdeal_eq {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    {I : Ideal (MvPolynomial n A)} (hI : MvPolynomial.IsQuotientBasis w I) :
    ∃ φ : MvPolynomial.QuotientBasisRing w →+* A,
      φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A ∧
        I = (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ) := by
  obtain ⟨φ, hφ⟩ := (MvPolynomial.quotientBasisEquiv w A).surjective ⟨I, hI⟩
  exact ⟨φ.toRingHom, RingHom.ext φ.commutes, (congrArg Subtype.val hφ).symm⟩

/-- The universal point of the Hilbert functor over `univObj w`. -/
private noncomputable def univPoint (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op (univObj w)) :=
  ofHilbIdeal ((MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map (univHom (𝟙 _)))) <|
    letI := (univObj w).hom.appTop.hom.toAlgebra
    hilbCond_of_isQuotientBasis (isQuotientBasis_map_quotientBasisIdeal _
      (univHom_comp_algebraMap _))

/-- The ideal of the pullback of the universal point along `b`. -/
private lemma hilbIdeal_map_univPoint {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    [IsAffine W.left] (b : W ⟶ univObj w) :
    hilbIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map b.op (univPoint w)) =
      (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map (univHom b)) := by
  rw [hilbIdeal_map, univPoint, hilbIdeal_ofHilbIdeal, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, MvPolynomial.map_map, ← univHom_comp, Category.comp_id]

/-- The annihilator of the cokernel of the images of the `w l` in the quotient of `Γ(T)[n]`
of a point `x`: the locus of `T` where these images span, hence form a basis. -/
private noncomputable def spanAnn {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    Ideal Γ(T.left, ⊤) :=
  Module.annihilator Γ(T.left, ⊤) ((MvPolynomial n Γ(T.left, ⊤) ⧸ hilbIdeal x) ⧸
    Submodule.span Γ(T.left, ⊤) (Set.range fun l ↦
      Ideal.Quotient.mk (hilbIdeal x) (MvPolynomial.map T.hom.appTop.hom (w l))))

/-- A pullback of `x` comes from the universal point if and only if `spanAnn x w` generates
the unit ideal. -/
private lemma exists_eq_univPoint_iff {T W : Over S} [IsAffine T.left] [IsAffine W.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤))
    (a : W ⟶ T) :
    (∃ b : W ⟶ univObj w, (hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x =
      (hilbertPresheaf (𝔸(n; S) ↘ S) d).map b.op (univPoint w)) ↔
      (spanAnn x w).map a.left.appTop.hom = ⊤ := by
  let := W.hom.appTop.hom.toAlgebra
  obtain ⟨hfin, -, -, -⟩ := (hilbCond_algebraMap_iff (d := d)).1 (hilbCond_hilbIdeal x)
  have hW := hilbCond_hilbIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x)
  rw [hilbIdeal_map] at hW
  obtain ⟨hfinW, hflat, hfp, hrank⟩ := (hilbCond_algebraMap_iff (d := d)).1 hW
  have hfp' : Module.FinitePresentation Γ(W.left, ⊤)
      (MvPolynomial n Γ(W.left, ⊤) ⧸ (hilbIdeal x).map (MvPolynomial.map a.left.appTop.hom)) :=
    .of_finite_of_finitePresentation _ _
  have hw (l : Fin d) : MvPolynomial.map (algebraMap Γ(S, ⊤) Γ(W.left, ⊤)) (w l) =
      MvPolynomial.map a.left.appTop.hom (MvPolynomial.map T.hom.appTop.hom (w l)) := by
    rw [MvPolynomial.map_map, RingHom.algebraMap_toAlgebra, ← Over.w a, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp]
  rw [spanAnn, ← MvPolynomial.span_range_mk_map_eq_top_iff]
  simp_rw [← hw]
  trans MvPolynomial.IsQuotientBasis w ((hilbIdeal x).map (MvPolynomial.map a.left.appTop.hom))
  · rw [← hilbIdeal_map]
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, hilbIdeal_map_univPoint]
      exact isQuotientBasis_map_quotientBasisIdeal _ (univHom_comp_algebraMap b)
    · intro h
      obtain ⟨φ, hφ, hI⟩ := exists_map_quotientBasisIdeal_eq h
      obtain ⟨b, rfl⟩ := exists_univHom_eq φ hφ
      exact ⟨b, hilbIdeal_injective (hI.trans (hilbIdeal_map_univPoint b).symm)⟩
  · exact ⟨fun h ↦ h.2, fun h ↦ ⟨linearIndependent_of_span_eq_top_of_rankAtStalk _ h hrank, h⟩⟩

end Universal

/-- A morphism `a : W ⟶ T` from an affine scheme lands in the complement of the zero locus of
an ideal `J` of `Γ(T)` if and only if `J` generates the unit ideal of `Γ(W)`. -/
private lemma range_subset_compl_zeroLocus_iff {T W : Scheme.{u}} [IsAffine W] (a : W ⟶ T)
    (J : Ideal Γ(T, ⊤)) :
    Set.range a ⊆ (T.zeroLocus (U := ⊤) (J : Set Γ(T, ⊤)))ᶜ ↔ J.map a.appTop.hom = ⊤ := by
  rw [Set.range_subset_iff, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top, Ideal.map,
    PrimeSpectrum.zeroLocus_span, ← W.toSpecΓ_image_zeroLocus, Set.image_eq_empty,
    Set.eq_empty_iff_forall_notMem]
  refine forall_congr' fun y ↦ ?_
  simp only [Set.mem_compl_iff, Scheme.mem_zeroLocus_iff, Set.forall_mem_image,
    ← Scheme.preimage_basicOpen_top]
  rfl

/-- **The Hilbert functor of an affine space over an affine base** (blueprint
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 4). For an affine scheme `S` and any set `n`
of variables, `Hilb^d` of the affine space `𝔸(n; S) ⟶ S` is representable. It is glued from the
affine schemes representing the subfunctors `F_W`, for `W` a set of `d` polynomials, of those `Z`
for which the images of the elements of `W` form a basis of `𝒪_Z`; these subfunctors are open and
cover `Hilb^d`. -/
theorem isRepresentable_hilbertPresheaf_affineSpace (n : Type u) (S : Scheme.{u}) [IsAffine S]
    (d : ℕ) : (hilbertPresheaf (𝔸(n; S) ↘ S) d).IsRepresentable := by
  refine Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over_of_isAffine _
    (isSheaf_zariskiTopology_hilbertPresheaf _ d) univObj univPoint
    (fun w T _ b b' h ↦ ?_) (fun w T _ x ↦ ?_) (fun T _ x t ↦ ?_)
  · let := T.hom.appTop.hom.toAlgebra
    have h' := congrArg hilbIdeal h
    rw [hilbIdeal_map_univPoint, hilbIdeal_map_univPoint] at h'
    exact univHom_injective (eq_of_map_quotientBasisIdeal_eq (univHom_comp_algebraMap b)
      (univHom_comp_algebraMap b') h')
  · refine ⟨⟨(T.left.zeroLocus (U := ⊤) (spanAnn x w : Set Γ(T.left, ⊤)))ᶜ,
      (Scheme.zeroLocus_isClosed _ _).isOpen_compl⟩, fun W _ a ↦ ?_⟩
    rw [exists_eq_univPoint_iff, ← range_subset_compl_zeroLocus_iff]
    rfl
  · obtain ⟨hfin, hflat, hfp, hrank⟩ := (hilbCond_algebraMap_iff (d := d)).1 (hilbCond_hilbIdeal x)
    have : Module.FinitePresentation Γ(T.left, ⊤)
        (MvPolynomial n Γ(T.left, ⊤) ⧸ hilbIdeal x) :=
      .of_finite_of_finitePresentation _ _
    obtain ⟨v, hv⟩ := MvPolynomial.exists_monomials_annihilator_not_le (hilbIdeal x)
      (T.left.toSpecΓ t) (hrank _)
    obtain ⟨f, hfJ, hft⟩ := Set.not_subset.1 hv
    let w : Fin d → MvPolynomial n Γ(S, ⊤) := fun l ↦ MvPolynomial.monomial (v l) 1
    have hw : (fun l ↦ Ideal.Quotient.mk (hilbIdeal x) (MvPolynomial.map T.hom.appTop.hom (w l))) =
        fun l ↦ Ideal.Quotient.mk (hilbIdeal x) (MvPolynomial.monomial (v l) 1) := by
      simp [w, MvPolynomial.map_monomial]
    have hJ : f ∈ spanAnn x w := by
      rwa [spanAnn, hw]
    let W : Over S := Over.mk ((T.left.basicOpen f).ι ≫ T.hom)
    have : IsAffine W.left := (isAffineOpen_top T.left).basicOpen f
    let a : W ⟶ T := Over.homMk (T.left.basicOpen f).ι
    have hrange : Set.range a.left = T.left.basicOpen f := Scheme.Opens.range_ι _
    obtain ⟨b, hb⟩ := (exists_eq_univPoint_iff (W := W) x w a).2 (by
      rw [← range_subset_compl_zeroLocus_iff, hrange]
      exact fun y hy hz ↦ (Scheme.mem_zeroLocus_iff _ _ _).1 hz f hJ hy)
    refine ⟨w, W, a, b, ?_, hb⟩
    rw [hrange, ← Scheme.toSpecΓ_preimage_basicOpen]
    exact hft

end AlgebraicGeometry
