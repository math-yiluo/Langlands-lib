/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback

/-!
# Naturality of the Kummer classes

The Kummer class `κ(u) : Λ_X ⟶ Λ_X(1)[1]` of a unit `u`
(`AlgebraicGeometry.Etale.kummerClassOf`, see
`WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic`) is natural under pullback:
for `f : X ⟶ Y`, the derived pullback `Lf^* κ(v)` is `κ(f^* v)`, up to the identifications
`Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)`. The Kummer classes therefore form a Kummer class
datum for the Tate twist `μₙ ⊗ Λ`.

## Main definitions

- `AlgebraicGeometry.Etale.hasKummerClass`: the Kummer class datum of the Tate twist `μₙ ⊗ Λ`,
  natural under pullback (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClassOf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [HasInvertibleExponent Λ X]
  [NeZero (ringChar Λ)]

section Naturality

variable {Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y)

lemma zmodToGmSections_zero_comp_gmSectionsPullback (v : Γ(Y, ⊤)ˣ) :
    zmodToGmSections 0 v (pow_zero v) ≫ gmSectionsPullback f =
      zmodToGmSections 0 (Units.map f.appTop.hom.toMonoidHom v) (pow_zero _) := by
  apply AddCommGrpCat.hom_ext_uliftInt
  have h1 := zmodToGmSections_natCast 0 v (pow_zero v) 1
  have h2 := zmodToGmSections_natCast 0 (Units.map f.appTop.hom.toMonoidHom v) (pow_zero _) 1
  simp only [Nat.cast_one, pow_one] at h1 h2
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, h1, h2, gmSectionsPullback_gmSection]

/-- The morphisms `ℤ ⟶ 𝔾ₘ` given by units are compatible with pullback. -/
lemma upperStar_map_unitToGmSheaf_comp (v : Γ(Y, ⊤)ˣ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map (unitToGmSheaf v) ≫
        upperStarGmSheafToGmSheaf f =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _ ≫
        unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v) := by
  rw [unitToGmSheaf, upperStar_map_constantSheafAdj_homEquiv_symm_comp,
    zmodToGmSections_zero_comp_gmSectionsPullback]
  rfl

/-- The comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` commutes with the `n`-th power maps. -/
lemma upperStarGmSheafToGmSheaf_comp_nsmul (m : ℕ) :
    upperStarGmSheafToGmSheaf f ≫ (m • 𝟙 X.gmSheaf) =
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (m • 𝟙 Y.gmSheaf) ≫
        upperStarGmSheafToGmSheaf f := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]

/-- The comparison map from the pullback of the Kummer sequence pulled back along `v` to the
Kummer sequence pulled back along the pullback of `v`, on the middle terms. -/
noncomputable def upperStarKummerPullbackX₂ (v : Γ(Y, ⊤)ˣ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        ((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).X₂ ⟶
      ((X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))).X₂ :=
  pullback.lift ((Etale.upperStar _ f).map (pullback.fst _ _) ≫ upperStarGmSheafToGmSheaf f)
    ((Etale.upperStar _ f).map (pullback.snd _ _) ≫
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _) (by
    change _ ≫ (ringChar Λ • 𝟙 X.gmSheaf) = _
    rw [Category.assoc, Category.assoc, upperStarGmSheafToGmSheaf_comp_nsmul,
      ← upperStar_map_unitToGmSheaf_comp, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact pullback.condition)

/-- The comparison from the pullback of the Kummer sequence pulled back along `v` to the Kummer
sequence pulled back along the pullback of `v`. -/
noncomputable def upperStarKummerPullbackHom (v : Γ(Y, ⊤)ˣ) :
    ((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).map
        (Etale.upperStar AddCommGrpCat.{u + 1} f) ⟶
      (X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v)) where
  τ₁ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf _ f
  τ₂ := upperStarKummerPullbackX₂ Λ f v
  τ₃ := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _
  comm₁₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, upperStarKummerPullbackX₂, pullback.lift_fst,
        ShortComplex.map_f, ShortComplex.pullback, ← Functor.map_comp_assoc]
      exact upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι _ f
    · simp only [Category.assoc, upperStarKummerPullbackX₂, pullback.lift_snd,
        ShortComplex.map_f, ShortComplex.pullback, ← Functor.map_comp_assoc]
      simp
  comm₂₃ := by
    simp [upperStarKummerPullbackX₂, ShortComplex.pullback]

/-- The comparison from the pullback of the Kummer sequence pulled back along `v`, with
coefficients extended to `Λ`, to the Kummer sequence pulled back along the pullback of `v`,
with coefficients extended to `Λ`. -/
noncomputable def upperStarKummerExtendScalarsHom (v : Γ(Y, ⊤)ˣ) :
    (((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).map (extendScalars Λ Y)).map
        (f)^*[ModuleCat.{u + 1} Λ] ⟶
      ((X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))).map (extendScalars Λ X) where
  τ₁ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₁
  τ₂ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₂
  τ₃ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₃
  comm₁₂ := by
    simp only [ShortComplex.map_f, Category.assoc, ← Functor.map_comp,
      (upperStarKummerPullbackHom Λ f v).comm₁₂]
    rw [Functor.map_comp]
    exact ((upperStarExtendScalarsIso Λ f).hom.naturality_assoc _ _).symm
  comm₂₃ := by
    simp only [ShortComplex.map_g, Category.assoc, ← Functor.map_comp,
      (upperStarKummerPullbackHom Λ f v).comm₂₃]
    rw [Functor.map_comp]
    exact ((upperStarExtendScalarsIso Λ f).hom.naturality_assoc _ _).symm

/-- Pasting a commutative square onto a commutative triangle, the second one under a functor. -/
private lemma comp_comp_map_comp_eq {D : Type*} [Category D] (T : D ⥤ D) {a b c d e g k : D}
    {x : a ⟶ b} {y : b ⟶ T.obj c} {z : c ⟶ d} {w : a ⟶ e} {δ : e ⟶ T.obj d} {t₁ : d ⟶ g}
    {t₃ : e ⟶ k} {δ' : k ⟶ T.obj g} (h₁ : x ≫ y ≫ T.map z = w ≫ δ)
    (h₂ : δ ≫ T.map t₁ = t₃ ≫ δ') :
    x ≫ y ≫ T.map (z ≫ t₁) = w ≫ t₃ ≫ δ' := by
  rw [T.map_comp, reassoc_of% h₁, h₂]

section SingleDelta

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- `leftDerivedUpperStar_map_singleδ` followed by a morphism `σ` of short exact sequences, with
the end terms, the connecting morphisms and the components of `σ` given up to equality. Instances
at a concrete coefficient category only have to match the latter up to these equalities, which
the kernel checks on the sheaves themselves, instead of under the derived pullback. -/
private lemma leftDerivedUpperStar_map_singleδ_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex (Sheaf Y.smallEtaleTopology A)} (hS : S.ShortExact)
    {S' : ShortComplex (Sheaf X.smallEtaleTopology A)} (hS' : S'.ShortExact)
    (σ : S.map (f)^*[A] ⟶ S') {Z₁ Z₃ : Sheaf Y.smallEtaleTopology A} (h₁ : S.X₁ = Z₁)
    (h₃ : S.X₃ = Z₃) {Z₁' Z₃' : Sheaf X.smallEtaleTopology A} (h₁' : S'.X₁ = Z₁')
    (h₃' : S'.X₃ = Z₃')
    {δ : (DerivedCategory.singleFunctor _ 0).obj Z₃ ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Z₁)⟦(1 : ℤ)⟧} (hδ : HEq δ hS.singleδ)
    {δ' : (DerivedCategory.singleFunctor _ 0).obj Z₃' ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Z₁')⟦(1 : ℤ)⟧} (hδ' : HEq δ' hS'.singleδ)
    {t₁ : (f)^*[A].obj Z₁ ⟶ Z₁'} (ht₁ : HEq t₁ σ.τ₁)
    {t₃ : (f)^*[A].obj Z₃ ⟶ Z₃'} (ht₃ : HEq t₃ σ.τ₃) :
    (L((f)^*[A])).map δ ≫ ((L((f)^*[A])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso A f).hom.app Z₁ ≫
          (DerivedCategory.singleFunctor _ 0).map t₁)⟦(1 : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso A f).hom.app Z₃ ≫
        (DerivedCategory.singleFunctor _ 0).map t₃ ≫ δ' := by
  subst h₁ h₃ h₁' h₃'
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hδ'
  obtain rfl := eq_of_heq ht₁
  obtain rfl := eq_of_heq ht₃
  have h2 := (ShortComplex.ShortExact.singleTriangle.map (hS.map_of_exact (f)^*[A]) hS' σ).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃] at h2
  exact comp_comp_map_comp_eq _ (leftDerivedUpperStar_map_singleδ A f hS) h2

end SingleDelta

omit [NeZero (ringChar Λ)] in
/-- The derived pullback of the connecting morphism of the Kummer sequence pulled back along `v`
is the connecting morphism of the Kummer sequence pulled back along the pullback of `v`:
```
Lf^*(Λ ⊗ ℤ_Y) ──Lf^* ∂(v)──▶ Lf^*((μₙ ⊗ Λ)[1]) ≅ (f^*(μₙ ⊗ Λ))[1]
      │                                           │
      ▼                                           ▼
  Λ ⊗ ℤ_X ──────────∂(f^* v)─────────────▶ (μₙ ⊗ Λ)[1]
```
-/
lemma leftDerivedUpperStar_map_kummerδ (v : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerδ Λ (unitToGmSheaf v)
        (fun y ↦ projective_sheafFiber_constantSheafInt (Y.uliftPointSmallEtale y))) ≫
      ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f)))⟦(1 : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((upperStarExtendScalarsIso Λ f).hom.app Y.constantSheafInt ≫
            (extendScalars Λ X).map
              ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _)) ≫
        kummerδ Λ (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))
          (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)) := by
  refine leftDerivedUpperStar_map_singleδ_comp _ f
    (shortExact_kummerSequence_pullback_map_extendScalars Λ (unitToGmSheaf v)
      (fun y ↦ projective_sheafFiber_constantSheafInt (Y.uliftPointSmallEtale y)))
    (shortExact_kummerSequence_pullback_map_extendScalars Λ
      (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))
      (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)))
    (upperStarKummerExtendScalarsHom Λ f v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rfl

/-- Pasting the squares of `leftDerivedUpperStar_map_kummerClassOf` in an arbitrary category: if a
functor `L` commuting with shifts `T`, `T'` (through `c`) maps the three factors `a`, `δ`, `e⁻¹⟦1⟧`
of a composite compatibly with the factors `a'`, `δ'`, `e'⁻¹⟦1⟧` of another one, then it maps the
composites compatibly. -/
private lemma map_comp_comp_shift_map_inv_eq {D D' : Type*} [Category D] [Category D']
    (L : D ⥤ D') (T : D ⥤ D) (T' : D' ⥤ D') (c : T ⋙ L ⟶ L ⋙ T') {P Q R U : D}
    {P' Q' R' U' M N : D'} {a : P ⟶ Q} {δ : Q ⟶ T.obj R} {e : U ≅ R} {θ : L.obj U ⟶ U'}
    {γ : L.obj P ⟶ P'} {a' : P' ⟶ Q'} {δ' : Q' ⟶ T'.obj R'} {e' : U' ≅ R'}
    {m₁ : L.obj Q ⟶ M} {n₁ : M ⟶ Q'} {m₃ : L.obj R ⟶ N} {n₃ : N ⟶ R'}
    (hA : L.map a ≫ m₁ ≫ n₁ = γ ≫ a') (hB : L.map e.hom ≫ m₃ ≫ n₃ = θ ≫ e'.hom)
    (hδ : L.map δ ≫ c.app R ≫ T'.map (m₃ ≫ n₃) = m₁ ≫ n₁ ≫ δ') :
    L.map (a ≫ δ ≫ T.map e.inv) ≫ c.app U ≫ T'.map θ = γ ≫ a' ≫ δ' ≫ T'.map e'.inv := by
  have hB' : L.map e.inv ≫ θ = (m₃ ≫ n₃) ≫ e'.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, ← hB, ← L.map_comp_assoc, e.inv_hom_id, L.map_id,
      Category.id_comp]
  have hc := c.naturality e.inv
  simp only [Functor.comp_map] at hc
  simp only [L.map_comp, Category.assoc]
  rw [reassoc_of% hc, ← T'.map_comp, hB', T'.map_comp, reassoc_of% hδ, reassoc_of% hA]

/-- The Kummer class is natural under pullback, `Lf^* κ(v) = κ(f^* v)`:
```
Lf^* Λ_Y ──Lf^* κ(v)──▶ Lf^*(Λ(1)[1]) ≅ (Lf^* Λ(1))[1]
    │                                  │
    ▼                                  ▼
   Λ_X ─────────κ(f^* v)──────────▶ Λ(1)[1]
```
-/
lemma leftDerivedUpperStar_map_kummerClassOf (v : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClassOf Y Λ v) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (tateTwistObject Λ Y 1) ≫
          (leftDerivedUpperStarTateTwistObjectIso Λ f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClassOf X Λ (Units.map f.appTop.hom.toMonoidHom v) := by
  rw [kummerClassOf_def, kummerClassOf_def]
  exact map_comp_comp_shift_map_inv_eq _ _ _ _
    (leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt Λ f)
    (leftDerivedUpperStar_map_tateTwistObjectOneIso Λ f) (leftDerivedUpperStar_map_kummerδ Λ f v)

end Naturality

/-- The Kummer class datum of the Tate twist `Λ(1) = μₙ ⊗ Λ`: the Kummer class of a unit is the
boundary of the unit in the Kummer sequence, with coefficients extended to `Λ`. -/
noncomputable instance hasKummerClass : HasKummerClass Λ where
  toHasTateTwist := hasTateTwist Λ
  kummerClass X _ u := kummerClassOf X Λ u
  kummerClass_mul X _ u v := kummerClassOf_mul X Λ u v
  leftDerivedUpperStar_map_kummerClass f u := leftDerivedUpperStar_map_kummerClassOf Λ f u

end Etale

end AlgebraicGeometry
