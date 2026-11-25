/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassCup
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale

/-!
# The Thom class of the zero section of affine space over a field

For `B` separated and locally of finite type over a field, and the zero section `z : B ↪ 𝔸^c_B`,
cut out by the coordinates `t₁, …, t_c`, the adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])` of the cup product
with supports `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` (`AlgebraicGeometry.Etale.kummerBoundaryProduct`) is an
isomorphism.

The proof is an induction on `c`. The empty product is the unit class, which is itself an
isomorphism. For the step, `𝔸^{c+1}_B ≅ 𝔸¹_{B'}` with `B' = 𝔸^c_B`, the first coordinate becoming
the coordinate `t` of the affine line (`AlgebraicGeometry.Etale.affineSpaceConsIso`), and the
product of `n + 1` Kummer boundaries is `∂κ(t) ∪ (∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c))`. The adjoint of `∂κ(t)`
is an isomorphism by the rank-one normalisation `HasKummerClass.IsNormalized`, and the
restriction of the second factor to `V(t) ≅ B'` is the product for `B'`, whose adjoint is an
isomorphism by induction. The cup product criterion
`AlgebraicGeometry.Etale.isIso_supportedClassMap_cupWithSupports` concludes.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_of_etale`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_zero`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_cons_coord`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-! ### Geometry: splitting off the first coordinate -/

/-- The relabelling `ULift (Fin c) ⊕ ULift (Fin 1) ≃ ULift (Fin (c + 1))`, `inl a ↦ a + 1`,
`inr _ ↦ 0`, putting the extra coordinate first. -/
def uliftFinSumFinOneEquiv (c : ℕ) :
    ULift.{u} (Fin c) ⊕ ULift.{u} (Fin 1) ≃ ULift.{u} (Fin (c + 1)) where
  toFun := Sum.elim (fun a ↦ ULift.up a.down.succ) fun _ ↦ ULift.up 0
  invFun a := Fin.cases (Sum.inr (ULift.up 0)) (fun b ↦ Sum.inl (ULift.up b)) a.down
  left_inv := by
    rintro (⟨a⟩ | ⟨a⟩)
    · simp
    · obtain rfl : a = 0 := Subsingleton.elim _ _
      rfl
  right_inv := by
    rintro ⟨a⟩
    cases a using Fin.cases <;> rfl

/-- `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`, under which the coordinate of the affine line is the *first*
coordinate `t₀` of `𝔸^{c+1}_B` and the coordinate `t_a` of `𝔸^c_B` is `t_{a+1}`
(`AlgebraicGeometry.Etale.affineSpaceConsIso_hom_appTop_coord_zero`,
`AlgebraicGeometry.Etale.affineSpaceConsIso_hom_appTop_coord_succ`). -/
noncomputable def affineSpaceConsIso (c : ℕ) (B : Scheme.{u}) :
    𝔸(ULift.{u} (Fin (c + 1)); B) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) :=
  AffineSpace.reindexIso B (uliftFinSumFinOneEquiv c) ≪≫ AffineSpace.sumIso B

/-- Under `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`, the coordinate of the affine line is `t₀`. -/
lemma affineSpaceConsIso_hom_appTop_coord_zero (c : ℕ) (B : Scheme.{u}) :
    (affineSpaceConsIso c B).hom.appTop
        (AffineSpace.coord 𝔸(ULift.{u} (Fin c); B) (ULift.up 0)) =
      AffineSpace.coord B (ULift.up 0) := by
  simp only [affineSpaceConsIso, Iso.trans_hom, AffineSpace.reindexIso_hom,
    AffineSpace.sumIso_hom, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.sumHom,
    AffineSpace.homOfVector_appTop_coord, Function.comp_apply, AffineSpace.reindex_appTop_coord]
  rfl

/-- Under `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`, the pullback of the coordinate `t_a` of `𝔸^c_B` is
`t_{a+1}`. -/
lemma affineSpaceConsIso_hom_appTop_coord_succ (c : ℕ) (B : Scheme.{u}) (a : Fin c) :
    (affineSpaceConsIso c B).hom.appTop
        ((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘ 𝔸(ULift.{u} (Fin c); B)).appTop
          (AffineSpace.coord B (ULift.up a))) =
      AffineSpace.coord B (ULift.up a.succ) := by
  have h : (AffineSpace.sumHom B).appTop
      ((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘ 𝔸(ULift.{u} (Fin c); B)).appTop
        (AffineSpace.coord B (ULift.up a))) = AffineSpace.coord B (Sum.inl (ULift.up a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.sumHom_over,
      AffineSpace.homOfVector_appTop_coord]
    rfl
  rw [affineSpaceConsIso, Iso.trans_hom, AffineSpace.reindexIso_hom, AffineSpace.sumIso_hom,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h, AffineSpace.reindex_appTop_coord]
  rfl

/-! ### Adjoints of classes with supports -/

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- If a class with supports `γ : Λ_X ⟶ Ri_! Ri^! L` is itself an isomorphism, so is its
adjoint `Λ_Z ⟶ Ri^! L`: `Ri_!` of the adjoint is an isomorphism, as `γ` factors through it via
the restriction map `Λ_X ⟶ Ri_! Λ_Z`, a reflection into the objects `Ri_! N`. -/
lemma isIso_supportedClassMap_of_isIso {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) [IsIso γ] :
    IsIso (supportedClassMap Λ i γ) := by
  set a := (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ)
  have hγ : supportedRestrictionMap Λ i ≫ a = γ :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
  have hab : a ≫ inv γ ≫ supportedRestrictionMap Λ i = 𝟙 _ :=
    (bijective_supportedRestrictionMap_comp Λ i _).1 (by
      dsimp only
      rw [reassoc_of% hγ, IsIso.hom_inv_id_assoc, Category.comp_id])
  have hba : (inv γ ≫ supportedRestrictionMap Λ i) ≫ a = 𝟙 _ := by
    rw [Category.assoc, hγ, IsIso.inv_hom_id]
  have : IsIso a := ⟨_, hab, hba⟩
  exact isIso_of_reflects_iso _ (R(i)_![ModuleCat.{u + 1} Λ])

/-- If the adjoint of a class with supports `γ` is an isomorphism, so is the adjoint of `γ`
followed by an isomorphism `f` of the coefficients: the adjoint is natural in the
coefficients. -/
lemma isIso_supportedClassMap_comp_map {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) (f : L ⟶ L')
    [IsIso f] (hγ : IsIso (supportedClassMap Λ i γ)) :
    IsIso (supportedClassMap Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
      ((R(i)^![Λ]).map f))) := by
  have : supportedClassMap Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
      ((R(i)^![Λ]).map f)) =
      supportedClassMap Λ i γ ≫ (R(i)^![Λ]).map f :=
    supportedTranspose_comp Λ i γ _
  rw [this]
  infer_instance

/-- The lift of an isomorphism through the counit of `Ri_! ⊣ Ri^!` along a surjective closed
immersion `i` (`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`) is an isomorphism: the counit
is one, the open complement of `i` being empty. -/
lemma isIso_liftCounitOfRangeEqUniv {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L)
    [IsIso φ] : IsIso (liftCounitOfRangeEqUniv Λ i hi φ) := by
  have : IsEmpty i.openComplement.toScheme := ⟨fun x ↦ x.2 (hi ▸ Set.mem_univ _)⟩
  have := isIso_counit_app_of_isZero Λ i L (isZero_derivedCategory_of_isEmpty _ _ _)
  have hγ : liftCounitOfRangeEqUniv Λ i hi φ ≫
      (rightDerivedUpperShriekAdjunction Λ i).counit.app L = φ :=
    (existsUnique_comp_counit_of_range_eq_univ Λ i hi φ).exists.choose_spec
  have : IsIso (liftCounitOfRangeEqUniv Λ i hi φ ≫
      (rightDerivedUpperShriekAdjunction Λ i).counit.app L) := by
    rw [hγ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)

/-- `eqToHom` between objects `Ri_! Ri^! L` and `Ri_! Ri^! L'` with `L = L'` is
`Ri_! Ri^!` of `eqToHom`. -/
lemma eqToHom_eq_map_map {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (e : L = L') :
    (eqToHom (by rw [e]) : (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj L) ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj L')) =
      (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map (eqToHom e)) := by
  subst e
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]

/-! ### The Thom class -/

section Kummer

variable [HasKummerClass Λ]

/-- **Transport of the Thom class property along étale maps.** Let `e : U' ⟶ U` be étale and let
`f'_a = e^* f_a`. If the adjoint of `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` is an isomorphism, so is the adjoint
of `∂κ(f'₁) ∪ ⋯ ∪ ∂κ(f'_n)`: the latter is the restriction of the former
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`), and the restriction of
supports along an étale map is an isomorphism. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_of_etale {U U' : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U'] (e : U' ⟶ U)
    [AlgebraicGeometry.Etale e] {n : ℕ} (f : Fin n → Γ(U, ⊤)) (f' : Fin n → Γ(U', ⊤))
    (hf : ∀ a, e.appTop (f a) = f' a)
    (h : IsIso (supportedClassMap Λ (U.zeroLocusSubschemeι (Set.range f))
      (kummerBoundaryProduct Λ f))) :
    IsIso (supportedClassMap Λ (U'.zeroLocusSubschemeι (Set.range f'))
      (kummerBoundaryProduct Λ f')) := by
  have hs : e.appTop '' Set.range f = Set.range f' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hf)
  have hg := isPullback_zeroLocusSubschemeι e (Set.range f) (Set.range f') hs
  rw [← restrictSupportedClass_kummerBoundaryProduct Λ e f f' hf _ hg,
    isIso_supportedClassMap_restrictSupportedClass_iff Λ e _ _ _ hg _ _ _ _
      (isIso_supportedRestriction_of_etale Λ e _ _ _ hg _ _ _)]
  infer_instance

/-- **The empty product of Kummer boundaries** is the Thom class of `U ⊆ U`: its adjoint
`Λ_U ⟶ Ri^! Λ_U(0)[0]` is an isomorphism. The class itself is an isomorphism, being the lift of
the isomorphism `Λ_U ≅ Λ_U(0)[0]` through the counit of `Ri_! ⊣ Ri^!` along the surjective
closed immersion `i : V(∅) ⟶ U`. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_zero (U : Scheme.{u})
    [HasInvertibleExponent Λ U] (f : Fin 0 → Γ(U, ⊤)) :
    IsIso (supportedClassMap Λ (U.zeroLocusSubschemeι (Set.range f))
      (kummerBoundaryProduct Λ f)) := by
  have : IsIso (kummerBoundaryProduct Λ f) := by
    rw [kummerBoundaryProduct]
    exact isIso_liftCounitOfRangeEqUniv Λ _ _ _
  exact isIso_supportedClassMap_of_isIso Λ _ _

variable [HasKummerClass.IsNormalized Λ]

/-- **The induction step for the Thom class.** Let `B'` be separated and locally of finite type
over a field, `X = 𝔸¹_{B'}` with coordinate `t` and projection `p`, and `g₁, …, g_c` functions
on `B'` such that the adjoint of `∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_c)` is an isomorphism. Then the adjoint of
`∂κ(t) ∪ ∂κ(p^* g₁) ∪ ⋯ ∪ ∂κ(p^* g_c)` on `X` is an isomorphism.

This is the cup product criterion
`AlgebraicGeometry.Etale.isIso_supportedClassMap_cupWithSupports`: the adjoint of `∂κ(t)` is an
isomorphism by the rank-one normalisation, and the restriction of
`∂κ(p^* g₁) ∪ ⋯ ∪ ∂κ(p^* g_c)` to `V(t) ≅ B'` is `∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_c)`. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_cons_coord {k : Type u} [Field k]
    (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of k)) [IsSeparated aB'] [LocallyOfFiniteType aB']
    [HasInvertibleExponent Λ B'] {c : ℕ} (g₀ : Fin c → Γ(B', ⊤))
    (h : IsIso (supportedClassMap Λ (B'.zeroLocusSubschemeι (Set.range g₀))
      (kummerBoundaryProduct Λ g₀))) :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B').zeroLocusSubschemeι
        (Set.range (Fin.cons (AffineSpace.coord B' (ULift.up 0))
          fun a ↦ (𝔸(ULift.{u} (Fin 1); B') ↘ B').appTop (g₀ a) :
            Fin (c + 1) → Γ(𝔸(ULift.{u} (Fin 1); B'), ⊤))))
      (kummerBoundaryProduct Λ (Fin.cons (AffineSpace.coord B' (ULift.up 0))
          fun a ↦ (𝔸(ULift.{u} (Fin 1); B') ↘ B').appTop (g₀ a) :
            Fin (c + 1) → Γ(𝔸(ULift.{u} (Fin 1); B'), ⊤)))) := by
  set X := 𝔸(ULift.{u} (Fin 1); B')
  set p := 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  set t := AffineSpace.coord B' (ULift.up (0 : Fin 1))
  set g : Fin c → Γ(X, ⊤) := fun a ↦ p.appTop (g₀ a)
  have : HasInvertibleExponent Λ X := .of_hom p
  set i₁ := X.zeroLocusSubschemeι {t}
  have : HasInvertibleExponent Λ (X.zeroLocusSubscheme {t}) := .of_hom i₁
  have hs : i₁.appTop '' Set.range g = Set.range (fun a ↦ i₁.appTop (g a)) := by
    rw [← Set.range_comp]
    rfl
  have hg := isPullback_zeroLocusSubschemeι i₁ (Set.range g) _ hs
  -- the restriction of `∂κ(p^* g₁) ∪ ⋯ ∪ ∂κ(p^* g_c)` to `V(t) ≅ B'` is `∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_c)`
  have hβ : IsIso (supportedClassMap Λ _ (restrictSupportedClass Λ i₁ _ _ _
      hg (leftDerivedUpperStarConstantComplexIso Λ i₁).inv
      (leftDerivedUpperStarTateShiftIso Λ i₁ c) (kummerBoundaryProduct Λ g))) := by
    rw [restrictSupportedClass_kummerBoundaryProduct Λ i₁ g _ (fun _ ↦ rfl) _ hg]
    have : IsIso (i₁ ≫ p) :=
      (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B' (s := {t})
        Set.range_unique).isIso_inv
    exact isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (i₁ ≫ p) g₀ _
      (fun a ↦ by rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]) h
  have hα := HasKummerClass.IsNormalized.isIso_supportedClassMap_kummerBoundary_coord
    (Λ := Λ) B' aB'
  have hcup := isIso_supportedClassMap_cupWithSupports i₁ _
    (X.zeroLocusSubschemeι (Set.range (Fin.cons t g : Fin (c + 1) → Γ(X, ⊤)))) _ _ hg
    (by rw [Fin.range_cons, range_zeroLocusSubschemeι_insert])
    (DerivedCategory.isInvertible.shift (isInvertible_tateObject Λ X c) _) _ _
    (constantComplexDiagonal Λ X) (constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom Λ X)
    _ _ hα hβ
  rw [kummerBoundaryProduct_cons, cupWithSupportsTateObject, Category.assoc,
    eqToHom_eq_map_map Λ _ (show (tateObject Λ X (1 + c))⟦2 * (1 + (c : ℤ))⟧ =
      (tateObject Λ X ((c + 1 : ℕ) : ℤ))⟦2 * ((c + 1 : ℕ) : ℤ)⟧ by
        rw [Nat.cast_succ, add_comm (1 : ℤ)]),
    ← Functor.map_comp, ← Functor.map_comp]
  exact isIso_supportedClassMap_comp_map Λ _ _ _ hcup

/-- Blueprint `proposition-purity-vector-bundles`: `𝔸¹ ⇒ 𝔸ⁿ`: the model purity, clause (i), over a
field.

For `B` separated and locally of finite type over a field, on which the exponent of `Λ` is
invertible, and the zero section `z : B ↪ 𝔸^c_B`, cut out by the coordinates `t₁, …, t_c`, the
adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])` of `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)`
(`AlgebraicGeometry.Etale.supportedClassMap`) is an isomorphism.

By induction on `c`, writing `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`
(`AlgebraicGeometry.Etale.affineSpaceConsIso`) with the first coordinate as the coordinate of
the affine line; the step is
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_cons_coord`. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field (c : ℕ) {k : Type u}
    [Field k] (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin c); B).zeroLocusSubschemeι
        (Set.range fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)))
      (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord B (ULift.up a))) := by
  induction c with
  | zero => exact isIso_supportedClassMap_kummerBoundaryProduct_zero Λ _ _
  | succ c ih =>
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B) :=
      .of_hom (𝔸(ULift.{u} (Fin c); B) ↘ B)
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) :=
      .of_hom (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘ 𝔸(ULift.{u} (Fin c); B))
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin (c + 1)); B) :=
      .of_hom (𝔸(ULift.{u} (Fin (c + 1)); B) ↘ B)
    refine isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (affineSpaceConsIso c B).hom
      _ _ (fun a ↦ ?_) (isIso_supportedClassMap_kummerBoundaryProduct_cons_coord Λ
        𝔸(ULift.{u} (Fin c); B) (𝔸(ULift.{u} (Fin c); B) ↘ B ≫ aB)
        (fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)) ih)
    cases a using Fin.cases with
    | zero => rw [Fin.cons_zero, affineSpaceConsIso_hom_appTop_coord_zero]
    | succ a => rw [Fin.cons_succ, affineSpaceConsIso_hom_appTop_coord_succ]

end Kummer

end Etale

end AlgebraicGeometry
