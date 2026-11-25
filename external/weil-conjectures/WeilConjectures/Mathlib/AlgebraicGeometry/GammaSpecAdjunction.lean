/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The canonical morphism from a basic open to the spectrum of a localization

We record that the canonical morphism `X.basicOpen x ⟶ Spec Γ(X, ⊤)[1/x]`, obtained by
restricting `X.toSpecΓ` to the basic open `D(x)` of `Spec Γ(X, ⊤)`, is compatible with the
localization map `Γ(X, ⊤) ⟶ Γ(X, ⊤)[1/x]`.

A morphism `m : X ⟶ Spec R` whose image avoids the zero loci of the elements of a submonoid `M`
of `R` factors through `Spec R_M ⟶ Spec R`
(`AlgebraicGeometry.exists_comp_SpecMap_algebraMap_localization`).

For a commutative ring `R`, the presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` on schemes is represented by
`Spec R` (`AlgebraicGeometry.ΓSpec.representableBy`).

`AlgebraicGeometry.Scheme.specMap_appTop_ΓSpecIso_inv_mul` computes the product of two global
sections of `Spec T` pulled back from `Spec R` and `Spec S` along ring maps into `T`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical morphism `X.basicOpen x ⟶ Spec Γ(X, ⊤)[1/x]`, composed with `Spec` of the
localization map, is the composite `X.basicOpen x ⟶ X ⟶ Spec Γ(X, ⊤)`. -/
@[reassoc]
lemma resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap (X : Scheme.{u}) (x : Γ(X, ⊤)) :
    X.toSpecΓ.resLE (PrimeSpectrum.basicOpen x) (X.basicOpen x)
        (X.toSpecΓ_preimage_basicOpen x).ge ≫ (basicOpenIsoSpecAway x).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  rw [basicOpenIsoSpecAway_hom_SpecMap, Scheme.Hom.resLE_comp_ι]

/-- **The Stein factorization** of a morphism `p : Y ⟶ Spec R`: with `B = Γ(Y, 𝒪_Y)`, an
`R`-algebra through `p`, the morphism `p` factors as
`Y ⟶ Spec B ⟶ Spec R`, the first map being the canonical morphism `Y.toSpecΓ` and the second
the morphism `Spec B ⟶ Spec R` of the algebra structure
(`AlgebraicGeometry.Scheme.toSpecΓ_steinFactorizationBase`). For a proper `p` this is the Stein
factorization [Stacks 03GX].
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
noncomputable def Scheme.Hom.steinFactorizationBase {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (p : Y ⟶ Spec R) : Spec Γ(Y, ⊤) ⟶ Spec R :=
  Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop)

/-- The Stein factorization `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec R` of `p : Y ⟶ Spec R` composes to
`p`. -/
@[reassoc (attr := simp)]
lemma Scheme.toSpecΓ_steinFactorizationBase {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (p : Y ⟶ Spec R) : Y.toSpecΓ ≫ p.steinFactorizationBase = p := by
  rw [Scheme.Hom.steinFactorizationBase, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-- A morphism `m : X ⟶ Spec R` whose image avoids the zero loci of the elements of a submonoid
`M` of `R` factors through `Spec R_M ⟶ Spec R`: the elements of `M` become units in
`Γ(X, 𝒪_X)`. -/
lemma exists_comp_SpecMap_algebraMap_localization {X : Scheme.{u}} {R : CommRingCat.{u}}
    (m : X ⟶ Spec R) (M : Submonoid R)
    (hM : ∀ r ∈ M, ∀ x : X, m x ∈ PrimeSpectrum.basicOpen r) :
    ∃ m' : X ⟶ Spec (CommRingCat.of (Localization M)),
      m' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) = m := by
  have hψ (r : M) : IsUnit (((Scheme.ΓSpecIso R).inv ≫ m.appTop).hom r) := by
    refine Scheme.isUnit_of_basicOpen_eq_top _ (top_unique fun x _ ↦ ?_)
    change x ∈ X.basicOpen (m.appTop ((Scheme.ΓSpecIso R).inv r))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact hM r r.2 x
  refine ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := M)
    (S := Localization M) hψ)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]
  exact Scheme.toSpecΓ_steinFactorizationBase m

/-- On global sections, a morphism of affine schemes `f : Spec S ⟶ Spec R` is the ring
homomorphism `R ⟶ S` it comes from, through `Γ(Spec R, ⊤) ≅ R`. -/
theorem Scheme.Hom.appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : Spec S ⟶ Spec R) (c : R) :
    f.appTop ((Scheme.ΓSpecIso R).inv c) = (Scheme.ΓSpecIso S).inv ((Spec.preimage f).hom c) := by
  have h := congr(($(Scheme.ΓSpecIso_inv_naturality (Spec.preimage f))).hom c)
  rw [Spec.map_preimage] at h
  exact h.symm

/-- For a commutative ring `R`, the presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` on schemes is represented
by `Spec R`: this is the adjunction `Γ ⊣ Spec`. -/
noncomputable def ΓSpec.representableBy (R : CommRingCat.{u}) :
    (Scheme.Γ ⋙ coyoneda.obj (op R)).RepresentableBy (Spec R) where
  homEquiv {U} := (ΓSpec.adjunction.homEquiv U (op R)).symm.trans (opEquiv _ _)
  homEquiv_comp f g :=
    congrArg Quiver.Hom.unop (ΓSpec.adjunction.homEquiv_naturality_left_symm (Y := op R) f g)

/-- The product of two sections of `Spec T` pulled back from `Spec R` and `Spec S` along ring maps
`φ : R ⟶ T` and `ψ : S ⟶ T` is the section given by `φ x * ψ y`. -/
lemma Scheme.specMap_appTop_ΓSpecIso_inv_mul {R S T : CommRingCat.{u}} (φ : R ⟶ T) (ψ : S ⟶ T)
    (x : R) (y : S) :
    (Spec.map φ).appTop ((ΓSpecIso R).inv x) * (Spec.map ψ).appTop ((ΓSpecIso S).inv y) =
      (ΓSpecIso T).inv (φ x * ψ y) := by
  rw [specMap_appTop_ΓSpecIso_inv, specMap_appTop_ΓSpecIso_inv, ΓSpecIso_inv_mul]

/-- If `φ x * ψ y = ψ z` for ring maps `φ : R ⟶ T` and `ψ : S ⟶ T`, the same identity holds for
the corresponding sections of `Spec T` pulled back along `Spec.map φ` and `Spec.map ψ`. -/
lemma Scheme.specMap_appTop_ΓSpecIso_inv_mul_eq {R S T : CommRingCat.{u}} (φ : R ⟶ T)
    (ψ : S ⟶ T) (x : R) (y z : S) (h : φ x * ψ y = ψ z) :
    (Spec.map φ).appTop ((ΓSpecIso R).inv x) * (Spec.map ψ).appTop ((ΓSpecIso S).inv y) =
      (Spec.map ψ).appTop ((ΓSpecIso S).inv z) := by
  rw [specMap_appTop_ΓSpecIso_inv_mul, h, specMap_appTop_ΓSpecIso_inv]

end AlgebraicGeometry
