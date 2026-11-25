/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts
import WeilConjectures.AlgebraicGeometry.Morphisms.TameRootProductResidueSeparable
import Mathlib.FieldTheory.SeparableDegree

/-!
# Local algebra of tame trait normalization

## References

* Stacks Project, Tag 0EYH, the tame charts used in the trait paragraph of 0EYJ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private abbrev ResidueSeparableAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem residueSeparableAt_comp {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
    (hf : ResidueSeparableAt f x) (hg : ResidueSeparableAt g (f x)) :
    ResidueSeparableAt (f ≫ g) x := by
  dsimp only [ResidueSeparableAt]
  rw [residueFieldMap_comp]
  let := (f.residueFieldMap x).hom.toAlgebra
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  have : IsScalarTower (T.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) :=
    .of_algebraMap_eq' rfl
  have : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := hf
  have : Algebra.IsSeparable (T.residueField (g (f x))) (Y.residueField (f x)) := hg
  exact Algebra.IsSeparable.trans (T.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem residueSeparableAt_of_comp {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
    (h : ResidueSeparableAt (f ≫ g) x) : ResidueSeparableAt g (f x) := by
  dsimp only [ResidueSeparableAt] at h
  rw [residueFieldMap_comp] at h
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  let φ : Y.residueField (f x) →ₐ[T.residueField (g (f x))] X.residueField x :=
    { toRingHom := (f.residueFieldMap x).hom
      commutes' := fun _ ↦ rfl }
  have : Algebra.IsSeparable (T.residueField (g (f x))) (X.residueField x) := by
    exact h
  exact Algebra.IsSeparable.of_algHom (T.residueField (g (f x))) _ φ

private theorem residueSeparableAt_etale {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Etale f] (x : X) : ResidueSeparableAt f x := by
  dsimp only [ResidueSeparableAt]
  infer_instance

private theorem residueSeparableAt_of_etale_baseChange {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) [Etale g] (x : X) (y : T) (hxy : f x = g y)
    (h : ∀ z : ↥(pullback f g), ResidueSeparableAt (pullback.snd f g) z) :
    ResidueSeparableAt f x := by
  obtain ⟨z, rfl, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  apply residueSeparableAt_of_comp (pullback.fst f g) f z
  rw [pullback.condition]
  exact residueSeparableAt_comp (pullback.snd f g) g z (h z)
    (residueSeparableAt_etale g _)

private theorem residueSeparableAt_stalk {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (h : ResidueSeparableAt f x) :
    letI := (f.stalkMap x).hom.toAlgebra
    letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
    Algebra.IsSeparable (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  dsimp only [ResidueSeparableAt] at h
  convert! h using 1
  exact Algebra.algebra_ext _ _ fun z ↦ by
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
    rfl

private theorem residueSeparableAt_of_root_charts {X Y : Scheme.{u}} (n : X ⟶ Y)
    (I : Type u) (R : I → CommRingCat.{u}) (φ : ∀ i, Spec (R i) ⟶ Y)
    (hφ : ∀ i, Etale (φ i))
    (hcover : ∀ y : Y, ∃ (i : I) (z : Spec (R i)), φ i z = y)
    (hcharts : ∀ i, ∃ (m : ℕ) (f : R i) (e : Fin m → ℕ),
      (∀ k, 0 < e k ∧ IsUnit (e k : R i)) ∧
      ∃ α : pullback n (φ i) ≅
        Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial (R i)) ^ e k - Polynomial.C f))),
        α.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (R i) (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial (R i)) ^ e k - Polynomial.C f)))) =
          pullback.snd n (φ i)) (x : X) : ResidueSeparableAt n x := by
  obtain ⟨i, y, hy⟩ := hcover (n x)
  let := hφ i
  apply residueSeparableAt_of_etale_baseChange n (φ i) x y hy.symm
  intro z
  obtain ⟨m, f, e, he, α, hα⟩ := hcharts i
  let D := CommRingCat.of (∀ k : Fin m,
    AdjoinRoot ((Polynomial.X : Polynomial (R i)) ^ e k - Polynomial.C f))
  let π : Spec D ⟶ Spec (R i) :=
    Spec.map (CommRingCat.ofHom (algebraMap (R i) D))
  have hroot : ResidueSeparableAt π (α.hom z) :=
    tameRootProduct_residue_separable (R i) m f e he (α.hom z)
  have hcomp := residueSeparableAt_comp α.hom π z
    (residueSeparableAt_etale α.hom z) hroot
  change α.hom ≫ π = pullback.snd n (φ i) at hα
  rw [hα] at hcomp
  exact hcomp

/-- Residue extensions at points above the closed trait section are separable. -/
theorem GaloisCover.stalk_normalization_trait_section_residue_separable {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      letI := (n.stalkMap x).hom.toAlgebra
      letI : IsLocalHom
          (algebraMap ((pullback c a).presheaf.stalk (n x))
            ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
              (pullback.fst c a)).presheaf.stalk x)) :=
        inferInstanceAs <| IsLocalHom (n.stalkMap x).hom
      Algebra.IsSeparable
        (IsLocalRing.ResidueField ((pullback c a).presheaf.stalk (n x)))
        (IsLocalRing.ResidueField
          ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
            (pullback.fst c a)).presheaf.stalk x)) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro a n τ hn x _hx
  apply residueSeparableAt_stalk n x
  obtain ⟨I, R, φ, hφ, hcover, hcharts⟩ :=
    GaloisCover.stalk_normalization_trait_charts
      c G hG q j hCη Z U jU PA ψ hjU hψ s hs hmin hdvr hn
  exact residueSeparableAt_of_root_charts n I R φ hφ hcover hcharts x

end AlgebraicGeometry.Scheme
