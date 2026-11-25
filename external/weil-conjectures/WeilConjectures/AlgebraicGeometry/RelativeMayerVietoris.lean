/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.RelativeMVCanonicalTriangles

/-! # Relative Mayer--Vietoris gluing for one complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.26.2 (Tag 0DJ9)
(blueprint: lem-pc-rf-single-complex-relative-mayer-vietoris).
-/

@[expose] public section

universe um wm

open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false

namespace AlgebraicGeometry

private theorem isIso_biprod_map
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {A B A' B' : C} {a : A ⟶ A'} {b : B ⟶ B'}
    (ha : IsIso a) (hb : IsIso b) : IsIso (biprod.map a b) := by
  let := ha
  let := hb
  change IsIso (biprod.mapIso (asIso a) (asIso b)).hom
  infer_instance

private theorem isIso_of_eq
    {C : Type*} [Category C] {A B : C} {a b : A ⟶ B}
    (h : a = b) (hb : IsIso b) : IsIso a := h.symm ▸ hb

/-- Relative Mayer--Vietoris gluing for the single-complex base-change map.
Source: Stacks Project, Tag 0DJ9, induction step
(blueprint: lem-pc-rf-single-complex-relative-mayer-vietoris).

Proof:
1. Since the bases are affine and `f` is quasi-compact and quasi-separated, `X`
   is qcqs. The affine morphism `g` has affine base change `g'`, so the inverse
   images of the three quasi-compact opens are quasi-compact. Apply
   `lem-pc-derived-mayer-vietoris-triangle` to `K` and `K'`, then apply the
   exact functors `Lg^*Rf_*` and `Rf'_*`. The composition identifications of
   `lem-pc-derived-direct-image-composition` identify their open terms.
2. `lem-pc-rf-mv-triangle-naturality` identifies the three comparison maps
   as a morphism of these distinguished triangles on `S'`.
3. The two individual isomorphisms on `U` and `V` give an isomorphism on
   their direct sum. The overlap map is also invertible by hypothesis.
   Apply `lem-sf-triangle-morphism-iso` to infer that the global map is invertible.
4. The global component is precisely the canonical base-change map followed
   by `Rf'_*` of `φ`, the composite asserted here. -/
theorem relativeMayerVietoris
    [∀ Z : Scheme.{um},
      HasDerivedCategory.{wm} (SheafOfModules.{um} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{um}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X)
    (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hU : IsIso (schemeDerivedBaseChangeMap (U.ι ≫ f)
      (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback U.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' U.ι ≫ f')).map
        (((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' U.ι) U.ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := U.ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' U.ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' U.ι)).map φ)))
    (hV : IsIso (schemeDerivedBaseChangeMap (V.ι ≫ f)
      (pullback.fst g' V.ι ≫ f') g (pullback.snd g' V.ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback V.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' V.ι ≫ f')).map
        (((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' V.ι) V.ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := V.ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' V.ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' V.ι)).map φ)))
    (hUV : IsIso (schemeDerivedBaseChangeMap ((U ⊓ V).ι ≫ f)
      (pullback.fst g' (U ⊓ V).ι ≫ f') g (pullback.snd g' (U ⊓ V).ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback (U ⊓ V).ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' (U ⊓ V).ι ≫ f')).map
        (((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' (U ⊓ V).ι) (U ⊓ V).ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := (U ⊓ V).ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' (U ⊓ V).ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' (U ⊓ V).ι)).map φ))) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' hpull.w K ≫
      (schemeDerivedDirectImage f').map φ) := by
  classical
  obtain ⟨d₁, d₂, d₃, d₁', d₂', d₃', hT, hT', t, ht₁, ht₂, ht₃⟩ :=
    relativeMV_canonicalTriangles f f' g g' hpull K K' φ
      U V hcover
  have h₂ := isIso_of_eq ht₂ (isIso_biprod_map hU hV)
  have h₃ := isIso_of_eq ht₃ hUV
  exact isIso_of_eq ht₁.symm (Pretriangulated.isIso₁_of_isIso₂₃ t hT hT' h₂ h₃)

end AlgebraicGeometry
