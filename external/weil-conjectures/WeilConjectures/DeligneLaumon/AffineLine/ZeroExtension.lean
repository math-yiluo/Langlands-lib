/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights

/-!
# Comparing the transform of the zero extension with the transform of the middle extension

Rotating the triangle of `0 → j_!M → j_*M → B → 0`, where `B = j_*M / j_!M` is the punctual
boundary sheaf, gives a short exact sequence of curve perverse sheaves
`B → j_!M[1] → j_*M[1]`. Fourier exactness on the perverse heart turns it into a short exact
sequence of perverse sheaves on the dual line. Each punctual summand of `B` transforms into a
lisse Artin–Schreier kernel shifted by one, and the middle extension transforms into
`(j'_*M')[1]`, so the whole sequence is concentrated in one ordinary degree:

`0 → B' → G → j'_*M' → 0`, with `FT_ψ(j_!M[1]) ≃ G[1]` and `FT_ψ(B) ≃ B'[1]`.

The correction term `B'` is lisse on the entire dual line and, by semicontinuity of weights
at the boundary points together with the weight zero of the Artin–Schreier kernel, has weights
at most `w`.

The datum of that sequence together with the two comparison isomorphisms is bundled as
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`, so that the correction sheaf
`B'` and its rank can be named in the weight estimate of
`WeilConjectures.DeligneLaumon.AffineLine.FourierWeight`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.shortExact_boundaryShortComplex` and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.boundaryTriangle_distinguished`: the sequence
  `0 → j_!M → j_*M → B → 0` is short exact, and its rotated triangle
  `B → j_!M[1] → j_*M[1] → B[1]` is distinguished, as is its Fourier transform
  (`…LisseOnDenseOpen.fourierTransform_mapTriangle_boundaryTriangle_distinguished`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`: the exact sequence, the
  comparison isomorphisms with the transforms, and the square identifying its epimorphism with
  the transform of `j_!M[1] → j_*M[1]`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection`: it exists.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.isLisse` and
  `…FourierCorrection.hasWeightsAtMost`: the correction sheaf is lisse of weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

section Boundary

variable (D : LisseOnDenseOpen k₀ l)

/-- The sequence `0 → j_!M → j_*M → B → 0` of Weil sheaves on the affine line, `B` being the
boundary sheaf. -/
noncomputable def boundaryShortComplex : ShortComplex (WeilSheaf k₀ l (affineLine k₀)) :=
  ShortComplex.mk ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf) (cokernel.π _)
    (cokernel.condition _)

/-- The sequence `0 → j_!M → j_*M → B → 0` is short exact: `j_!M → j_*M` is a monomorphism
(`AlgebraicGeometry.WeilSheaf.mono_extensionByZeroToDirectImage_app`) and `B` is its cokernel.
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
lemma shortExact_boundaryShortComplex : D.boundaryShortComplex.ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (WeilSheaf.mono_extensionByZeroToDirectImage_app D.j D.sheaf)
    (inferInstanceAs (Epi (cokernel.π _)))

/-- The rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` of the sequence
`0 → j_!M → j_*M → B → 0`, whose middle arrow is `-(j_!M[1] → j_*M[1])`. -/
noncomputable def boundaryTriangle : Triangle (WeilComplex k₀ l (affineLine k₀)) :=
  (WeilSheaf.singleTriangle D.shortExact_boundaryShortComplex).rotate.rotate

lemma boundaryTriangle_mor₂ :
    D.boundaryTriangle.mor₂ = -D.shiftedExtensionByZeroToMiddleExtension :=
  rfl

/-- The rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` is distinguished.
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
lemma boundaryTriangle_distinguished : D.boundaryTriangle ∈ distTriang _ :=
  rot_of_distTriang _ (rot_of_distTriang _
    (WeilSheaf.singleTriangle_distinguished D.shortExact_boundaryShortComplex))

/-- The Fourier transform of the rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` is
distinguished, the transform being a triangulated functor. (blueprint:
`lemma-fourier-transform-boundary-sequence`) -/
lemma fourierTransform_mapTriangle_boundaryTriangle_distinguished :
    (fourierTransform ψ).mapTriangle.obj D.boundaryTriangle ∈ distTriang _ :=
  (fourierTransform ψ).map_distinguished _ D.boundaryTriangle_distinguished

end Boundary

/--
The zero-extension comparison datum for `D` and a Fourier partner `D'`: a short exact sequence
`0 → B' → G → j'_*M' → 0` of Weil sheaves on the dual line together with the isomorphisms
that identify `G[1]` with `FT_ψ(j_!M[1])`, `B'[1]` with `FT_ψ(B)` and `(j'_*M')[1]` with
`FT_ψ(j_*M[1])`, where `B = j_*M / j_!M` is the boundary sheaf of `D`, such that the epimorphism
`G → j'_*M'` is the transform of `j_!M[1] → j_*M[1]`:

```
  FT_ψ(B) ≃ B'[1]

  FT_ψ(j_!M[1]) ──FT_ψ(can[1])──▶ FT_ψ(j_*M[1])
        │ ≃                             │ ≃
        ▼                               ▼
      G[1] ────────────g[1]──────────▶ X₃[1]

  0 ──▶ B' ──▶ G ──g──▶ X₃ ≃ j'_*M' ──▶ 0
```

The square pins the sequence down: a short exact sequence is determined up to isomorphism by its
epimorphism, `B'` being its kernel, so the sequence is the one obtained from the transform of the
rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` and not, say, a split one. The square is stated
for the middle arrow of the rotated triangle only: the first arrow `B → j_!M[1]` is the connecting
morphism of `0 → j_!M → j_*M → B → 0`, whose formation needs `j_!M → j_*M` to be a
monomorphism, and comparing whole triangles needs a shift-compatibility of the transform; the
square already determines the sequence. (blueprint: `lemma-fourier-transform-boundary-sequence`)
-/
structure FourierCorrection (D D' : LisseOnDenseOpen k₀ l) where
  /-- The short exact sequence `0 → B' → G → j'_*M' → 0` on the dual line. -/
  seq : ShortComplex (WeilSheaf k₀ l (affineLine k₀))
  /-- The sequence is short exact. -/
  shortExact : seq.ShortExact
  /-- Its third term is the middle extension of the Fourier partner. -/
  isoDirectImage : seq.X₃ ≅ D'.directImage
  /-- The transform of the shifted zero extension is the shifted middle term. -/
  isoExtensionByZero : (fourierTransform ψ).obj D.shiftedExtensionByZero ≅
    (WeilSheaf.toComplex.obj seq.X₂)⟦(1 : ℤ)⟧
  /-- The transform of the boundary sheaf is the shifted first term. -/
  isoBoundary : (fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
    (WeilSheaf.toComplex.obj seq.X₁)⟦(1 : ℤ)⟧
  /-- The transform of the middle extension is the shifted third term. -/
  isoMiddleExtension : (fourierTransform ψ).obj D.middleExtension ≅
    (WeilSheaf.toComplex.obj seq.X₃)⟦(1 : ℤ)⟧
  /-- The epimorphism `G → j'_*M'` of the sequence is the transform of `j_!M[1] → j_*M[1]`. -/
  fourierTransform_map_comp_isoMiddleExtension_hom :
    (fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension ≫
        isoMiddleExtension.hom =
      isoExtensionByZero.hom ≫ (WeilSheaf.toComplex.map seq.g)⟦(1 : ℤ)⟧'

/-- **Steps 1–3 of `lemma-fourier-transform-boundary-sequence`.** The transform of the boundary
sheaf `B = j_*M / j_!M` is `B'[1]` for a Weil sheaf `B'` on the dual line which is lisse.
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
theorem exists_isLisse_iso_fourierTransform_boundarySheaf (D : LisseOnDenseOpen k₀ l) :
    ∃ B' : WeilSheaf k₀ l (affineLine k₀), B'.IsLisse ∧
      Nonempty ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
        WeilSheaf.toShiftedComplex.obj B') := by
  exact WeilSheaf.exists_isLisse_iso_fourierTransform_of_isZero_upperStar ψ D.j D.boundarySheaf
    D.isZero_upperStar_boundarySheaf

section Construction

variable {ψ} {D D' : LisseOnDenseOpen k₀ l} {B' : WeilSheaf k₀ l (affineLine k₀)}
  (eB : (fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
    WeilSheaf.toShiftedComplex.obj B')
  (eM : (fourierTransform ψ).obj D.middleExtension ≅ D'.middleExtension)

/-- The transform of the rotated boundary triangle `B → j_!M[1] → j_*M[1] → B[1]`. -/
noncomputable abbrev fourierTriangle (D : LisseOnDenseOpen k₀ l) :
    Triangle (WeilComplex k₀ l (affineLine k₀)) :=
  (fourierTransform ψ).mapTriangle.obj D.boundaryTriangle

lemma boundaryTriangle_obj₂ (D : LisseOnDenseOpen k₀ l) :
    D.boundaryTriangle.obj₂ = D.shiftedExtensionByZero :=
  rfl

lemma fourierTriangle_obj₂ (D : LisseOnDenseOpen k₀ l) :
    (fourierTriangle (ψ := ψ) D).obj₂ = (fourierTransform ψ).obj D.shiftedExtensionByZero :=
  rfl

lemma fourierTriangle_distinguished (D : LisseOnDenseOpen k₀ l) :
    fourierTriangle (ψ := ψ) D ∈ distTriang _ :=
  D.fourierTransform_mapTriangle_boundaryTriangle_distinguished ψ

lemma fourierTriangle_mor₂ (D : LisseOnDenseOpen k₀ l) :
    (fourierTriangle (ψ := ψ) D).mor₂ =
      -(fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension := by
  change (fourierTransform ψ).map D.boundaryTriangle.mor₂ = _
  rw [boundaryTriangle_mor₂, Functor.map_neg]

lemma fourierTriangle_mor₁_comp (D : LisseOnDenseOpen k₀ l) :
    (fourierTriangle (ψ := ψ) D).mor₁ ≫
      (fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension = 0 := by
  have h := comp_distTriang_mor_zero₁₂ _ (fourierTriangle_distinguished (ψ := ψ) D)
  rwa [fourierTriangle_mor₂, Preadditive.comp_neg, neg_eq_zero] at h

include eB eM in
/-- Step 5 of `lemma-fourier-transform-boundary-sequence`: the transform `K` of `j_!M[1]` has its
cohomology concentrated in degree `-1`, since the two outer terms of the triangle
`B'[1] → K → (j'_*M')[1] →` have. -/
lemma isZero_homologySheaf_fourierTransform_shiftedExtensionByZero {a : ℤ}
    (ha : a ≠ -1) :
    IsZero ((WeilComplex.homologySheaf a).obj
      ((fourierTransform ψ).obj D.shiftedExtensionByZero)) := by
  have h₁ : IsZero ((WeilComplex.homologySheaf a).obj (fourierTriangle (ψ := ψ) D).obj₁) :=
    (WeilSheaf.isZero_homologySheaf_toShiftedComplex ha B').of_iso
      ((WeilComplex.homologySheaf a).mapIso eB)
  have h₃ : IsZero ((WeilComplex.homologySheaf a).obj (fourierTriangle (ψ := ψ) D).obj₃) :=
    (WeilSheaf.isZero_homologySheaf_toShiftedComplex ha D'.directImage).of_iso
      ((WeilComplex.homologySheaf a).mapIso eM)
  have hex := WeilComplex.homologySheaf_exact₂ _ a (fourierTriangle_distinguished (ψ := ψ) D)
  have : Mono ((WeilComplex.homologySheaf a).map (fourierTriangle (ψ := ψ) D).mor₂) :=
    hex.mono_g (h₁.eq_of_src _ _)
  rw [h₃.eq_of_tgt ((WeilComplex.homologySheaf a).map (fourierTriangle (ψ := ψ) D).mor₂) 0]
    at this
  exact IsZero.of_mono_zero ((WeilComplex.homologySheaf a).obj (fourierTriangle (ψ := ψ) D).obj₂)
    ((WeilComplex.homologySheaf a).obj (fourierTriangle (ψ := ψ) D).obj₃)

/-- The isomorphism `FT_ψ(j_!M[1]) ≅ G[1]`, `G = 𝓗⁻¹ FT_ψ(j_!M[1])`, of Step 5 of
`lemma-fourier-transform-boundary-sequence`. -/
noncomputable def isoExtensionByZeroOfIso :
    (fourierTransform ψ).obj D.shiftedExtensionByZero ≅
      WeilSheaf.toShiftedComplex.obj ((WeilComplex.homologySheaf (-1)).obj
        ((fourierTransform ψ).obj D.shiftedExtensionByZero)) :=
  (WeilComplex.nonempty_iso_toShiftedComplex _ fun _ ha ↦
    isZero_homologySheaf_fourierTransform_shiftedExtensionByZero eB eM ha).some

/-- The first map `B' → G` of the sequence of Step 5. -/
noncomputable def correctionSeqF :
    B' ⟶ (WeilComplex.homologySheaf (-1)).obj
      ((fourierTransform ψ).obj D.shiftedExtensionByZero) :=
  WeilSheaf.toShiftedComplex.preimage
    (eB.inv ≫ (fourierTriangle (ψ := ψ) D).mor₁ ≫ (isoExtensionByZeroOfIso eB eM).hom)

/-- The second map `G → j'_*M'` of the sequence of Step 5. -/
noncomputable def correctionSeqG :
    (WeilComplex.homologySheaf (-1)).obj ((fourierTransform ψ).obj D.shiftedExtensionByZero) ⟶
      D'.directImage :=
  WeilSheaf.toShiftedComplex.preimage ((isoExtensionByZeroOfIso eB eM).inv ≫
    (fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension ≫ eM.hom)

lemma toShiftedComplex_map_correctionSeqF :
    WeilSheaf.toShiftedComplex.map (correctionSeqF eB eM) =
      eB.inv ≫ (fourierTriangle (ψ := ψ) D).mor₁ ≫ (isoExtensionByZeroOfIso eB eM).hom :=
  WeilSheaf.toShiftedComplex.map_preimage _

lemma toShiftedComplex_map_correctionSeqG :
    WeilSheaf.toShiftedComplex.map (correctionSeqG eB eM) =
      (isoExtensionByZeroOfIso eB eM).inv ≫
        (fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension ≫ eM.hom :=
  WeilSheaf.toShiftedComplex.map_preimage _

/-- The short complex `0 → B' → G → j'_*M' → 0` of Step 5 of
`lemma-fourier-transform-boundary-sequence`, read off from the transform of the rotated boundary
triangle through the isomorphisms with the shifted sheaves. -/
noncomputable def correctionSeq : ShortComplex (WeilSheaf k₀ l (affineLine k₀)) :=
  ShortComplex.mk (correctionSeqF eB eM) (correctionSeqG eB eM)
    (WeilSheaf.toShiftedComplex.map_injective (by
      rw [Functor.map_comp, toShiftedComplex_map_correctionSeqF,
        toShiftedComplex_map_correctionSeqG, Functor.map_zero]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [reassoc_of% (fourierTriangle_mor₁_comp (ψ := ψ) D), zero_comp, comp_zero]))

/-- The sequence `𝓗⁻¹` of the transformed boundary triangle. -/
noncomputable def homologySeq (D : LisseOnDenseOpen k₀ l) :
    ShortComplex (WeilSheaf k₀ l (affineLine k₀)) :=
  ShortComplex.mk ((WeilComplex.homologySheaf (-1)).map (fourierTriangle (ψ := ψ) D).mor₁)
    ((WeilComplex.homologySheaf (-1)).map (fourierTriangle (ψ := ψ) D).mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
      (fourierTriangle_distinguished (ψ := ψ) D), Functor.map_zero])

/-- `𝓗⁻¹` of a morphism of shifted Weil sheaves. -/
lemma homologySheaf_map_toShiftedComplex_map {F G : WeilSheaf k₀ l (affineLine k₀)}
    (φ : F ⟶ G) :
    (WeilComplex.homologySheaf (-1)).map (WeilSheaf.toShiftedComplex.map φ) ≫
        WeilSheaf.toShiftedComplexCompHomologySheafIso.hom.app G =
      WeilSheaf.toShiftedComplexCompHomologySheafIso.hom.app F ≫ φ :=
  WeilSheaf.toShiftedComplexCompHomologySheafIso.hom.naturality φ

/-- The first component `𝓗⁻¹ FT_ψ(B) ≅ B'` of the comparison of Step 5. -/
noncomputable def correctionIso₁ :
    (WeilComplex.homologySheaf (-1)).obj (fourierTriangle (ψ := ψ) D).obj₁ ≅ B' :=
  (WeilComplex.homologySheaf (-1)).mapIso eB ≪≫
    WeilSheaf.toShiftedComplexCompHomologySheafIso.app B'

/-- The second component `𝓗⁻¹ FT_ψ(j_!M[1]) ≅ G` of the comparison of Step 5. -/
noncomputable def correctionIso₂ :
    (WeilComplex.homologySheaf (-1)).obj (fourierTriangle (ψ := ψ) D).obj₂ ≅
      (WeilComplex.homologySheaf (-1)).obj ((fourierTransform ψ).obj D.shiftedExtensionByZero) :=
  (WeilComplex.homologySheaf (-1)).mapIso
      (eqToIso (fourierTriangle_obj₂ (ψ := ψ) D) ≪≫ isoExtensionByZeroOfIso eB eM) ≪≫
    WeilSheaf.toShiftedComplexCompHomologySheafIso.app
      ((WeilComplex.homologySheaf (-1)).obj ((fourierTransform ψ).obj D.shiftedExtensionByZero))

/-- The third component `𝓗⁻¹ FT_ψ(j_*M[1]) ≅ j'_*M'` of the comparison of Step 5. -/
noncomputable def correctionIso₃ :
    (WeilComplex.homologySheaf (-1)).obj (fourierTriangle (ψ := ψ) D).obj₃ ≅ D'.directImage :=
  (WeilComplex.homologySheaf (-1)).mapIso eM ≪≫
    WeilSheaf.toShiftedComplexCompHomologySheafIso.app D'.directImage

/-- The short complex of Step 5 is the sequence `𝓗⁻¹` of the transformed triangle, up to the sign
of the last map. -/
noncomputable def correctionSeqIso : homologySeq (ψ := ψ) D ≅ correctionSeq eB eM :=
  ShortComplex.isoMk (correctionIso₁ eB) (correctionIso₂ eB eM) (-correctionIso₃ eM)
    (by
      change _ ≫ correctionSeqF eB eM = (WeilComplex.homologySheaf (-1)).map
        (fourierTriangle (ψ := ψ) D).mor₁ ≫ _
      simp only [correctionIso₁, correctionIso₂, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc, eqToIso_refl, Iso.refl_hom, Category.id_comp]
      rw [← homologySheaf_map_toShiftedComplex_map, toShiftedComplex_map_correctionSeqF]
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc])
    (by
      change _ ≫ correctionSeqG eB eM = (WeilComplex.homologySheaf (-1)).map
        (fourierTriangle (ψ := ψ) D).mor₂ ≫ _
      simp only [correctionIso₂, correctionIso₃, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc, Preadditive.neg_iso_hom, Preadditive.comp_neg, eqToIso_refl,
        Iso.refl_hom, Category.id_comp]
      rw [← homologySheaf_map_toShiftedComplex_map, toShiftedComplex_map_correctionSeqG,
        fourierTriangle_mor₂, Functor.map_neg, Preadditive.neg_comp, neg_neg]
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc])

/-- The sequence `0 → B' → G → j'_*M' → 0` of Step 5 is short exact: in the long exact sequence
of cohomology sheaves of the transformed triangle, `𝓗⁻²` of `(j'_*M')[1]` and `𝓗⁰` of `B'[1]`
vanish. -/
lemma shortExact_correctionSeq : (correctionSeq eB eM).ShortExact := by
  have hT := fourierTriangle_distinguished (ψ := ψ) D
  refine ShortComplex.shortExact_of_iso (correctionSeqIso eB eM) ?_
  have h₃ : IsZero ((WeilComplex.homologySheaf (-2)).obj (fourierTriangle (ψ := ψ) D).obj₃) :=
    (WeilSheaf.isZero_homologySheaf_toShiftedComplex (by norm_num) D'.directImage).of_iso
      ((WeilComplex.homologySheaf (-2)).mapIso eM)
  have h₁ : IsZero ((WeilComplex.homologySheaf 0).obj (fourierTriangle (ψ := ψ) D).obj₁) :=
    (WeilSheaf.isZero_homologySheaf_toShiftedComplex (by norm_num) B').of_iso
      ((WeilComplex.homologySheaf 0).mapIso eB)
  have hm := (WeilComplex.homologySheaf_exact₁ _ (-2) (-1) hT (by norm_num)).mono_g
    (h₃.eq_of_src _ _)
  have he := (WeilComplex.homologySheaf_exact₃ _ (-1) 0 hT (by norm_num)).epi_f
    (h₁.eq_of_tgt _ _)
  exact { exact := WeilComplex.homologySheaf_exact₂ _ (-1) hT, mono_f := hm, epi_g := he }

/-- The zero-extension comparison datum built from the isomorphisms `FT_ψ(B) ≅ B'[1]` and
`FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]` by Step 5 of `lemma-fourier-transform-boundary-sequence`. -/
noncomputable def fourierCorrectionOfIso : FourierCorrection ψ D D' where
  seq := correctionSeq eB eM
  shortExact := shortExact_correctionSeq eB eM
  isoDirectImage := Iso.refl _
  isoExtensionByZero := isoExtensionByZeroOfIso eB eM
  isoBoundary := eB
  isoMiddleExtension := eM
  fourierTransform_map_comp_isoMiddleExtension_hom := by
    change _ = _ ≫ WeilSheaf.toShiftedComplex.map (correctionSeqG eB eM)
    rw [toShiftedComplex_map_correctionSeqG, Iso.hom_inv_id_assoc]

end Construction

/-- For an irreducible nonexceptional `M` and a Fourier partner `D'` of `D`, the zero-extension
comparison datum exists. Only the hypothesis on the Fourier partner `D'` enters the argument:
irreducibility and nonexceptionality serve to guarantee that a Fourier partner exists.
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
theorem nonempty_fourierCorrection (_hψ : ψ ≠ 1) (D D' : LisseOnDenseOpen k₀ l)
    (_hD : D.sheaf.IsIrreducibleLisse)
    (_hne : D.sheaf.IsNonexceptional ψ D.j) (hFT : D.IsFourierPartner ψ D') :
    Nonempty (FourierCorrection ψ D D') := by
  obtain ⟨B', -, ⟨eB⟩⟩ := D.exists_isLisse_iso_fourierTransform_boundarySheaf ψ
  exact ⟨fourierCorrectionOfIso eB hFT.some⟩

/-- The correction sheaf `B'` is lisse on the entire dual line: it is a sum of finite direct
images of Artin–Schreier kernels. It is `𝓗⁻¹ FT_ψ(B)`, as is the sheaf of
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_isLisse_iso_fourierTransform_boundarySheaf`.
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
theorem FourierCorrection.isLisse {D D' : LisseOnDenseOpen k₀ l}
    (c : FourierCorrection ψ D D') : c.seq.X₁.IsLisse := by
  obtain ⟨B', hB', ⟨eB⟩⟩ := D.exists_isLisse_iso_fourierTransform_boundarySheaf ψ
  exact hB'.of_iso (WeilSheaf.toShiftedComplex.preimageIso (c.isoBoundary.symm ≪≫ eB)).symm

/-- The correction sheaf `B'` has weights at most `w` when `M` is punctually `ι`-pure of weight
`w`: semicontinuity of weights at the boundary points, together with the weight zero of the
Artin–Schreier kernel
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_of_iso_fourierTransform`).
(blueprint: `lemma-fourier-transform-boundary-sequence`) -/
theorem FourierCorrection.hasWeightsAtMost (ι : PadicAlgCl l →+* ℂ)
    {D D' : LisseOnDenseOpen k₀ l} (c : FourierCorrection ψ D D') {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) : c.seq.X₁.HasWeightsAtMost ι w :=
  D.hasWeightsAtMost_of_iso_fourierTransform ψ hw.hasWeightsAtMost c.isoBoundary

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
