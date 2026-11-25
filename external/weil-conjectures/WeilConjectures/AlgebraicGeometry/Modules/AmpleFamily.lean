/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Ample families of sections of an invertible module

A scheme `X` *has an ample family* if it carries an invertible module `L` with finitely many
global sections `s i : 𝒪_X ⟶ L` whose non-vanishing loci `X_{s i}` are affine and cover `X`. This
is the form of ampleness (Stacks 01PS) produced by the proof of Stacks 0BF7.

## Main definitions

- `AlgebraicGeometry.Scheme.HasAmpleFamily`: `X` carries an invertible module with finitely many
  sections whose non-vanishing loci are affine and cover `X`.

## Main statements

- `AlgebraicGeometry.Scheme.HasAmpleFamily.of_isAffineHom`: the property pulls back along affine
  morphisms.
- `AlgebraicGeometry.Scheme.HasAmpleFamily.of_iso`: the property is invariant under isomorphism.
- `AlgebraicGeometry.isAffineHom_sigmaDesc`: a morphism out of a finite disjoint union is affine
  if each of its components is.
- `AlgebraicGeometry.Scheme.HasAmpleFamily.sigma`: a finite disjoint union of copies of a scheme
  with an ample family has an ample family.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The preimage of an open `U` under a morphism `Sigma.desc f` out of a disjoint union is the
union of the images of the preimages `f i ⁻¹ᵁ U` in the components. -/
lemma preimage_sigmaDesc {σ : Type u} {g : σ → Scheme.{u}} {X : Scheme.{u}}
    (f : ∀ i, g i ⟶ X) (U : X.Opens) :
    Sigma.desc f ⁻¹ᵁ U = ⨆ i, Sigma.ι g i ''ᵁ (f i ⁻¹ᵁ U) := by
  ext x
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk g).surjective x
  rw [sigmaMk_mk, SetLike.mem_coe, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
  refine ⟨fun h ↦ ⟨i, y, ?_, rfl⟩, ?_⟩
  · rwa [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] at h
  rintro ⟨j, z, hz, e⟩
  obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff g j i z y).mp e)
  rwa [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

/-- A morphism `Sigma.desc f` out of a finite disjoint union is affine if each `f i` is: the
preimage of an affine open is the disjoint union of the affine opens `f i ⁻¹ᵁ U`. -/
lemma isAffineHom_sigmaDesc {σ : Type u} [Finite σ] {g : σ → Scheme.{u}} {X : Scheme.{u}}
    (f : ∀ i, g i ⟶ X) [∀ i, IsAffineHom (f i)] : IsAffineHom (Sigma.desc f) where
  isAffine_preimage U hU := by
    rw [preimage_sigmaDesc]
    refine IsAffineOpen.iSup_of_disjoint (fun i ↦ (hU.preimage (f i)).image_of_isOpenImmersion _)
      fun i j hij ↦ ?_
    exact (disjoint_opensRange_sigmaι g i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)

namespace Scheme

/-- A scheme `X` *has an ample family* if it carries an invertible module `L` with finitely many
global sections `s i : 𝒪_X ⟶ L` whose non-vanishing loci are affine and cover `X`. -/
def HasAmpleFamily (X : Scheme.{u}) : Prop :=
  ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u) (_ : Finite ι)
    (s : ι → (𝟙_ X.Modules ⟶ L)),
    (∀ i, IsAffineOpen (Modules.Hom.zeroLocus (s i)).support.compl) ∧
      ⨆ i, (Modules.Hom.zeroLocus (s i)).support.compl = ⊤

lemma hasAmpleFamily_iff (X : Scheme.{u}) :
    X.HasAmpleFamily ↔
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
        (_ : Finite ι) (s : ι → (𝟙_ X.Modules ⟶ L)),
        (∀ i, IsAffineOpen (Modules.Hom.zeroLocus (s i)).support.compl) ∧
          ⨆ i, (Modules.Hom.zeroLocus (s i)).support.compl = ⊤ :=
  Iff.rfl


namespace HasAmpleFamily

/-- **Ample families pull back along affine morphisms.** If `L` with sections `s i` is an ample
family on `Y` and `f : X ⟶ Y` is affine, then `f^* L` with the sections `f^* s i` is an ample
family on `X`: the non-vanishing locus of `f^* s i` is the preimage of that of `s i`. -/
theorem of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (h : Y.HasAmpleFamily) :
    X.HasAmpleFamily := by
  obtain ⟨L, hL, ι, _, s, hs, hcov⟩ := h
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ Y.Modules) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  let t (i : ι) : 𝟙_ X.Modules ⟶ (Modules.pullback f).obj L :=
    (Modules.pullbackObjUnitIso f).inv ≫ (Modules.pullback f).map (s i)
  have ht (i : ι) : (Modules.Hom.zeroLocus (t i)).support.compl =
      f ⁻¹ᵁ (Modules.Hom.zeroLocus (s i)).support.compl := by
    rw [Modules.Hom.zeroLocus_eq_of_arrowIso (t i) ((Modules.pullback f).map (s i))
      (Arrow.isoMk (Modules.pullbackObjUnitIso f).symm (Iso.refl _)),
      ← Modules.Hom.comap_zeroLocus, IdealSheafData.support_comap]
    rfl
  refine ⟨_, hL.pullback, ι, inferInstance, t, fun i ↦ ?_, ?_⟩
  · rw [ht]
    exact (hs i).preimage f
  · simp_rw [ht]
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]

/-- **Ample families are invariant under isomorphism.** -/
theorem of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : Y.HasAmpleFamily) : X.HasAmpleFamily :=
  of_isAffineHom e.hom h

/-- A finite disjoint union of copies of a scheme with an ample family has an ample family: the
fold map `∐ Y ⟶ Y` is affine. -/
theorem sigma {Y : Scheme.{u}} (σ : Type u) [Finite σ] (h : Y.HasAmpleFamily) :
    (∐ fun _ : σ ↦ Y).HasAmpleFamily :=
  have : ∀ _ : σ, IsAffineHom (𝟙 Y) := fun _ ↦ inferInstance
  have := isAffineHom_sigmaDesc fun _ : σ ↦ 𝟙 Y
  of_isAffineHom (Sigma.desc fun _ : σ ↦ 𝟙 Y) h

end HasAmpleFamily

end Scheme

end AlgebraicGeometry
