/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian

/-!
# Sheaves are filtered colimits of constructible subsheaves (Stacks 03SA)

Let `X` be a Noetherian scheme and `Λ` a finite commutative ring. Every étale sheaf `F` of
`Λ`-modules on `X` is a quotient of the sum `∐ v_! Λ` over the sections of `F` over affine étale
`X`-schemes `v : V ⟶ X` (`AlgebraicGeometry.Etale.epi_sigmaDesc_sectionHom`). The images of the
finite subsums are constructible subsheaves of `F` (quotients of constructible sheaves, the kernel
being constructible by `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`), they form a
directed family indexed by the finite sets of sections, and `F` is their colimit
(`AlgebraicGeometry.Etale.isColimitFinsetSectionImageCocone`, blueprint
`lemma-finiteness-small-etale-topoi--1`).

## Main definitions

- `AlgebraicGeometry.Etale.finsetSectionImage F`: the functor `S ↦ im(∐_{i ∈ S} v_i! Λ ⟶ F)`
  from the directed set of finite sets of sections of `F`, with values in subsheaves of `F`.
- `AlgebraicGeometry.Etale.finsetSectionImageCocone F`: its cocone with point `F`.

## Main statements

- `AlgebraicGeometry.Etale.isColimitFinsetSectionImageCocone`: `F` is the colimit.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_finsetSectionImage_obj`: the subsheaves are
  constructible.
- `AlgebraicGeometry.Etale.exists_isColimit_isConstructibleSheaf` (blueprint
`lemma-finiteness-small-etale-topoi--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] IsFiltered.isConnected

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The generators `v_! Λ` of `F`, indexed by the sections of `F` over affine étale
`X`-schemes. -/
abbrev sectionGenerator (i : SectionIndex F) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  lowerShriekUnit (Λ := Λ) i.1.1.hom i.1.1.prop

/-- The map `v_! Λ ⟶ F` given by a section of `F` over an affine étale `X`-scheme. -/
abbrev sectionGeneratorHom (i : SectionIndex F) : sectionGenerator F i ⟶ F :=
  sectionHom F i.1.1.hom i.1.1.prop i.2

/-- The image of the finite subsum `∐_{i ∈ S} v_i! Λ ⟶ F`, as a subobject of `F`. -/
abbrev finsetSectionImageSubobject (S : Finset (SectionIndex F)) : Subobject F :=
  imageSubobject (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S)

lemma finsetSectionImageSubobject_mono :
    Monotone (finsetSectionImageSubobject F) := by
  intro S S' h
  let incl : (∐ fun i : S ↦ sectionGenerator F i.1) ⟶ ∐ fun i : S' ↦ sectionGenerator F i.1 :=
    Sigma.desc fun i : S ↦ Sigma.ι (fun i : S' ↦ sectionGenerator F i.1) ⟨i.1, h i.2⟩
  have hfac : incl ≫ finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S' =
      finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S := by
    ext i
    simp [incl]
  simpa only [hfac] using imageSubobject_comp_le incl
    (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S')

/-- The directed family of the images of the finite subsums of `∐ v_! Λ ⟶ F`, as a functor
from the finite sets of sections of `F` to the subsheaves of `F`. -/
def finsetSectionImage : Finset (SectionIndex F) ⥤ Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) :=
  (finsetSectionImageSubobject_mono F).functor ⋙ Subobject.underlying

/-- The cocone with point `F` over the images of the finite subsums of `∐ v_! Λ ⟶ F`, given by
the inclusions of the images. -/
@[simps]
def finsetSectionImageCocone : Cocone (finsetSectionImage F) where
  pt := F
  ι :=
    { app S := (finsetSectionImageSubobject F S).arrow
      naturality S S' h := by
        simp only [finsetSectionImage, Functor.comp_obj, Functor.comp_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact Subobject.ofLE_arrow _ }

instance mono_finsetSectionImageCocone_ι_app (S : Finset (SectionIndex F)) :
    Mono ((finsetSectionImageCocone F).ι.app S) :=
  Subobject.arrow_mono _

/-- The inclusions of the images of the finite subsums of `∐ v_! Λ ⟶ F` form a monomorphism from
the diagram to the constant diagram at `F`. -/
def finsetSectionImageToConst : finsetSectionImage F ⟶ (Functor.const _).obj F :=
  (finsetSectionImageCocone F).ι

instance mono_finsetSectionImageToConst : Mono (finsetSectionImageToConst F) :=
  have (S : Finset (SectionIndex F)) : Mono ((finsetSectionImageToConst F).app S) :=
    Subobject.arrow_mono (finsetSectionImageSubobject F S)
  NatTrans.mono_of_mono_app _

/-- The images of the finite subsums of `∐ v_! Λ ⟶ F` exhaust `F`: `F` is their colimit, the
colimit being exact in the Grothendieck abelian category of sheaves. -/
def isColimitFinsetSectionImageCocone : IsColimit (finsetSectionImageCocone F) := by
  classical
  let c := colimit.cocone (finsetSectionImage F)
  let hc := colimit.isColimit (finsetSectionImage F)
  let d : c.pt ⟶ F := hc.desc (finsetSectionImageCocone F)
  have hd (S : Finset (SectionIndex F)) : c.ι.app S ≫ d = (finsetSectionImageSubobject F S).arrow :=
    hc.fac _ S
  have hmono : Mono d := colim.map_mono' (finsetSectionImageToConst F) hc
    (isColimitConstCocone _ F) d (fun S ↦ (hd S).trans (by simp [finsetSectionImageToConst]))
  -- every generator factors through the image of the subsum indexed by itself
  have hgen (i : SectionIndex F) : ∃ l : sectionGenerator F i ⟶ c.pt,
      l ≫ d = sectionGeneratorHom F i := by
    let S : Finset (SectionIndex F) := {i}
    let k : sectionGenerator F i ⟶ ∐ fun j : S ↦ sectionGenerator F j.1 :=
      Sigma.ι (fun j : S ↦ sectionGenerator F j.1) ⟨i, Finset.mem_singleton_self i⟩
    refine ⟨k ≫ factorThruImageSubobject _ ≫ c.ι.app S, ?_⟩
    rw [Category.assoc, Category.assoc, hd, imageSubobject_arrow_comp]
    simp [k, finsetSigmaDesc]
  choose l hl using hgen
  have hepi : Epi d := by
    have := epi_sigmaDesc_sectionHom F
    have hfac : Sigma.desc l ≫ d = Sigma.desc fun i : SectionIndex F ↦ sectionGeneratorHom F i := by
      ext i
      simp [hl]
    exact epi_of_epi_fac hfac
  have : IsIso d := isIso_of_mono_of_epi d
  exact IsColimit.ofPointIso hc

variable [Finite Λ]

/-- The images of the finite subsums of `∐ v_! Λ ⟶ F` are constructible, on a Noetherian scheme:
they are quotients of finite sums of the constructible sheaves `v_! Λ` by subsheaves, which are
constructible. -/
instance isConstructibleSheaf_finsetSectionImage_obj [IsNoetherian X]
    (S : Finset (SectionIndex F)) : IsConstructibleSheaf ((finsetSectionImage F).obj S) := by
  have hH (i : SectionIndex F) : IsConstructibleSheaf (sectionGenerator F i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := X) i.1.1.hom
  let f := finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S
  have := isConstructibleSheaf_finsetSigma (sectionGenerator F) S
  have : IsConstructibleSheaf (kernel f) := IsConstructibleSheaf.of_mono (kernel.ι f)
  have : IsConstructibleSheaf (cokernel (kernel.ι f)) := IsConstructibleSheaf.cokernel _
  exact IsConstructibleSheaf.of_iso ((Abelian.coimageIsoImage' f).trans (imageSubobjectIso f).symm)

/-- Blueprint `lemma-finiteness-small-etale-topoi--1`: constructible generation (Stacks 03SA).

Let `X` be a Noetherian scheme, for instance a scheme of finite type over a field, and `Λ` a
finite commutative ring. Every sheaf `F` of `Λ`-modules on `X_ét` is a filtered colimit of
constructible sheaves: it is the colimit of the directed family of its constructible subsheaves
`AlgebraicGeometry.Etale.finsetSectionImage F`, the images of the finite subsums of the
presentation `∐ v_! Λ ⟶ F` by extensions by zero along affine étale `v : V ⟶ X`
(`AlgebraicGeometry.Etale.isColimitFinsetSectionImageCocone`). -/
@[stacks 03SA]
theorem exists_isColimit_isConstructibleSheaf [IsNoetherian X] :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D),
      c.pt = F ∧ (∀ j, IsConstructibleSheaf (D.obj j)) ∧ (∀ j, Mono (c.ι.app j)) ∧
        Nonempty (IsColimit c) :=
  ⟨_, inferInstance, inferInstance, finsetSectionImage F, finsetSectionImageCocone F, rfl,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, ⟨isColimitFinsetSectionImageCocone F⟩⟩

end Etale

end AlgebraicGeometry
