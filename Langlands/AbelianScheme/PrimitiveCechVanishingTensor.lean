import Langlands.AbelianScheme.PrimitiveCechVanishing
import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityReduction

/-! # Vanishing of primitive degree-two Čech classes, on the chosen fibre square -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology (structurePull)
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PrimitiveCechVanishing

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The chosen fibre square of `A` in the slice category is its binary product. -/
def tensorIsoProd : A.X ⊗ A.X ≅ A.X ⨯ A.X where
  hom := prod.lift (fst A.X A.X) (snd A.X A.X)
  inv := lift prod.fst prod.snd
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by
    apply prod.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem tensorIsoProd_hom_fst : (tensorIsoProd A).hom ≫ prod.fst = fst A.X A.X :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem tensorIsoProd_hom_snd : (tensorIsoProd A).hom ≫ prod.snd = snd A.X A.X :=
  prod.lift_snd _ _

theorem tensorIsoProd_hom_mul : (tensorIsoProd A).hom ≫ mul A = fst A.X A.X * snd A.X A.X := by
  rw [mul, MonObj.comp_mul, tensorIsoProd_hom_fst, tensorIsoProd_hom_snd]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of the reduced coproduct on the degree-two structure cohomology of the chosen
fibre square. -/
theorem injective_tensor :
    Function.Injective (structurePull (fst A.X A.X * snd A.X A.X) 2 -
      structurePull (fst A.X A.X) 2 - structurePull (snd A.X A.X) 2) := by
  have hK : Function.Injective (structurePull (mul A) 2 -
      structurePull (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 -
      structurePull (prod.snd : A.X ⨯ A.X ⟶ A.X) 2) := fieldH2PrimitiveInjectivity K A
  rw [← tensorIsoProd_hom_mul, ← tensorIsoProd_hom_fst, ← tensorIsoProd_hom_snd,
    Langlands.AbelianScheme.ArtinianH2Reduction.structurePull_comp,
    Langlands.AbelianScheme.ArtinianH2Reduction.structurePull_comp,
    Langlands.AbelianScheme.ArtinianH2Reduction.structurePull_comp,
    ← LinearMap.comp_sub, ← LinearMap.comp_sub]
  exact (Langlands.AbelianScheme.ArtinianH2Reduction.structurePull_injective_of_iso
    (tensorIsoProd A) 2).comp hK

set_option maxHeartbeats 1600000 in
/-- The statement of `exists_coboundary` for the chosen fibre square `A ⊗ A` of the slice
category, with its projections and the multiplication `fst * snd`. -/
theorem exists_coboundary_tensor
    {I : Type u} [Fintype I] (W : I → A.X.left.Opens) (hW : ⨆ i, W i = ⊤)
    (hWa : ∀ i, IsAffineOpen (W i))
    {κ : Type u} [Fintype κ] (W₂ : κ → (A.X ⊗ A.X).left.Opens) (hW₂ : ⨆ i, W₂ i = ⊤)
    (hW₂a : ∀ i, IsAffineOpen (W₂ i))
    {LP LQ : Type u} [Fintype LP] [Fintype LQ]
    (VP : LP → (A.X ⊗ A.X).left.Opens) (hVP : ⨆ i, VP i = ⊤) (hVPa : ∀ i, IsAffineOpen (VP i))
    (VQ : LQ → (A.X ⊗ A.X).left.Opens) (hVQ : ⨆ i, VQ i = ⊤) (hVQa : ∀ i, IsAffineOpen (VQ i))
    (βP : LP → κ) (hβP : ∀ j, VP j ≤ W₂ (βP j)) (βQ : LQ → κ) (hβQ : ∀ j, VQ j ≤ W₂ (βQ j))
    (a₁ : LP → I) (ha₁ : ∀ j, VP j ≤ (fst A.X A.X).left ⁻¹ᵁ W (a₁ j))
    (aₘ : LQ → I)
    (haₘ : ∀ j, VQ j ≤ (fst A.X A.X * snd A.X A.X).left ⁻¹ᵁ W (aₘ j))
    (a₂ : LQ → I) (ha₂ : ∀ j, VQ j ≤ (snd A.X A.X).left ⁻¹ᵁ W (a₂ j))
    (d : LinearMap.ker (dCochain A.X.hom W (unitModule A.X.left) 2))
    (e : LinearMap.ker (dCochain (A.X ⊗ A.X).hom W₂ (unitModule (A.X ⊗ A.X).left) 2))
    (hP : (refineCochain (A.X ⊗ A.X).hom W₂ VP βP hβP (unitModule _)).f 2
        (e : cochain (A.X ⊗ A.X).hom W₂ (unitModule _) 2) =
      (unitCochainMap (fst A.X A.X) W VP a₁ ha₁).f 2
        (d : cochain A.X.hom W (unitModule _) 2))
    (hQ : (refineCochain (A.X ⊗ A.X).hom W₂ VQ βQ hβQ (unitModule _)).f 2
        (e : cochain (A.X ⊗ A.X).hom W₂ (unitModule _) 2) =
      (unitCochainMap (fst A.X A.X * snd A.X A.X) W VQ aₘ haₘ).f 2
          (d : cochain A.X.hom W (unitModule _) 2) -
        (unitCochainMap (snd A.X A.X) W VQ a₂ ha₂).f 2
          (d : cochain A.X.hom W (unitModule _) 2)) :
    ∃ y, dCochain A.X.hom W (unitModule A.X.left) 1 y = d := by
  let P := A.X ⊗ A.X
  have : IsSeparated P.hom := by
    change IsSeparated (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
    infer_instance
  let p₁ : P ⟶ A.X := fst A.X A.X
  let p₂ : P ⟶ A.X := snd A.X A.X
  let m : P ⟶ A.X := fst A.X A.X * snd A.X A.X
  let pull (f : P ⟶ A.X) :=
    (relativeCohomologyPullback f (SheafOfModules.unit A.X.left.ringCatSheaf) 2 ≫
      (relativeCohomology P.hom 2).map (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom).hom
  let o := canonicalClass A.X.hom W hW hWa 1 d
  have h₁ := pull_canonicalClass p₁ W VP a₁ ha₁ hW hVP hWa hVPa 1 d
  have hₘ := pull_canonicalClass m W VQ aₘ haₘ hW hVQ hWa hVQa 1 d
  have h₂ := pull_canonicalClass p₂ W VQ a₂ ha₂ hW hVQ hWa hVQa 1 d
  have eP := canonicalClass_refine P.hom W₂ VP βP hβP hW₂ hVP hW₂a hVPa 1 e
  have eQ := canonicalClass_refine P.hom W₂ VQ βQ hβQ hW₂ hVQ hW₂a hVQa 1 e
  have hP' : pull p₁ o = canonicalClass P.hom W₂ hW₂ hW₂a 1 e := by
    rw [eP]
    refine h₁.trans (congrArg _ (Subtype.ext ?_))
    exact hP.symm
  have hQ' : pull m o - pull p₂ o = canonicalClass P.hom W₂ hW₂ hW₂a 1 e := by
    rw [eQ]
    change _ = canonicalClass P.hom VQ hVQ hVQa 1 _
    rw [show (⟨_, refine_mem_ker P.hom W₂ VQ βQ hβQ 1 e⟩ :
        LinearMap.ker (dCochain P.hom VQ (unitModule P.left) 2)) =
        ⟨_, chainMap_mem_ker W VQ (unitCochainMap m W VQ aₘ haₘ) 1 d⟩ -
          ⟨_, chainMap_mem_ker W VQ (unitCochainMap p₂ W VQ a₂ ha₂) 1 d⟩ from
      Subtype.ext hQ, map_sub]
    exact congrArg₂ (· - ·) hₘ h₂
  have hzero : (pull m - pull p₁ - pull p₂) o = 0 := by
    simp only [LinearMap.sub_apply]
    rw [hP', ← hQ']
    abel
  have hinj : Function.Injective (pull m - pull p₁ - pull p₂) := injective_tensor A
  have ho : o = 0 := hinj (hzero.trans (map_zero _).symm)
  exact (canonicalClass_eq_zero_iff A.X.hom W hW hWa 1 d).mp ho

end Langlands.AbelianScheme.PrimitiveCechVanishing
