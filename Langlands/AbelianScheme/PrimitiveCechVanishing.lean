import Langlands.AbelianScheme.FieldH2PrimitiveInjectivityProof
import Langlands.AbelianScheme.CanonicalH1Primitive
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqRefine

/-! # Vanishing of degree-two Čech classes that become primitive on the square -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PrimitiveCechVanishing

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The group law of `A`, as a morphism from the square. -/
def mul : A.X ⨯ A.X ⟶ A.X := prod.fst * prod.snd

set_option maxHeartbeats 1600000 in
/-- Let `d` be an ordered Čech `2`-cocycle of the structure sheaf of an abelian variety `A` for
a finite affine cover `W`, and let `e` be one of `A × A` for a finite affine cover `W₂`. Suppose
that `e`, refined to a cover `VP` of `A × A` refining the inverse images of `W` under the
first projection, is the pullback of `d` along the first projection, and that `e`, refined to a
cover `VQ` refining the inverse images of `W` under the multiplication and under the second
projection, is the difference of the pullbacks of `d` along the multiplication and the second
projection. Then `d` is a coboundary. -/
theorem exists_coboundary
    {I : Type u} [Fintype I] (W : I → A.X.left.Opens) (hW : ⨆ i, W i = ⊤)
    (hWa : ∀ i, IsAffineOpen (W i))
    {κ : Type u} [Fintype κ] (W₂ : κ → (A.X ⨯ A.X).left.Opens) (hW₂ : ⨆ i, W₂ i = ⊤)
    (hW₂a : ∀ i, IsAffineOpen (W₂ i))
    {LP LQ : Type u} [Fintype LP] [Fintype LQ]
    (VP : LP → (A.X ⨯ A.X).left.Opens) (hVP : ⨆ i, VP i = ⊤) (hVPa : ∀ i, IsAffineOpen (VP i))
    (VQ : LQ → (A.X ⨯ A.X).left.Opens) (hVQ : ⨆ i, VQ i = ⊤) (hVQa : ∀ i, IsAffineOpen (VQ i))
    (βP : LP → κ) (hβP : ∀ j, VP j ≤ W₂ (βP j)) (βQ : LQ → κ) (hβQ : ∀ j, VQ j ≤ W₂ (βQ j))
    (a₁ : LP → I) (ha₁ : ∀ j, VP j ≤ (prod.fst : A.X ⨯ A.X ⟶ A.X).left ⁻¹ᵁ W (a₁ j))
    (aₘ : LQ → I)
    (haₘ : ∀ j, VQ j ≤ (mul A).left ⁻¹ᵁ W (aₘ j))
    (a₂ : LQ → I) (ha₂ : ∀ j, VQ j ≤ (prod.snd : A.X ⨯ A.X ⟶ A.X).left ⁻¹ᵁ W (a₂ j))
    (d : LinearMap.ker (dCochain A.X.hom W (unitModule A.X.left) 2))
    (e : LinearMap.ker (dCochain (A.X ⨯ A.X).hom W₂ (unitModule (A.X ⨯ A.X).left) 2))
    (hP : (refineCochain (A.X ⨯ A.X).hom W₂ VP βP hβP (unitModule _)).f 2
        (e : cochain (A.X ⨯ A.X).hom W₂ (unitModule _) 2) =
      (unitCochainMap (prod.fst : A.X ⨯ A.X ⟶ A.X) W VP a₁ ha₁).f 2
        (d : cochain A.X.hom W (unitModule _) 2))
    (hQ : (refineCochain (A.X ⨯ A.X).hom W₂ VQ βQ hβQ (unitModule _)).f 2
        (e : cochain (A.X ⨯ A.X).hom W₂ (unitModule _) 2) =
      (unitCochainMap (mul A) W VQ aₘ haₘ).f 2
          (d : cochain A.X.hom W (unitModule _) 2) -
        (unitCochainMap (prod.snd : A.X ⨯ A.X ⟶ A.X) W VQ a₂ ha₂).f 2
          (d : cochain A.X.hom W (unitModule _) 2)) :
    ∃ y, dCochain A.X.hom W (unitModule A.X.left) 1 y = d := by
  let P := A.X ⨯ A.X
  let p₁ : P ⟶ A.X := prod.fst
  let p₂ : P ⟶ A.X := prod.snd
  let m : P ⟶ A.X := mul A
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
  have hinj : Function.Injective (pull m - pull p₁ - pull p₂) := fieldH2PrimitiveInjectivity K A
  have ho : o = 0 := hinj (hzero.trans (map_zero _).symm)
  exact (canonicalClass_eq_zero_iff A.X.hom W hW hWa 1 d).mp ho

end Langlands.AbelianScheme.PrimitiveCechVanishing
