/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.Fourier

/-!
# Concentration of the zero-extension transform

For a nonzero irreducible lisse Weil sheaf `M` on a dense open `j : U₀ ↪ 𝔸¹` which is
constituent-nonexceptional, the blueprint lemma `proposition-purity-lisse-part-fourier-transform`
states:

1. the twisted cohomology `H_c^q(U, M ⊗ ℒ_{ψ(ax)})` is concentrated in degree one;
2. the twisted dual `M† = M^∨ ⊗ 𝓑_b` is again irreducible lisse and nonexceptional;
3. the transforms `FT_ψ(j_!M)` and `FT_{ψ⁻¹}(j_!M†)` are sheaves, and `R^ν pr₂! 𝒦` of the
   realified kernel `𝒦` is concentrated in degree one, where it is
   `FT_ψ(j_!M) ⊕ FT_{ψ⁻¹}(j_!M†)`.

This file contains the formal plumbing for part (3): the compatibility of `toComplex` with the
pullback and with the tensor product by a lisse sheaf, and the computation of the higher direct
images with compact support of a sum of two kernels `𝒦_{ψᵢ} ⊗ pr₁^* Fᵢ` whose transforms are
sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section ToComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product of a Weil sheaf placed in degree zero with a lisse Weil sheaf `G` is the
tensor product of the sheaves, placed in degree zero: the tensor product with a lisse sheaf,
the internal hom out of its dual, is exact. -/
noncomputable def WeilSheaf.toComplexCompTensorLisseIso (G : WeilSheaf k₀ l X)
    (hG : G.IsLisse) :
    WeilSheaf.toComplex ⋙ WeilComplex.tensorLisse G hG ≅
      { obj F := WeilSheaf.tensorObj G F hG
        map f := ObjectProperty.homMk ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map f.hom)
        map_id F := ObjectProperty.hom_ext _ ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map_id F.obj)
        map_comp f g := ObjectProperty.hom_ext _ ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map_comp f.hom g.hom) } ⋙ WeilSheaf.toComplex :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (G.dual hG).obj).singleFunctorCompRightDerivedFunctorIso.app F.obj))
    fun f ↦ ObjectProperty.hom_ext _
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (G.dual hG).obj).singleFunctorCompRightDerivedFunctorIso.hom.naturality f.hom)

end ToComplex

section Kernel

attribute [local instance] Abelian.hasFiniteBiproducts

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- The kernel sheaf `𝒦_ψ ⊗ pr₁^* F` on the affine plane whose compactly supported direct image
along `pr₂` computes the Fourier transform of `F`. -/
noncomputable abbrev WeilSheaf.fourierKernelTensor (F : WeilSheaf k₀ l (affineLine k₀)) :
    WeilSheaf k₀ l (affinePlane k₀) :=
  WeilSheaf.tensorObj (fourierKernel ψ) ((WeilSheaf.upperStar (affinePlane.fst k₀)).obj F)
    (isLisse_fourierKernel ψ)

/-- The compactly supported direct image `Rpr₂!(𝒦_ψ ⊗ pr₁^* F)` is the transform of `F` shifted
by `-1`: the transform is `Rpr₂!(𝒦_ψ ⊗ pr₁^* -)[1]`, and the pullback and the tensor product
with the lisse kernel are exact. (blueprint: `sec-Fourier-inversion`) -/
noncomputable def WeilSheaf.derivedLowerShriekFourierKernelTensorIso
    (F : WeilSheaf k₀ l (affineLine k₀)) :
    (WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.fourierKernelTensor ψ F)) ≅
      ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj F))⟦(-1 : ℤ)⟧ :=
  (WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).mapIso
      (((WeilSheaf.toComplexCompTensorLisseIso (fourierKernel ψ)
        (isLisse_fourierKernel ψ)).app _).symm ≪≫
      (WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).mapIso
        ((WeilSheaf.toComplexCompUpperStarIso (affinePlane.fst k₀)).app F).symm) ≪≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).symm.app _

variable {ψ} {F S : WeilSheaf k₀ l (affineLine k₀)}
  (e : (fourierTransform ψ).obj (WeilSheaf.toComplex.obj F) ≅ WeilSheaf.toComplex.obj S)

include e in
/-- If the transform of `F` is a sheaf `S`, then `R^ν pr₂!(𝒦_ψ ⊗ pr₁^* F)` vanishes for
`ν ≠ 1`. -/
theorem WeilSheaf.isZero_higherLowerShriek_fourierKernelTensor {ν : ℕ} (hν : ν ≠ 1) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l (affinePlane.snd k₀) ν).obj
      (WeilSheaf.fourierKernelTensor ψ F)) :=
  (WeilSheaf.isZero_homologySheaf_shift_toComplex S (n := -1) (a := ν) (by omega)).of_iso
    ((WeilComplex.homologySheaf ν).mapIso
      (WeilSheaf.derivedLowerShriekFourierKernelTensorIso ψ F ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso e))

/-- If the transform of `F` is a sheaf `S`, then `R^1 pr₂!(𝒦_ψ ⊗ pr₁^* F) ≅ S`. -/
noncomputable def WeilSheaf.higherLowerShriekFourierKernelTensorIso :
    (WeilSheaf.higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj
      (WeilSheaf.fourierKernelTensor ψ F) ≅ S :=
  (WeilComplex.homologySheaf 1).mapIso
      (WeilSheaf.derivedLowerShriekFourierKernelTensorIso ψ F ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso e) ≪≫
    WeilComplex.homologySheafShiftIso _ (-1) 1 0 (by norm_num) ≪≫
    WeilSheaf.toComplexCompHomologySheafIso.app S

end Kernel

end AlgebraicGeometry
