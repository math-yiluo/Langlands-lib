/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# Exactness of Čech complexes from the vanishing of higher direct images

Over an affine base, the Čech complex of a quasi-coherent module for an affine open cover of a
quasi-compact separated scheme computes the higher direct images (Leray). Hence it is exact in
degree `q > 0` as soon as `R^q f_* ℱ = 0`
(`AlgebraicGeometry.Scheme.Modules.exactAt_cechComplex_of_isZero_higherDirectImage`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T)

/-- **Vanishing higher direct images make Čech complexes exact.** Let `f : X ⟶ T` be quasi-compact
and separated with `T` affine, `U` a cover of `X` by affine opens and `ℱ` quasi-coherent. If
`R^q f_* ℱ = 0`, then the Čech complex of `ℱ` for `U` is exact in degree `q`: by Leray's theorem
its cohomology is `H^q(X, ℱ) = Γ(T, R^q f_* ℱ)`. -/
theorem exactAt_cechComplex_of_isZero_higherDirectImage [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ)
    (h : IsZero ((higherDirectImage f q).obj ℱ)) :
    ((TopCat.Presheaf.cechComplex U).obj ℱ.presheaf).ExactAt q := by
  have h₁ : Subsingleton Γ((higherDirectImage f q).obj ℱ, ⊤) := ⟨fun x y ↦ by
    have h0 := h.eq_of_src (𝟙 _) 0
    have hx : x = 0 := congr($(congrArg (fun φ ↦ Hom.app φ ⊤) h0) x)
    have hy : y = 0 := congr($(congrArg (fun φ ↦ Hom.app φ ⊤) h0) y)
    rw [hx, hy]⟩
  obtain ⟨e₁⟩ := nonempty_sections_higherDirectImage_iso_H f ℱ q
  have h₂ : Subsingleton (ℱ.H q) := e₁.symm.subsingleton
  obtain ⟨e₂⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated f U hU hU' ℱ q
  have h₃ : Subsingleton (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :=
    e₂.toEquiv.subsingleton
  have h₄ : Subsingleton (((TopCat.Presheaf.cechComplex U).obj ℱ.presheaf).homology q) :=
    (cechComplexHomologyAddEquiv U ℱ q).symm.subsingleton
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme.Modules
