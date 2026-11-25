/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Ample families descend from the reduced subscheme in characteristic `p`

Say that a scheme `X` *has an ample family* if there are an invertible module `L` on `X` and
finitely many sections `s i : 𝒪_X ⟶ L` whose non-vanishing loci `X_{s i}` are affine and cover
`X`.

* Ample families pull back along affine morphisms: the non-vanishing locus of the pulled back
  section is the preimage of the non-vanishing locus
  (`exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom`).
* If `X` is quasi-compact and locally noetherian and a prime `p` vanishes on `X`, and the reduced
  subscheme `X_red` has an ample family, then so does `X` (Stacks 0BD4 (3)): some power of the
  absolute Frobenius of `X` kills the nilradical, hence factors through an affine morphism
  `X ⟶ X_red` along which the ample family pulls back
  (`exists_isAffineOpen_compl_support_zeroLocus_of_nilradical`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules in
/-- **Ample families pull back along affine morphisms.** If `f : X ⟶ Y` is affine and `Y` has an
invertible module `L` with finitely many sections `s i` whose non-vanishing loci are affine and
cover `Y`, then the pullbacks `f^* s i` of these sections to `f^* L` have the same property on
`X`: their non-vanishing loci are the preimages `f⁻¹ Y_{s i}`. -/
theorem exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    (h : ∃ (L : Y.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ Y.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ X.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤ := by
  obtain ⟨L, hL, ι, hι, s, hs, hcov⟩ := h
  have := IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  have hpre (i : ι) :
      (Hom.zeroLocus ((pullbackObjUnitIso f).inv ≫ (pullback f).map (s i))).support.compl =
        f ⁻¹ᵁ (s i).zeroLocus.support.compl := by
    rw [Hom.zeroLocus_eq_of_arrowIso _ ((pullback f).map (s i))
      (Arrow.isoMk (pullbackObjUnitIso f).symm (Iso.refl _)), ← Hom.comap_zeroLocus,
      Scheme.IdealSheafData.support_comap]
    rfl
  refine ⟨(pullback f).obj L, hL.pullback, ι, hι,
    fun i ↦ (pullbackObjUnitIso f).inv ≫ (pullback f).map (s i), fun i ↦ ?_, ?_⟩
  · rw [hpre]
    exact (hs i).preimage f
  · simp_rw [hpre, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]

open Scheme.Modules in
/-- **Ample families descend from the reduced subscheme in characteristic `p`** (Stacks 0BD4 (3)).
Let `X` be a quasi-compact locally noetherian scheme in which the prime `p` vanishes. If the
reduced subscheme `X_red` carries an invertible module with finitely many sections whose
non-vanishing loci are affine and cover `X_red`, then so does `X`. -/
@[stacks 0BD4]
theorem exists_isAffineOpen_compl_support_zeroLocus_of_nilradical {X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (h : ∃ (L : X.nilradical.subscheme.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L)
      (ι : Type u) (_ : Finite ι) (s : ι → (𝟙_ X.nilradical.subscheme.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ X.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤ := by
  obtain ⟨n, hn⟩ := X.exists_nilradical_le_ker_iterateFrobenius hp hX
  rw [← Scheme.IdealSheafData.ker_subschemeι X.nilradical] at hn
  have : IsAffineHom (IsClosedImmersion.lift _ _ hn ≫ X.nilradical.subschemeι) := by
    rw [IsClosedImmersion.lift_fac]
    infer_instance
  have : IsAffineHom (IsClosedImmersion.lift _ _ hn) := .of_comp _ X.nilradical.subschemeι
  exact exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom
    (IsClosedImmersion.lift _ _ hn) h

end AlgebraicGeometry
