/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Limit
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Zariski's Main Theorem: the finite factorization

Mathlib's `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` proves Grothendieck's form of
Zariski's Main Theorem: a separated, quasi-compact, locally quasi-finite morphism `f: X ⟶ S`
locally of finite type factors as an open immersion into the relative normalization of `S` in
`X` followed by an integral morphism. Over a quasi-compact quasi-separated base we deduce the
factorization through a *finite* `S`-scheme (Stacks Project Tag 05K0), by writing the relative
normalization as a cofiltered limit of finite `S`-schemes
(`AlgebraicGeometry.Scheme.Hom.nonempty_finiteApproximation_of_isIntegralHom`) and descending
the open immersion to a finite stage. If `f` is moreover locally of finite presentation, the
finite `S`-scheme can be chosen of finite presentation (Stacks Project Tag 0F2N).

## Main results

- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion`:
  a quasi-compact open of a limit of finite `S`-schemes is open in a closed subscheme of some
  stage.
- `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`:
  **Zariski's Main Theorem**, finite factorization (Stacks Project Tag 05K0).
- `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation`:
  the finitely presented refinement (Stacks Project Tag 0F2N).

## References

* Stacks Project, Tags 05K0 and 0F2N
* Stacks Project, Tags 01Z4, 081B and 01QV (descent of the immersion to a finite stage)
* Stacks Project, Tags 09YZ, 09ZQ and 01PF (finite and finitely presented approximation)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Descent of the immersion to a finite stage**.
Let `ν: N ⟶ S` be presented as a cofiltered limit of finite `S`-schemes `T_λ`, with `S`
quasi-compact and quasi-separated, and let `ι: X ⟶ N` be a quasi-compact open immersion with
`X` locally of finite type over `S`. Then there are an index `λ₀` and a factorization
`X ⟶ T ⟶ T_{λ₀}` of `X ⟶ N ⟶ T_{λ₀}` into a quasi-compact open immersion followed by a closed
immersion. If `S` is locally Noetherian, `T_{λ₀}` is moreover of finite presentation over `S`. -/
theorem Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion
    {X N S : Scheme.{u}} {ν : N ⟶ S} (F : ν.FiniteApproximation) [CompactSpace S]
    [QuasiSeparatedSpace S] (ι : X ⟶ N) [IsOpenImmersion ι] [QuasiCompact ι]
    [LocallyOfFiniteType (ι ≫ ν)] :
    ∃ (i : F.I) (T : Scheme.{u}) (j : X ⟶ T) (k : T ⟶ F.D.obj i), IsOpenImmersion j ∧
      QuasiCompact j ∧ IsClosedImmersion k ∧ j ≫ k = ι ≫ F.π.app i ∧
      (IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p i)) := by
  have : CompactSpace N := Scheme.compactSpace_of_isLimit F.D _ F.isLimit
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace ι
  have (i : F.I) : LocallyOfFiniteType (ι ≫ (Cone.mk N F.π).π.app i ≫ F.p i) := by
    change LocallyOfFiniteType (ι ≫ F.π.app i ≫ F.p i)
    rw [F.π_p]; infer_instance
  obtain ⟨i, U, g, hU, hg, hgU⟩ :=
    Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit F.isLimit F.p ι
  have : QuasiCompact U.ι := U.quasiCompact_ι hU
  let h := g ≫ U.ι
  have : QuasiCompact h.toImage := QuasiCompact.of_comp h.toImage h.imageι
  refine ⟨i, h.image, h.toImage, h.imageι, inferInstance, inferInstance, inferInstance, ?_,
    fun _ ↦ inferInstance⟩
  rw [Scheme.Hom.toImage_imageι]
  exact hgU

/-- **Zariski's Main Theorem, finite factorization**. A separated, quasi-compact, locally
quasi-finite morphism `f : X ⟶ S` locally of finite type to a quasi-compact quasi-separated scheme
factors as a quasi-compact open immersion `j : X ⟶ T` followed by a finite morphism `p : T ⟶ S`.
-/
@[stacks 05K0]
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ j ≫ p = f := by
  obtain ⟨F⟩ := f.fromNormalization.nonempty_finiteApproximation_of_isIntegralHom
  have : LocallyOfFiniteType (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]; infer_instance
  obtain ⟨i, T, j, k, hj, hjc, hk, hjk, -⟩ := F.exists_isOpenImmersion_isClosedImmersion
    f.toNormalization
  refine ⟨T, j, k ≫ F.p i, hj, hjc, inferInstance, ?_⟩
  rw [reassoc_of% hjk, F.π_p, f.toNormalization_fromNormalization]

/-- **Zariski's Main Theorem, finitely presented finite factorization**. A separated,
quasi-compact, locally quasi-finite morphism `f : X ⟶ S` locally of finite presentation to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion `j : X ⟶ T`
followed by a finite morphism `p : T ⟶ S` of finite presentation. -/
@[stacks 0F2N]
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ LocallyOfFinitePresentation p ∧ j ≫ p = f := by
  obtain ⟨T₀, j₀, p₀, hj₀, hj₀c, hp₀, hjp₀⟩ :=
    f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace T₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  have : QuasiSeparatedSpace T₀ := quasiSeparatedSpace_of_quasiSeparated p₀
  obtain ⟨A⟩ := p₀.nonempty_finitePresentationApproximation
  obtain ⟨K, hK⟩ := Scheme.exists_isFinite_of_isLimit A.D _ A.isLimit (fun K ↦ A.p.app K)
    (fun g ↦ (A.p.naturality g).trans (Category.comp_id _)) p₀ A.w
  let ι := j₀ ≫ A.π.app K
  have : IsImmersion ι := inferInstance
  obtain ⟨U, g, hU, hg, hgU⟩ := ι.exists_isCompact_isClosedImmersion
  have hgf : g ≫ U.ι ≫ A.p.app K = f := by
    rw [reassoc_of% hgU, Category.assoc, A.w, hjp₀]
  have : LocallyOfFinitePresentation (g ≫ U.ι ≫ A.p.app K) := by rw [hgf]; infer_instance
  have := locallyOfFinitePresentation_of_comp g (U.ι ≫ A.p.app K)
  obtain ⟨J, hJ, hJU⟩ := Scheme.IdealSheafData.exists_finiteType_comap_eq U hU g.ker
    (fun V _ ↦ g.fg_ideal_ker V)
  have : LocallyOfFinitePresentation J.subschemeι :=
    Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι fun V ↦ hJ V le_top
  have hker : (pullback.fst U.ι J.subschemeι).ker = g.ker := hJU
  have := IsClosedImmersion.isIso_lift (pullback.fst U.ι J.subschemeι) g hker
  let e := IsClosedImmersion.lift (pullback.fst U.ι J.subschemeι) g hker.le
  have : QuasiCompact U.ι := U.quasiCompact_ι hU
  refine ⟨J.subscheme, e ≫ pullback.snd U.ι J.subschemeι, J.subschemeι ≫ A.p.app K,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition_assoc, IsClosedImmersion.lift_fac_assoc, hgf]

end AlgebraicGeometry
