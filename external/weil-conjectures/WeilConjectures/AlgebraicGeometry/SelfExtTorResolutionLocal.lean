/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluation
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.LocalTensorFiniteFreeZeroModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties

/-! # Local models of augmented self-Ext/self-Tor resolutions

Source: Stacks Project, Tags 0BQY, 068C and 08BS.
(blueprint: new-j3-self-ext-tor-local). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Local zero-differential models for the pullback of an augmented K-flat resolution,
and K-injectivity for the restriction of an augmented K-injective resolution.

Source: Stacks Project, Tag 0BQY (quotient Koszul computation), Tag 068C (affine
sheafification), and Tag 08BS (restriction of K-injective complexes).
(blueprint: new-j3-self-ext-tor-local).

Proof: Put A = Gamma(Y,U), I = ker(i)(U), and choose the finite Koszul-regular sequence
f supplied by hU. Its Koszul complex is a bounded finite-free projective resolution
of A/I. Sheafify its augmentation on U and identify tilde(A/I) with the restricted
pushforward of O_Z. The augmentation a identifies the restriction of P with the same
single quotient complex. Since P is K-flat with flat terms, its tensor pullback
computes the derived pullback, as does the sheafified Koszul resolution. Comparison
of these two resolutions in the localization gives a quasi-isomorphism roof between
the restriction of T and the sheafified Koszul complex tensored with A/I. Each f_j
vanishes in A/I, so the latter differential is zero. Its exterior-power terms are
finite free and it is supported in degrees -m through zero. Further restriction to
V and to its over site W is exact, preserves the quasi-isomorphisms in the roof,
and takes finite free modules to finite free modules. This proves the stated model
condition, with that restricted roof. Restriction of J to V, then to W, preserves
K-injectivity since each restriction is right adjoint to exact extension by zero.
The augmentation b identifies J as a resolution of O_Z; K-injectivity is a separate
explicit hypothesis, not a consequence of its homology. The proof applies to each
chart using the fixed global P and J. For an empty sequence the Koszul complex has
one term. Empty charts and zero quotients give zero models, so no nonempty or
proper-ideal assumption is required. -/
theorem selfExt_tor_resolution_local
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
      (SheafOfModules.unit Z.ringCatSheaf) ⟶ J)
    (_hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (_hflat : ∀ k : ℤ, SheafOfModules.IsFlat (P.X k))
    (_hb : QuasiIso b) (_hJ : J.IsKInjective) :
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
      let Fc := moduleOpenOverComplexFunctor Z V W
      CochainComplex.IsKInjective (Fc.obj J) ∧
        HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) := by
  dsimp
  intro V U hU
  let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
  constructor
  · let := _hJ
    let F := Scheme.Modules.restrictFunctor V.ι
    let G := SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let : F.Additive := inferInstance
    let : F.PreservesKInjectiveComplexes :=
      (openImmersion_restriction_derived_properties V.ι).2
    let Jv : CochainComplex V.toScheme.Modules ℤ := (F.mapHomologicalComplex (.up ℤ)).obj J
    let : CochainComplex.IsKInjective Jv := Functor.PreservesKInjectiveComplexes.isKInjective_map J
    have hzero : G.PreservesZeroMorphisms := by
      constructor
      intro M N
      ext A x
      rfl
    exact isKInjective_restrict_localized V.toScheme.ringCatSheaf W
      hzero Jv
  · exact local_tensor_has_finite_free_zero_model i P a _hP _hflat V U hU

end AlgebraicGeometry
