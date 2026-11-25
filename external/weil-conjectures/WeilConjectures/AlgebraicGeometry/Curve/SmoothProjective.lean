/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective


public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Varieties, projective morphisms and smooth projective curves

This file sets up the conventions of the curve-calculation chapter of the blueprint: varieties
and curves over a field, (H-)projective morphisms, the relative dimension of a morphism, and
smooth projective curves. It compares them with the curves of
`WeilConjectures/AlgebraicGeometry/Curve.lean` (`AlgebraicGeometry.IsCurve`,
`AlgebraicGeometry.IsConnectedCurve`), which are the curves of the smooth-curve chapter.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.relativeDimension`,
  `AlgebraicGeometry.Scheme.Hom.IsOfRelativeDimension`:
  the dimension of the fibres of a morphism.
- `AlgebraicGeometry.IsHProjective`, `AlgebraicGeometry.IsProjective`: H-projective and projective
  morphisms, given by a closed immersion into a projective space `ℙ(n; S)`.
- `AlgebraicGeometry.IsVariety`: an integral separated scheme of finite type over a field.
- `AlgebraicGeometry.IsIntegralCurve`: a variety of dimension one.
- `AlgebraicGeometry.IsSmoothProjectiveCurve`: a curve which is smooth and projective.

## Main statements

- `AlgebraicGeometry.IsHProjective.isProper`: H-projective morphisms are proper.
- `AlgebraicGeometry.IsSmoothProjectiveCurve.isConnectedCurve_and_smooth`: a smooth projective
  curve is a smooth proper connected curve in the sense of `AlgebraicGeometry.IsConnectedCurve`.
- `AlgebraicGeometry.IsSmoothProjectiveCurve.smoothOfRelativeDimension`: a smooth projective
  curve is smooth of relative dimension one.
- `AlgebraicGeometry.IsSmoothProjectiveCurve.finiteDimensional_H_one`,
  `AlgebraicGeometry.IsSmoothProjectiveCurve.arithmeticGenus_baseChangeField`,
  `AlgebraicGeometry.IsSmoothProjectiveCurve.genus_baseChangeField`: the genus of a smooth
  projective curve is finite, invariant under base change to a field extension, and agrees with
  the genus of the base change.
- `AlgebraicGeometry.IsSmoothProjectiveCurve.isConnectedCurve_baseChangeField`: the base change
  of a geometrically integral smooth projective curve to a field extension is a smooth proper
  connected curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section RelativeDimension

variable {X S : Scheme.{u}}

/-- The *relative dimension* of a morphism `f : X ⟶ S` at a point `s : S`: the dimension
`dim X_s` of the fibre `X_s = X ×_S Spec κ(s)`. It is `⊥` when the fibre is empty.

The *dimension* of a scheme is the Krull dimension `topologicalKrullDim` of its underlying space.

(blueprint: `def-pc-dimension`) -/
noncomputable def Scheme.Hom.relativeDimension (f : X ⟶ S) (s : S) : WithBot ℕ∞ :=
  topologicalKrullDim (f.fiber s)

/-- A morphism `f : X ⟶ S` is *of relative dimension `d`* if all its nonempty fibres have
dimension `d`.

(blueprint: `def-pc-dimension`) -/
def Scheme.Hom.IsOfRelativeDimension (f : X ⟶ S) (d : ℕ) : Prop :=
  ∀ s : S, Nonempty (f.fiber s) → f.relativeDimension s = d

/-- A morphism which is smooth of relative dimension `d` is of relative dimension `d`: each of
its fibres is smooth of relative dimension `d` over a field. -/
theorem Scheme.Hom.isOfRelativeDimension_of_smoothOfRelativeDimension (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] : f.IsOfRelativeDimension d := by
  intro s _
  have : SmoothOfRelativeDimension d (f.fiberToSpecResidueField s) :=
    inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd _ _))
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (f.fiberToSpecResidueField s) d

end RelativeDimension

section Projective

variable {X S : Scheme.{u}}







end Projective

section Curve

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A *variety* over a field `K` is an integral scheme `X` over `K` whose structure morphism
`f : X ⟶ Spec K` is separated and of finite type ("of finite type" being spelled as
`LocallyOfFiniteType` together with `QuasiCompact`).

(blueprint: `def-pc-curve`) -/
class IsVariety (f : X ⟶ Spec (.of K)) : Prop
    extends IsSeparated f, LocallyOfFiniteType f, QuasiCompact f where
  /-- A variety is integral. -/
  isIntegral : IsIntegral X

/-- A *curve* over a field `K` in the sense of the curve-calculation chapter: a variety over `K`
of dimension one. This differs from `AlgebraicGeometry.IsCurve`, the curves of the smooth-curve
chapter, which need not be integral; the two are compared in
`AlgebraicGeometry.IsIntegralCurve.isConnectedCurve`.

(blueprint: `def-pc-curve`, `rem-ptr-pc-curve-2`) -/
class IsIntegralCurve (f : X ⟶ Spec (.of K)) : Prop extends IsVariety f where
  /-- A curve has dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

/-- A *smooth projective curve* over a field `K`: a curve over `K` (in the sense of
`AlgebraicGeometry.IsIntegralCurve`) whose structure morphism is smooth and projective.

(blueprint: `def-pc-smooth-projective-curve`, `rem-ptr-pc-smooth-projective-curve-3`) -/
class IsSmoothProjectiveCurve (f : X ⟶ Spec (.of K)) : Prop
    extends IsIntegralCurve f, Smooth f, IsProjective f

attribute [instance] IsVariety.isIntegral

/-- **Integral curves are connected curves.** A curve over `K` in the sense of
`AlgebraicGeometry.IsIntegralCurve` (integral, separated, of finite type and of dimension one)
is a connected curve in the sense of `AlgebraicGeometry.IsConnectedCurve`: being irreducible it
is connected, and it is separated, of finite type and of dimension one. -/
instance (priority := 100) IsIntegralCurve.isConnectedCurve (f : X ⟶ Spec (.of K))
    [IsIntegralCurve f] : IsConnectedCurve f where
  krullDim_le_one := (IsIntegralCurve.topologicalKrullDim_eq_one (f := f)).le
  connectedSpace := inferInstance
  krullDim_eq_one := IsIntegralCurve.topologicalKrullDim_eq_one (f := f)

/-- **Smooth projective curves are smooth connected curves.** A smooth projective curve `X`
over a field `K` is a smooth connected curve: `X` is nonempty, connected, separated, of finite
type and of dimension one over `K`, and smooth over `K`. The blueprint states this over an
algebraically closed field, but the argument does not use it.

(blueprint: `lem-pc-curves-are-sc`) -/
theorem IsSmoothProjectiveCurve.isConnectedCurve_and_smooth (f : X ⟶ Spec (.of K))
    [IsSmoothProjectiveCurve f] : IsConnectedCurve f ∧ Smooth f ∧ IsProper f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A smooth projective curve over `K` is smooth of relative dimension one over `K`: it is
irreducible, smooth and of dimension one. -/
instance (priority := 100) IsSmoothProjectiveCurve.smoothOfRelativeDimension
    (f : X ⟶ Spec (.of K)) [IsSmoothProjectiveCurve f] : SmoothOfRelativeDimension 1 f :=
  (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
    (by exact_mod_cast IsIntegralCurve.topologicalKrullDim_eq_one (f := f))

end Curve

section GeneralCurve

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

variable [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]

variable (k C) in
/-- **The genus of a geometrically integral smooth projective curve is finite.** For a smooth
projective curve `C` over `k`, its genus `g(C) = dim_k H¹(C, 𝒪_C)`
(`AlgebraicGeometry.Scheme.arithmeticGenus`) is the dimension of a finite-dimensional
`k`-vector space, coherent cohomology of a proper scheme over a field being finite-dimensional.

(blueprint: `corollary-serre-duality-field-extension--2`) -/
theorem IsSmoothProjectiveCurve.finiteDimensional_H_one :
    FiniteDimensional k (Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1) :=
  have := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  have : (SheafOfModules.unit C.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit C.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  Scheme.Modules.finiteDimensional_H_of_isProper _ 1

variable (K : Type u) [Field K] [Algebra k K]

variable (k C) in
/-- **The genus is invariant under base change.** For a smooth projective curve `C` over `k` and
a field extension `K/k`, `g(C_K) = g(C)`, where `g = dim H¹(-, 𝒪)`: this is flat base change of
cohomology along `C_K ⟶ C`.

(blueprint: `corollary-serre-duality-field-extension--2`) -/
theorem IsSmoothProjectiveCurve.arithmeticGenus_baseChangeField :
    Scheme.arithmeticGenus K (C.baseChangeField k K) = Scheme.arithmeticGenus k C :=
  Scheme.arithmeticGenus_pullback K

/-- The base change of a smooth projective curve to a field extension is smooth of relative
dimension one. -/
instance IsSmoothProjectiveCurve.smoothOfRelativeDimension_baseChangeField :
    SmoothOfRelativeDimension 1 (C.baseChangeField k K ↘ Spec (.of K)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd _ _))

/-- The base change of a smooth projective curve to a field extension is proper. -/
instance IsSmoothProjectiveCurve.isProper_baseChangeField :
    IsProper (C.baseChangeField k K ↘ Spec (.of K)) :=
  inferInstanceAs (IsProper (pullback.snd _ _))

variable (k C) in
/-- **The genus of the base change.** For a smooth projective curve `C` over `k` and a field
extension `K/k`, the genus `dim_K Γ(C_K, Ω¹_{C_K/K})` of the smooth proper curve `C_K`
(`AlgebraicGeometry.Scheme.Hom.genus`, blueprint `prose-C-05`) is the genus
`g(C) = dim_k H¹(C, 𝒪_C)` of `C`.

(blueprint: `corollary-serre-duality-field-extension--2`) -/
theorem IsSmoothProjectiveCurve.genus_baseChangeField :
    (C.baseChangeField k K ↘ Spec (.of K)).genus = Scheme.arithmeticGenus k C :=
  Scheme.genus_eq_arithmeticGenus.trans (arithmeticGenus_baseChangeField k C K)

variable [GeometricallyIntegral (C ↘ Spec (.of k))]

/-- The base change of a geometrically integral smooth projective curve to a field extension is
integral. -/
instance IsSmoothProjectiveCurve.isIntegral_baseChangeField :
    IsIntegral (C.baseChangeField k K) :=
  pullback_of_geometrically (GeometricallyIntegral.geometrically_isIntegral
    (f := C ↘ Spec (.of k))) K _

variable (k C) in
/-- **Base change of a geometrically integral smooth projective curve.** For a geometrically
integral smooth projective curve `C` over `k` and a field extension `K/k` (in the blueprint,
algebraically closed), the base change `C_K` is a proper smooth connected curve over `K` in the
sense of `AlgebraicGeometry.IsConnectedCurve`, so that the degree and `Pic⁰` conventions of the
smooth-curve chapter apply to it.

(blueprint: `corollary-serre-duality-field-extension--2`) -/
theorem IsSmoothProjectiveCurve.isConnectedCurve_baseChangeField :
    IsConnectedCurve (C.baseChangeField k K ↘ Spec (.of K)) ∧
      Smooth (C.baseChangeField k K ↘ Spec (.of K)) ∧
      IsProper (C.baseChangeField k K ↘ Spec (.of K)) := by
  have hdim : topologicalKrullDim (C.baseChangeField k K) = 1 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (C.baseChangeField k K ↘ Spec (.of K)) 1
  have : IsCurve (C.baseChangeField k K ↘ Spec (.of K)) := ⟨hdim.le⟩
  exact ⟨⟨inferInstance, hdim⟩, SmoothOfRelativeDimension.smooth 1 _, inferInstance⟩

end GeneralCurve

end AlgebraicGeometry
