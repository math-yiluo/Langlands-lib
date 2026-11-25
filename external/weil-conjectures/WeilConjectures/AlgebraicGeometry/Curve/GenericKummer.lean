/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityCohomology
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.GenericKummer

/-!
# The generic Kummer residue sheaf of a smooth curve

Let `C` be a smooth integral separated connected curve over a field `k`, with generic point
`η : Spec k(C) ⟶ C`, and let `n` be invertible in `k`. Then the valuations at the closed points
give an isomorphism `R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n`
(`AlgebraicGeometry.IsConnectedCurve.genericKummerResidueIso`). The field `k` need not be
algebraically closed.

This is the case of a curve of `AlgebraicGeometry.Scheme.genericKummerResidueIso`, which holds
for every integral regular noetherian scheme of dimension one: a smooth curve is regular
(`AlgebraicGeometry.IsRegular.of_smooth`) and noetherian, and a connected curve has dimension
one.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- A curve is noetherian. -/
lemma IsCurve.isNoetherian (f : C ⟶ Spec (.of k)) [IsCurve f] : IsNoetherian C :=
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  ⟨⟩

variable (f : C ⟶ Spec (.of k)) [Smooth f] [IsConnectedCurve f] [IsIntegral C] {n : ℕ}
  (hn : (n : k) ≠ 0)
  (c : Cofan fun x : {x : C // IsClosed ({x} : Set C)} ↦ C.pointConstantZMod n x.1)
  (hc : IsColimit c)

namespace IsConnectedCurve

/-- **The generic Kummer residue sheaf of a smooth curve**. Let `C` be a smooth integral separated
connected curve over a field `k`, with generic point `η : Spec k(C) ⟶ C`, and let `n` be invertible
in `k`. Then

```
  R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n,
```

where `R¹η_*` is the first right derived functor of the direct image `η_*` on abelian étale
sheaves, `μₙ` is the sheaf of `n`-th roots of unity of `Spec k(C)`, `i_x : Spec κ(x) ⟶ C` is the
inclusion of a closed point and the direct sum is the vertex of any colimit cofan `c`. The
isomorphism is given by the valuations at the closed points
(`AlgebraicGeometry.IsConnectedCurve.genericKummerResidueIso_spec`). -/
def genericKummerResidueIso :
    ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).rightDerived 1).obj
      ((Spec C.functionField).rootsOfUnitySheaf n) ≅ c.pt :=
  haveI := IsCurve.isNoetherian f
  haveI := IsRegular.of_smooth f
  Scheme.genericKummerResidueIso (IsConnectedCurve.krullDim_eq_one (f := f))
    (Scheme.isUnit_natCast_of_ne_zero f hn) c hc

/-- **The generic Kummer residue isomorphism of a smooth curve is given by valuations**: composed
with the Kummer coboundary `η_* 𝔾ₘ ⟶ R¹η_* μₙ`, it is the divisor map `f ↦ ∑_x ord_x(f) [x]`
followed by reduction modulo `n`. Here `cD` is any colimit cofan on the family `x ↦ i_{x*} ℤ` of
points of codimension one, which are the closed points of `C`. -/
lemma genericKummerResidueIso_spec
    (cD : Cofan fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantInt x.1)
    (hcD : IsColimit cD) :
    haveI := IsCurve.isNoetherian f
    haveI := IsRegular.of_smooth f
    C.genericGmIso.hom ≫ Scheme.genericKummerδ n (Scheme.isUnit_natCast_of_ne_zero f hn) ≫
        (genericKummerResidueIso f hn c hc).hom =
      C.divisorSequenceMap cD hcD ≫
        Scheme.divisorsModNMap n (IsConnectedCurve.krullDim_eq_one (f := f)) cD hcD c :=
  haveI := IsCurve.isNoetherian f
  haveI := IsRegular.of_smooth f
  Scheme.genericKummerResidueIso_spec _ _ c hc cD hcD

end IsConnectedCurve

end AlgebraicGeometry

end
