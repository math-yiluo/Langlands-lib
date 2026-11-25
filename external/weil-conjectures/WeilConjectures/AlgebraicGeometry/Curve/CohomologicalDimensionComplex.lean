/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.GenericCohomologicalDimension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion

/-!
# Cohomological dimension of a curve: complexes and variants

Let `C` be a curve over an algebraically closed field `k`. The étale cohomology of a torsion
sheaf on `C` vanishes in degrees `≥ 3`
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`). This file deduces the
corresponding statement for complexes: for a bounded complex `K` of étale abelian sheaves with
torsion cohomology sheaves and `𝓗ⁱ(K) = 0` for `i > b`, the hypercohomology
`Hᵠ(C, K) = Hom_{D(C_ét)}(ℤ, K[q])` vanishes for `q > b + 2`. It also records the
notion of a curve coefficient pair.

## Main definitions

- `AlgebraicGeometry.IsCurveCoefficientPair`: a curve over an algebraically closed field
  together with a torsion étale sheaf on it.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_shiftedHom_of_isGE_of_isLE`: vanishing of the
  hypercohomology of bounded complexes with torsion cohomology sheaves in degrees `> b + 2`.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_lt_of_smooth`: the sheaf case
  for smooth connected curves.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

instance : ObjectProperty.IsClosedUnderIsomorphisms
    (fun F : Sheaf J AddCommGrpCat.{w} ↦ F.IsTorsion) where
  of_iso e h := h.of_iso e

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- Blueprint `theorem-cohomology-curves`: **curve coefficient pairs.** Let `k` be an
algebraically closed field and `f : C ⟶ Spec k` a curve, that is, a separated morphism of
finite type with `dim C ≤ 1` (`AlgebraicGeometry.IsCurve`). A pair `(C, F)` of such a curve
and a torsion abelian étale sheaf `F` on `C` is a *curve coefficient pair*.
(blueprint: `theorem-cohomology-curves`) -/
structure IsCurveCoefficientPair (f : C ⟶ Spec (.of k))
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop where
  /-- The base field is algebraically closed. -/
  isAlgClosed : IsAlgClosed k
  /-- `C` is a curve over `k`. -/
  isCurve : IsCurve f
  /-- The coefficient sheaf is a torsion sheaf. -/
  isTorsion : F.IsTorsion

/-- The cohomology of a curve coefficient pair vanishes in degrees `≥ 3`
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`). -/
lemma IsCurveCoefficientPair.subsingleton_sheafH {f : C ⟶ Spec (.of k)}
    {F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}} (h : IsCurveCoefficientPair f F)
    (q : ℕ) (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) :=
  have := h.isAlgClosed
  have := h.isCurve
  IsCurve.subsingleton_sheafH_of_three_le f F h.isTorsion q hq

variable [IsAlgClosed k]

/-- Blueprint `theorem-cohomology-curves--1`: **cohomological dimension of a smooth curve.**
For a smooth separated connected curve `C` over an algebraically closed field and any torsion
étale sheaf `F` on `C`, `Hᵠ(C, F) = 0` for `q > 2`. A smooth connected curve is integral, and
the argument at the generic point of
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_isIntegral` applies; smoothness is
not needed for it.
(blueprint: `theorem-cohomology-curves--1`) -/
theorem IsConnectedCurve.subsingleton_sheafH_of_two_lt_of_smooth (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) (hq : 2 < q) : Subsingleton (Sheaf.H F q) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  exact IsCurve.subsingleton_sheafH_of_three_le_of_isIntegral f F hF q hq

/-- **Vanishing in high degrees, complex form.** Let `C` be a curve over an algebraically
closed field `k` and `K` a bounded complex of abelian étale sheaves on `C` (an object of the
derived category whose cohomology sheaves `𝓗ⁱ(K)` vanish outside `[a, b]`) all of whose
cohomology sheaves are torsion. Then the hypercohomology
`Hᵠ(C, K) = Hom_{D(C_ét)}(ℤ, K[q])` vanishes for `q > b + 2`.

The proof is by induction on the amplitude of `K`, using the truncation triangles
`τ_{< b} K ⟶ K ⟶ 𝓗ᵇ(K)[-b] ⟶` of the canonical t-structure and the sheaf case
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`; this replaces the
hypercohomology spectral sequence of the blueprint proof.
(blueprint: `theorem-cohomology-curves`) -/
theorem IsCurve.subsingleton_shiftedHom_of_isGE_of_isLE (f : C ⟶ Spec (.of k)) [IsCurve f]
    [HasDerivedCategory.{w} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (K : DerivedCategory (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})) (a b : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsTorsion) (q : ℤ) (hq : b + 2 < q) :
    Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))) K q) :=
  DerivedCategory.subsingleton_shiftedHom_of_ext _ (fun F ↦ F.IsTorsion) 3
    (fun Y hY m hm ↦ IsCurve.subsingleton_sheafH_of_three_le f Y hY m hm) K a b
    (fun i _ ↦ hK i) q (by lia)

/-- **Vanishing in high degrees, complex form, for `D^b`.** Let `C` be a curve over an
algebraically closed field `k` and `K` an object of the bounded derived category of abelian
étale sheaves on `C` with torsion cohomology sheaves, and with `𝓗ⁱ(K) = 0` for `i > b`. Then
`Hᵠ(C, K) = Hom_{D(C_ét)}(ℤ, K[q])` vanishes for `q > b + 2`. The shift by `b` cannot be
dropped: `(ℤ/2)[-3]` on `ℙ¹` has `H³ = H⁰(ℙ¹, ℤ/2) ≠ 0`. -/
theorem IsCurve.subsingleton_shiftedHom_of_bounded (f : C ⟶ Spec (.of k)) [IsCurve f]
    [HasDerivedCategory.{w} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (K : DerivedCategory (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hKb : DerivedCategory.TStructure.t.bounded K) (b : ℤ) [K.IsLE b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsTorsion) (q : ℤ) (hq : b + 2 < q) :
    Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))) K q) := by
  obtain ⟨⟨a, ha⟩, -⟩ := hKb
  exact IsCurve.subsingleton_shiftedHom_of_isGE_of_isLE f K a b hK q hq

end AlgebraicGeometry
