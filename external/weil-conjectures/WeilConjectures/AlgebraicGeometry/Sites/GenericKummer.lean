/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FirstCokernel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# The generic Kummer residue sheaf

Let `X` be an integral regular noetherian scheme of dimension one (for instance a smooth
connected curve over a field), with generic point `η : Spec k(X) ⟶ X`, and let `n` be invertible
on `X`. Then the valuations at the closed points give an isomorphism

```
  R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n
```

of étale sheaves on `X`, where `μₙ` is the sheaf of `n`-th roots of unity on `Spec k(X)` and
`i_x : Spec κ(x) ⟶ X` is the inclusion of a closed point.

## Main definitions

- `AlgebraicGeometry.Scheme.pointConstantZMod`: the sheaf `i_{x*} ℤ/n` of a point `x`.
- `AlgebraicGeometry.Scheme.genericKummerResidueIso`: the isomorphism
  `R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n`.

## Main statements

- `AlgebraicGeometry.Scheme.isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField`:
  `R¹η_* 𝔾ₘ = 0`.
- `AlgebraicGeometry.Scheme.genericKummerResidueIso_spec`: the isomorphism is given by the
  valuations.

## Implementation details

We argue on sheaves rather than on stalks. The Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` on
`Spec k(X)` and `R¹η_* 𝔾ₘ = 0` (Hilbert 90, see
`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`) identify `R¹η_* μₙ`
with the cokernel of multiplication by `n` on `η_* 𝔾ₘ`, the quotient map being the Kummer
coboundary. The divisor sequence
`0 ⟶ 𝔾ₘ ⟶ η_* 𝔾ₘ ⟶ ⨁_x i_{x*} ℤ ⟶ 0` (`AlgebraicGeometry.Scheme.shortExact_divisorSequence`),
on whose first term multiplication by `n` is an epimorphism by the Kummer sequence on `X`,
identifies this cokernel with the cokernel of `n` on `⨁_x i_{x*} ℤ`, which is
`⨁_x i_{x*} ℤ/n` since each `i_{x*}` is exact (`i_x` is a closed immersion). The resulting
isomorphism sends the Kummer class of a rational function `f` to `∑_x (ord_x f mod n) [x]`
(`AlgebraicGeometry.Scheme.genericKummerResidueIso_spec`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Order

noncomputable section

namespace AddCommGrpCat

variable (n : ℕ)

@[simp]
lemma uliftIntToZMod_apply (a : ULift.{u + 1} ℤ) :
    uliftIntToZMod.{u + 1} n a = ULift.up ((a.down : ℤ) : ZMod n) :=
  rfl

@[reassoc (attr := simp)]
lemma nsmul_id_comp_uliftIntToZMod :
    (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ uliftIntToZMod.{u + 1} n = 0 := by
  ext a
  simp

/-- The reduction map `ℤ ⟶ ℤ/n` is a cokernel of multiplication by `n` on `ℤ`. -/
def isColimitUliftIntToZMod :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_uliftIntToZMod.{u} n)) := by
  let S := ShortComplex.mk _ _ (nsmul_id_comp_uliftIntToZMod.{u} n)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have ha : ((a.down : ℤ) : ZMod n) = 0 := congrArg ULift.down ha
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ha
    exact ⟨ULift.up b, ULift.ext (by simp [S, hb])⟩
  have : Epi S.g := (AddCommGrpCat.epi_iff_surjective _).2 fun a ↦
    ⟨ULift.up (a.down : ZMod n).valMinAbs, ULift.ext (ZMod.coe_valMinAbs (a.down : ZMod n))⟩
  exact hS.gIsCokernel

end AddCommGrpCat

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (n : ℕ)

section PointSheaf

/-- The étale sheaf `i_{x*} ℤ/n` on `X`: the pushforward of the constant sheaf `ℤ/n` along the
canonical morphism `i_x : Spec κ(x) ⟶ X` of a point `x` of `X`. -/
def pointConstantZMod (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((Spec (X.residueField x)).constantZMod n)

/-- The reduction map `i_{x*} ℤ ⟶ i_{x*} ℤ/n`. -/
def pointConstantIntToZMod (x : X) : X.pointConstantInt x ⟶ X.pointConstantZMod n x :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
    ((constantSheaf _ AddCommGrpCat.{u + 1}).map (AddCommGrpCat.uliftIntToZMod.{u + 1} n))

@[reassoc (attr := simp)]
lemma nsmul_id_comp_pointConstantIntToZMod (x : X) :
    (n • 𝟙 (X.pointConstantInt x)) ≫ X.pointConstantIntToZMod n x = 0 := by
  have : n • 𝟙 (X.pointConstantInt x) =
      (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
        ((constantSheaf _ AddCommGrpCat.{u + 1}).map (n • 𝟙 _)) := by
    simp [pointConstantInt]
  rw [this, pointConstantIntToZMod, ← Functor.map_comp, ← Functor.map_comp,
    AddCommGrpCat.nsmul_id_comp_uliftIntToZMod, Functor.map_zero, Functor.map_zero]

/-- At a closed point `x`, the reduction map `i_{x*} ℤ ⟶ i_{x*} ℤ/n` is a cokernel of
multiplication by `n`. -/
def isColimitPointConstantIntToZMod {x : X} (hx : IsClosed ({x} : Set X)) :
    IsColimit (CokernelCofork.ofπ _ (X.nsmul_id_comp_pointConstantIntToZMod n x)) :=
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  Functor.isColimitCokernelCoforkNSMulMap n _
    (Functor.isColimitCokernelCoforkNSMulMap n _ (AddCommGrpCat.isColimitUliftIntToZMod.{u} n))

end PointSheaf

section Dimension

variable {X}

/-- On an integral scheme of dimension one, the points of codimension one are the closed
points. -/
lemma coheight_eq_one_iff_isClosed [IsIntegral X] (hX : topologicalKrullDim X = 1) (x : X) :
    coheight x = 1 ↔ IsClosed ({x} : Set X) := by
  constructor
  · intro hx
    refine closure_subset_iff_isClosed.1 fun y hy ↦ ?_
    rw [← specializes_iff_mem_closure] at hy
    by_contra hne
    have hlt : y < x := lt_of_le_not_ge (le_iff_specializes.2 hy) fun h ↦
      hne (Set.mem_singleton_iff.2 (hy.antisymm (le_iff_specializes.1 h)).eq.symm)
    have h₁ := coheight_add_one_le hlt
    have h₂ : (coheight y : WithBot ℕ∞) ≤ 1 := hX ▸ coheight_le_topologicalKrullDim y
    have h₂ : coheight y ≤ 1 := by exact_mod_cast h₂
    rw [hx] at h₁
    exact absurd (h₁.trans h₂) (by decide)
  · intro hx
    have hle : (coheight x : WithBot ℕ∞) ≤ 1 := hX ▸ coheight_le_topologicalKrullDim x
    have hne : coheight x ≠ 0 := by
      intro h0
      have hmax : IsMax x := Order.coheight_eq_zero.1 h0
      have h₁ : x ≤ genericPoint X :=
        le_iff_specializes.2 ((genericPoint_spec X).specializes (Set.mem_univ x))
      have h₂ : genericPoint X = x :=
        ((le_iff_specializes.1 h₁).antisymm (le_iff_specializes.1 (hmax h₁))).eq
      have hu : (Set.univ : Set X) = {x} := by
        rw [← genericPoint_spec X, h₂, hx.closure_eq]
      have : Subsingleton X := ⟨fun a b ↦ by
        have ha : a ∈ ({x} : Set X) := hu ▸ Set.mem_univ a
        have hb : b ∈ ({x} : Set X) := hu ▸ Set.mem_univ b
        rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]⟩
      have h₃ := topologicalKrullDim_zero_of_discreteTopology X
      rw [hX] at h₃
      exact absurd h₃ (by decide)
    have hle' : coheight x ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (Order.one_le_iff_ne_zero.2 hne)

end Dimension

section Generic

variable [IsIntegral X] [IsNoetherian X] [IsRegular X]

/-- **`R¹η_* 𝔾ₘ = 0` along the generic point** `η : Spec k(X) ⟶ X` of an integral regular
noetherian scheme, for the right derived functors of `η_*` on abelian étale sheaves. This is
`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf` (Hilbert 90 on the
generic fibres of affine étale `X`-schemes), read through
`CategoryTheory.Functor.isZero_rightDerived_one_of_epi_map`. -/
theorem isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived 1).obj
      (Spec X.functionField).gmSheaf) := by
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf
  have := X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf (Injective.ι G)
  have h := (Etale.lowerStar AddCommGrpCat.{u + 1}
    X.fromSpecFunctionField).isZero_rightDerived_one_of_epi_map (Injective.ι G)
  have := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  exact h.of_iso (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived
    1).mapIso (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField)).symm)

variable {X n}

omit [IsNoetherian X] [IsRegular X] in
/-- An integer invertible on `X` is invertible on the generic point of `X`. -/
lemma isUnit_natCast_functionField (hn : IsUnit (n : Γ(X, ⊤))) :
    IsUnit (n : Γ(Spec X.functionField, ⊤)) := by
  simpa using hn.map X.fromSpecFunctionField.appTop.hom

omit [IsNoetherian X] [IsRegular X] in
variable (n) in
/-- The direct image of the `n`-th power map of `𝔾ₘ` is the `n`-th power map. -/
lemma lowerStar_map_kummerSequence_g :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map
      ((Spec X.functionField).kummerSequence n).g = n • 𝟙 ((Etale.lowerStar AddCommGrpCat.{u + 1}
        X.fromSpecFunctionField).obj (Spec X.functionField).gmSheaf) := by
  change (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map
    (n • 𝟙 (Spec X.functionField).gmSheaf) = _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]

omit [IsNoetherian X] [IsRegular X] in
variable (n) in
/-- The Kummer coboundary `η_* 𝔾ₘ ⟶ R¹η_* μₙ` along the generic point `η : Spec k(X) ⟶ X`: the
connecting morphism of the long exact sequence of the right derived functors of `η_*` attached
to the Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` on `Spec k(X)`. On the sections over an étale
`X`-scheme `V`, it is classically described as sending a rational function on `V` to its
Kummer class. -/
def genericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived 1).obj
        ((Spec X.functionField).rootsOfUnitySheaf n) :=
  ((Spec X.functionField).kummerSequence_shortExact n
    (isUnit_natCast_functionField hn)).rightDerivedZeroδ _

omit [IsNoetherian X] [IsRegular X] in
@[reassoc (attr := simp)]
lemma nsmul_id_comp_genericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    (n • 𝟙 _) ≫ genericKummerδ n hn = 0 := by
  have := ((Spec X.functionField).kummerSequence_shortExact n
    (isUnit_natCast_functionField hn)).map_g_comp_rightDerivedZeroδ
      (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField)
  rwa [lowerStar_map_kummerSequence_g] at this

/-- **`R¹η_* μₙ` is the cokernel of `n` on `η_* 𝔾ₘ`**, the quotient map being the Kummer
coboundary. -/
def isColimitGenericKummerδ (hn : IsUnit (n : Γ(X, ⊤))) :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_genericKummerδ hn)) :=
  CokernelCofork.isColimitOfEq (lowerStar_map_kummerSequence_g n)
    (((Spec X.functionField).kummerSequence_shortExact n
      (isUnit_natCast_functionField hn)).isColimitCokernelCoforkRightDerivedZeroδ _
        (X.isZero_rightDerived_one_lowerStar_gmSheaf_fromSpecFunctionField))

section Divisors

variable (hX : topologicalKrullDim X = 1)

omit [IsNoetherian X] [IsRegular X] in
include hX in
/-- On an integral scheme of dimension one, the points of codimension one are the closed
points. -/
def coheightOneEquivClosedPoints :
    {x : X // coheight x = 1} ≃ {x : X // IsClosed ({x} : Set X)} :=
  Equiv.subtypeEquivRight (coheight_eq_one_iff_isClosed hX)

variable (n)
  (cD : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hcD : IsColimit cD)
  (c : Cofan fun x : {x : X // IsClosed ({x} : Set X)} ↦ X.pointConstantZMod n x.1)

omit [IsNoetherian X] [IsRegular X] in
/-- The reduction map `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ ⟶ ⨁_{x closed} i_{x*} ℤ/n` of an integral scheme of
dimension one, between the vertices of a colimit cofan `cD` and of a cofan `c`. -/
def divisorsModNMap : cD.pt ⟶ c.pt :=
  Cofan.IsColimit.desc hcD fun x ↦
    X.pointConstantIntToZMod n x.1 ≫ c.inj (coheightOneEquivClosedPoints hX x)

omit [IsNoetherian X] [IsRegular X] in
@[reassoc (attr := simp)]
lemma inj_divisorsModNMap (x : {x : X // coheight x = 1}) :
    cD.inj x ≫ divisorsModNMap n hX cD hcD c =
      X.pointConstantIntToZMod n x.1 ≫ c.inj (coheightOneEquivClosedPoints hX x) :=
  Cofan.IsColimit.fac _ _ _

omit [IsNoetherian X] [IsRegular X] in
@[reassoc (attr := simp)]
lemma nsmul_id_comp_divisorsModNMap :
    (n • 𝟙 cD.pt) ≫ divisorsModNMap n hX cD hcD c = 0 := by
  refine Cofan.IsColimit.hom_ext hcD _ _ fun x ↦ ?_
  rw [Limits.comp_zero, ← nsmul_id_comp_eq_comp_nsmul_id_assoc, inj_divisorsModNMap,
    nsmul_id_comp_pointConstantIntToZMod_assoc, Limits.zero_comp]

omit [IsNoetherian X] [IsRegular X] in
/-- The reduction map `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ ⟶ ⨁_{x closed} i_{x*} ℤ/n` is a cokernel of
multiplication by `n`. -/
def isColimitDivisorsModNMap (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 cD.pt) (divisorsModNMap n hX cD hcD c)
      (nsmul_id_comp_divisorsModNMap n hX cD hcD c)) :=
  Cofan.IsColimit.isColimitCokernelCoforkNSMul n hcD
    (Cofan.isColimitReindex (coheightOneEquivClosedPoints hX) hc)
    (fun x ↦ X.pointConstantIntToZMod n x.1) (fun x ↦ X.nsmul_id_comp_pointConstantIntToZMod n x.1)
    (fun x ↦ X.isColimitPointConstantIntToZMod n (coheightOneEquivClosedPoints hX x).2)

variable {n}

/-- The divisor map followed by reduction modulo `n`,
`η_* 𝔾ₘ ⟶ ⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ ⟶ ⨁_{x closed} i_{x*} ℤ/n`, is a cokernel of multiplication by
`n` on `η_* 𝔾ₘ`. -/
def isColimitDivisorSequenceMapComp (hn : IsUnit (n : Γ(X, ⊤))) (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 X.genericGm)
      (X.divisorSequenceMap cD hcD ≫ divisorsModNMap n hX cD hcD c) (by
        rw [nsmul_id_comp_eq_comp_nsmul_id_assoc, nsmul_id_comp_divisorsModNMap,
          Limits.comp_zero])) :=
  have : Epi (n • 𝟙 X.gmSheaf) := (X.kummerSequence_shortExact n hn).epi_g
  (X.shortExact_divisorSequence cD hcD).isColimitCokernelCoforkNSMul n
    (isColimitDivisorsModNMap n hX cD hcD c hc)

/-- The composite of the divisor map with any map out of `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ` does not
depend on the choice of the colimit cofan. -/
lemma divisorSequenceMap_comp_desc {W : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : ∀ x : {x : X // coheight x = 1}, X.pointConstantInt x.1 ⟶ W)
    (cD' : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1)
    (hcD' : IsColimit cD') :
    X.divisorSequenceMap cD hcD ≫ Cofan.IsColimit.desc hcD g =
      X.divisorSequenceMap cD' hcD' ≫ Cofan.IsColimit.desc hcD' g := by
  let e := hcD.coconePointUniqueUpToIso hcD'
  have he (x : {x : X // coheight x = 1}) : cD.inj x ≫ e.hom = cD'.inj x :=
    hcD.comp_coconePointUniqueUpToIso_hom hcD' ⟨x⟩
  have h₁ : X.divisorSequenceMap cD hcD ≫ e.hom = X.divisorSequenceMap cD' hcD' := by
    have : e.hom ≫ X.divisorsToPointFunctionSheaf cD' hcD' =
        X.divisorsToPointFunctionSheaf cD hcD :=
      Cofan.IsColimit.hom_ext hcD _ _ fun x ↦ by
        rw [reassoc_of% (he x), divisorsToPointFunctionSheaf, divisorsToPointFunctionSheaf,
          Cofan.IsColimit.fac, Cofan.IsColimit.fac]
    rw [← cancel_mono (X.divisorsToPointFunctionSheaf cD' hcD'), Category.assoc, this,
      divisorSequenceMap_comp, divisorSequenceMap_comp]
  have h₂ : Cofan.IsColimit.desc hcD g = e.hom ≫ Cofan.IsColimit.desc hcD' g :=
    Cofan.IsColimit.hom_ext hcD _ _ fun x ↦ by
      rw [Cofan.IsColimit.fac, reassoc_of% (he x), Cofan.IsColimit.fac]
  rw [h₂, ← Category.assoc, h₁]

end Divisors

section Iso

variable (hX : topologicalKrullDim X = 1) (hn : IsUnit (n : Γ(X, ⊤)))
  (c : Cofan fun x : {x : X // IsClosed ({x} : Set X)} ↦ X.pointConstantZMod n x.1)
  (hc : IsColimit c)

/-- **The generic Kummer residue sheaf**. Let `X` be an integral regular noetherian scheme of
dimension one, for instance a smooth connected curve over a field, with generic point
`η : Spec k(X) ⟶ X`, and let `n` be invertible on `X`. Then

```
  R¹η_* μₙ ≅ ⨁_{x closed} i_{x*} ℤ/n,
```

where `R¹η_*` is the first right derived functor of the direct image `η_*` on abelian étale
sheaves, `μₙ` is the sheaf of `n`-th roots of unity of `Spec k(X)`, `i_x : Spec κ(x) ⟶ X` is
the inclusion of a closed point and the direct sum is the vertex of any colimit cofan `c`.

The isomorphism is given by the valuations at the closed points: it sends the Kummer class of a
rational function `f` to `∑_x (ord_x f mod n) [x]`. -/
def genericKummerResidueIso :
    ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).rightDerived 1).obj
      ((Spec X.functionField).rootsOfUnitySheaf n) ≅ c.pt :=
  haveI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  haveI : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  IsColimit.coconePointUniqueUpToIso
    (CokernelCofork.isColimitNSMulOfIso n X.genericGmIso (isColimitGenericKummerδ hn))
    (isColimitDivisorSequenceMapComp hX _
      (colimit.isColimit (Discrete.functor fun x : {x : X // coheight x = 1} ↦
        X.pointConstantInt x.1)) c hn hc)

/-- **The generic Kummer residue isomorphism is given by valuations**. Composed with the Kummer
coboundary `η_* 𝔾ₘ ⟶ R¹η_* μₙ` (`AlgebraicGeometry.Scheme.genericKummerδ`, precomposed with
`η_* η^* 𝔾ₘ ≅ η_* 𝔾ₘ`), the isomorphism `AlgebraicGeometry.Scheme.genericKummerResidueIso` is the
divisor map `f ↦ ∑_x ord_x(f) [x]` (`AlgebraicGeometry.Scheme.divisorSequenceMap`), with values in
the vertex of any colimit cofan `cD` on the family `x ↦ i_{x*} ℤ` of points of codimension one,
followed by reduction modulo `n`. -/
lemma genericKummerResidueIso_spec
    (cD : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1)
    (hcD : IsColimit cD) :
    X.genericGmIso.hom ≫ genericKummerδ n hn ≫ (genericKummerResidueIso hX hn c hc).hom =
      X.divisorSequenceMap cD hcD ≫ divisorsModNMap n hX cD hcD c := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  rw [← Category.assoc]
  refine (IsColimit.comp_coconePointUniqueUpToIso_hom
    (CokernelCofork.isColimitNSMulOfIso n X.genericGmIso (isColimitGenericKummerδ hn))
    (isColimitDivisorSequenceMapComp hX _
      (colimit.isColimit (Discrete.functor fun x : {x : X // coheight x = 1} ↦
        X.pointConstantInt x.1)) c hn hc) WalkingParallelPair.one).trans ?_
  exact X.divisorSequenceMap_comp_desc _ _ _ _ _

end Iso

end Generic

end AlgebraicGeometry.Scheme

end
