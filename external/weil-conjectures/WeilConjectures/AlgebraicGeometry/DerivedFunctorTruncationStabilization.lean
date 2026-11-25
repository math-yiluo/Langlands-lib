/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Stabilization of derived cohomology on the lower truncation tower

Source: Stacks Project, Derived Categories of Schemes, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-functor-truncation-stabilization).
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isZero_rightDerived_shifted_single
    {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasDerivedCategory AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions C] [HasInjectiveResolutions C]
    (F : C ⥤ AddCommGrpCat.{u}) [F.Additive] (M : C) (i n : ℤ) (p : ℕ)
    (hp : n + i = (p : ℤ)) (hM : IsZero ((F.rightDerived p).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      (F.rightDerivedFunctor.obj
        ((DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj M))⟦n⟧))) := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let S := (DerivedCategory.singleFunctor C 0).obj M
  let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M
  let e₁ := F.rightDerivedFunctor.mapIso ((shiftFunctor (DerivedCategory C) n).mapIso e.symm)
  let e₂ := (F.rightDerivedFunctor.commShiftIso n).app S
  let e₃ := ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso n i p hp).app
    (F.rightDerivedFunctor.obj S)
  exact hM.of_iso
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso (e₁ ≪≫ e₂) ≪≫
      e₃ ≪≫ F.homologyRightDerivedFunctorObjSingleFunctorIso M p)

/-- An additive functor with right derived functors vanishing in degrees at least `N`
on quasi-coherent modules induces isomorphisms on degree-`i` cohomology between successive
lower truncations whenever `n ≥ N - i`. The source truncation is `τ≥(-n) E` and the target
is `τ≥(-n+1) E = τ≥(-(n-1)) E`; the map is the standard t-structure's canonical one.
Source: Stacks Project, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-functor-truncation-stabilization).

Proof:
1. Use the successive lower-truncation triangle
`H^(-n)(E)[n] → E_n → E_(n-1) → H^(-n)(E)[n+1]`
(`lem-pc-derived-lower-truncation-step-triangle`).
2. Apply the unbounded triangulated right derived functor
(`lem-pc-right-derived-functor-triangulated`). Its commutation with shifts, the cohomology
shift isomorphism (`lem-sp-derived-cohomology-shift`), and the source library's comparison
`homologyRightDerivedFunctorObjSingleFunctorIso` identify the endpoint in degree `j`
with `R^(n+j)F(H^(-n)(E))` for `n+j ≥ 0`. The comparison uses the bounded-below single
identification (`lem-sp-derived-functor-single-identification`) and the compatibility of
bounded-below and unbounded right derived functors.
3. The cohomology sheaf is quasi-coherent by `E.property`. For `j = i` and `j = i+1`,
`n+j ≥ N ≥ 0`, so the endpoint objects vanish by `hvan`, including at equality.
4. The long exact cohomology sequence (`lem-sf-derived-homology-long-exact`) makes the
transition map monic and epic, hence an isomorphism. -/
theorem isIso_rightDerivedFunctor_lowerTruncation_step
    (X : Scheme.{u})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ AddCommGrpCat.{u})
    [F.Additive] (N : ℕ)
    (hvan : ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M))
    (E : schemeDerivedQCohCategory X) (i n : ℤ) (hn : (N : ℤ) - i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
          (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E.obj))) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let M := (DerivedCategory.homologyFunctor C (-n)).obj E.obj
  have hM : M.IsQuasicoherent := E.property (-n)
  have hz (j : ℤ) (hj : (N : ℤ) ≤ n + j) :
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
        (F.rightDerivedFunctor.obj
          ((DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj M))⟦n⟧))) := by
    have hp : n + j = (((n + j).toNat : ℕ) : ℤ) := by omega
    exact isZero_rightDerived_shifted_single F M j n (n + j).toNat hp
      (hvan M hM (n + j).toNat (by omega))
  obtain ⟨f, h, hT⟩ := DerivedCategory.exists_lowerTruncationStepTriangle E.obj n
  let T := Pretriangulated.Triangle.mk f
    ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E.obj) h
  let T' := F.rightDerivedFunctor.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ :=
    F.rightDerivedFunctor.map_distinguished T hT
  have hz₀ : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj T'.obj₁) :=
    hz i (by omega)
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i + 1)).obj
      T'.obj₁) := hz (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T' hT' i).2
      (hz₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T' hT' i (i + 1)).2
      (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
    T'.mor₂)

end AlgebraicGeometry
