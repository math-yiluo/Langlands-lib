/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.LocalDerivation

/-!
# Infinitesimal points of a group scheme

The infinitesimal points `S[ε] ⟶ G` of a group scheme reducing to the identity
(`AlgebraicGeometry.GrpObj.infPoints`), and the bridge `AlgebraicGeometry.GrpObj.toLie` sending
such a point to the `ε`-coefficient of its comorphism, a morphism `ω_{G/S} ⟶ 𝒪_S`.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Infinitesimal points -/

section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- Precomposition with a morphism `f : X ⟶ Y` over `S`, as a group homomorphism
`G(Y) →* G(X)` on points of a group scheme. -/
noncomputable def pointsPrecomp {X Y : Over S} (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun y := f ≫ y
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

@[simp]
theorem pointsPrecomp_apply {X Y : Over S} (f : X ⟶ Y) (y : Y ⟶ G) :
    pointsPrecomp G f y = f ≫ y :=
  rfl

namespace GrpObj

/-- The infinitesimal points of a group scheme `G` over `S`: the points `v : S[ε] ⟶ G` over `S`
reducing to the identity along `i : S ⟶ S[ε]`, the kernel of `G(S[ε]) → G(S)`. Its group law is
the addition of tangent vectors, and it is in bijection with `Lie(G)` (`lieEquiv`).
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def infPoints : Subgroup (Scheme.dualNumbersOver S ⟶ G) :=
  (pointsPrecomp G (Scheme.dualNumbersιOver S)).ker

theorem mem_infPoints {v : Scheme.dualNumbersOver S ⟶ G} :
    v ∈ infPoints G ↔ Scheme.dualNumbersιOver S ≫ v = 1 :=
  MonoidHom.mem_ker

instance : (infPoints G).Normal :=
  MonoidHom.normal_ker _

/-- The identity point, as a morphism of schemes, is the identity section. -/
theorem one_left : (1 : Over.mk (𝟙 S) ⟶ G).left = unitSection G := by
  rw [Hom.one_def, Over.comp_left, unitSection]
  have : (SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left = 𝟙 S :=
    (Category.comp_id _).symm.trans (Over.w _)
  rw [this]
  exact Category.id_comp _

theorem ι_comp_left_eq {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    S.dualNumbersι ≫ v.left = unitSection G := by
  rw [mem_infPoints] at hv
  rw [← one_left G, ← hv]
  rfl

/-! ### The bridge from infinitesimal points to the Lie algebra -/

/-- The derivation `d_v : 𝒪_G → (i ≫ v)_*𝒪_S` attached to a point `v : S[ε] ⟶ G`: the
`ε`-coefficient of `v^♯(a) = e^♯(a) + ε d_v(a)`. It is a derivation over `f⁻¹𝒪_S` because `v`
is a morphism of schemes over `S` and `ε² = 0`. -/
noncomputable def infDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    ((Scheme.Modules.pushforward (S.dualNumbersι ≫ v.left)).obj
      (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom where
  d {V} :=
    { toFun := fun a ↦ (v.left.app V.unop a).snd
      map_zero' := by rw [map_zero]; rfl
      map_add' x y := by rw [map_add]; rfl }
  d_mul {V} a b := by
    change (v.left.app V.unop (a * b)).snd =
      (v.left.app V.unop a).fst * (v.left.app V.unop b).snd +
        (v.left.app V.unop b).fst * (v.left.app V.unop a).snd
    rw [map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul, mul_comm (v.left.app V.unop a).snd]
  d_map {X Y} f x := by
    have h := ConcreteCategory.congr_hom (v.left.c.naturality f) x
    exact (congr_arg snd h).trans (DualNumber.snd_mapRingHom _ _)
  d_app {X} a := by
    let ε₀ : (TopCat.Presheaf.pushforward CommRingCat v.left.base).obj
        (Scheme.dualNumbersOver S).left.presheaf ⟶
        (TopCat.Presheaf.pushforward CommRingCat v.left.base).obj
          (Scheme.dualNumbersOver S).left.presheaf :=
      Functor.whiskerLeft ((TopologicalSpace.Opens.map v.left.base).op ⋙ S.presheaf)
        (CommRingCat.dualNumberFst ≫ CommRingCat.dualNumberInl)
    have key : (G.hom.pullbackPresheafHom ≫ v.left.c) ≫ ε₀ =
        G.hom.pullbackPresheafHom ≫ v.left.c := by
      simp only [Scheme.Hom.pullbackPresheafHom, ← Adjunction.homEquiv_naturality_right_symm]
      congr 1
      ext U b
      have hb : ((v.left ≫ G.hom).app U b).snd = 0 := by
        rw [Scheme.Hom.congr_app (Over.w v) U]
        exact (DualNumber.snd_mapRingHom _ _).trans (map_zero _)
      exact TrivSqZeroExt.ext rfl hb.symm
    have h := ConcreteCategory.congr_hom (congr_app key X) a
    exact (congr_arg snd h).symm.trans rfl

/-- The morphism `(i ≫ v)^*Ω¹_{G/S} ⟶ 𝒪_S` attached to a point `v : S[ε] ⟶ G`: the derivation
`d_v` through the universal property of `Ω¹_{G/S}` and the adjunction `(i ≫ v)^* ⊣ (i ≫ v)_*`. -/
noncomputable def omegaHom (v : Scheme.dualNumbersOver S ⟶ G) :
    (Scheme.Modules.pullback (S.dualNumbersι ≫ v.left)).obj G.hom.cotangentSheaf ⟶
      Scheme.Modules.unitModule S :=
  ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).desc
        (infDerivation G v)))

/-- The bridge from infinitesimal points to the Lie algebra: a point `v : S[ε] ⟶ G` reducing to
the identity goes to the `ε`-coefficient of `v^♯`, a derivation `𝒪_G → e_*𝒪_S`, that is a morphism
`ω_{G/S} = e^*Ω¹_{G/S} ⟶ 𝒪_S`. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def toLie (v : infPoints G) : Lie G :=
  (Scheme.Modules.pullbackCongr (ι_comp_left_eq G v.2)).inv.app G.hom.cotangentSheaf ≫
    omegaHom G v.1

end GrpObj

end InfPoints

end AlgebraicGeometry
