/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-!
# Termwise derived pullback of a bounded-above flat complex

Source: Stacks Project, Cohomology, Tags 06YD and 06YJ
(blueprint: lemma-coherent-base-change-invertible-sheaves--2).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A bounded-above complex `K` of flat structure-sheaf modules computes its derived
pullback term by term. The functor `F` is pinned on objects and maps to the recorded
`Scheme.Modules.tensorPullback`. Its left-derived counit `ε` is canonical by the
left-derived universal property. The isomorphism `e` in the ordinary-to-derived direction
has inverse exactly `ε` at `K`, rather than being an unrelated isomorphism.
The localization `Qh` after the homotopy quotient represents complexes in the derived
category; invertibility there expresses the quasi-isomorphism comparison of the node.
Source: Stacks Project, Cohomology, Tags 06YD and 06YJ
(blueprint: lemma-coherent-base-change-invertible-sheaves--2).

Proof:
1. By lem-pc-bounded-above-flat-kflat (Stacks 06YD), the bounded-above flat complex
   `K` is K-flat over the structure sheaf of `S`.
2. Its identity is a K-flat resolution. The K-flat computation of
   lemma-coherent-base-change-invertible-sheaves--2 (Stacks 06YJ) identifies the derived pullback of
   `K` with the termwise tensor pullback of `K`. Its counit at `K` is therefore invertible.
   Take its inverse to obtain the ordinary-to-derived comparison `e`; this is the
   canonical identification in the derived category, hence the quasi-isomorphism
   comparison in the node. -/
theorem flatComplexDerivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) :
    ∃ (F : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace))
      (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
      (_ : ∀ {M N} (a : M ⟶ N),
        F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
          eqToHom (hF N).symm)
      (_ : F.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      (derivedPullback g).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
        ∃ e : DerivedCategory.Qh.obj
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≅
            (derivedPullback g).obj
              (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)),
          e.inv = ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hderived, htri, hε⟩ :=
    (derivedPullback_spec g)
  refine ⟨F, hF, hFmap, hFadd, ε, hderived, ?_⟩
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    S.toRingedSpace K hbounded hflat
  have := hε K hK
  exact ⟨(asIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))).symm,
    rfl⟩

end AlgebraicGeometry
