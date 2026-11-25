/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Single

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale

private theorem exists_resolution_comparison
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K J I : CochainComplex C ℤ} (t : K ⟶ J) (s : K ⟶ I)
    [QuasiIso t] [QuasiIso s] [I.IsKInjective] :
    ∃ a : J ⟶ I, QuasiIso a ∧ Nonempty (Homotopy (t ≫ a) s) := by
  let P := HomotopyCategory.quotient C (.up ℤ)
  let b := inv (DerivedCategory.Q.map t) ≫ DerivedCategory.Q.map s
  obtain ⟨a', ha'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (P.obj J) I).2
    ((DerivedCategory.quotientCompQhIso C).hom.app J ≫ b ≫
      (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨a, rfl⟩ := P.map_surjective a'
  have ha : DerivedCategory.Q.map a = b := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app J)]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality, ha']
    simp
  have : IsIso (DerivedCategory.Q.map a) := by rw [ha]; dsimp [b]; infer_instance
  refine ⟨a, (DerivedCategory.isIso_Q_map_iff_quasiIso C a).1 this, ⟨?_⟩⟩
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective (P.obj K) I).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)).1
  change DerivedCategory.Qh.map (P.map (t ≫ a)) ≫ _ =
    DerivedCategory.Qh.map (P.map s) ≫ _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality]
  simp [Functor.map_comp, ha, b]

private theorem isIso_map_homology_zero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : K.d (-1) 0 = 0) (hL : L.d (-1) 0 = 0) :
    IsIso (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) 0) := by
  have hK' : (K.sc 0).f = 0 := by
    change K.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rwa [(ComplexShape.up ℤ).prev_eq' (show (-1 : ℤ) + 1 = 0 by decide)]
  have hL' : (L.sc 0).f = 0 := by
    change L.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rwa [(ComplexShape.up ℤ).prev_eq' (show (-1 : ℤ) + 1 = 0 by decide)]
  have := F.preservesLeftHomology_of_zero_f (K.sc 0) hK'
  have := F.preservesLeftHomology_of_zero_f (L.sc 0) hL'
  have := (quasiIsoAt_iff f 0).1 (inferInstance : QuasiIsoAt f 0)
  have : ShortComplex.QuasiIso
      (F.mapShortComplex.map ((shortComplexFunctor C (.up ℤ) 0).map f)) :=
    ShortComplex.quasiIso_map_of_preservesLeftHomology F _
  exact (quasiIsoAt_iff_isIso_homologyMap _ 0).1
    ((quasiIsoAt_iff _ 0).2 this)

/-- The augmentation induces an isomorphism on degree-zero sections cohomology.
Source: Stacks Project, Tag 05TD, proof of (3), and Tag 013K (injective resolutions).
(blueprint: lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor)

Proof: Choose a nonnegative injective resolution s₀ : G[0] → I₀ and extend it by
zero to integer degrees. It is K-injective because it is bounded below with injective
terms. Global sections are additive and left exact: they are right adjoint to the
constant-sheaf functor. Thus Γ(G) identifies with the kernel of Γ(d₀⁰). There are no
boundaries in degree zero because I₀⁻¹ = 0. The cycle factor z₀ of Γ(s₀⁰) therefore
induces an isomorphism ε₀ : Γ(G) → H⁰(Γ(I₀)).

Since I is K-injective and s₀ is a quasi-isomorphism, lift s through s₀ to a chain map
a : I₀ → I with a homotopy s₀ ≫ a ∼ s. It is a quasi-isomorphism and a homotopy
equivalence between K-injective complexes: the localization functor from the homotopy
category is fully faithful on K-injective targets. Applying the additive functor Γ
preserves this homotopy equivalence, so H⁰(Γ(a)) is an isomorphism. The homotopy
s₀ ≫ a ∼ s says that their degree-zero components differ by d⁻¹h⁰ (the source is
concentrated in degree zero). After Γ this difference is a boundary. Hence
ε₀ ≫ H⁰(Γ(a)) = z ≫ homologyπ by the assumed equality hz. Both factors on the left
are isomorphisms, proving the assertion. This also covers complexes I with negative
terms: those terms contribute boundaries, rather than being assumed zero. The factor
z is uniquely determined by hz because iCycles is monic. -/
theorem isIso_degreeZeroCohomology_cycles_factor (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    [QuasiIso s] [I.IsKInjective]
    (z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (hz : z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0)) :
    IsIso (z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homologyπ 0) := by
  let := HasDerivedCategory.standard
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
  have := IsGrothendieckAbelian.enoughInjectives.{u + 1}
    (C := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
  let F := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let M := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let K := (CochainComplex.singleFunctor _ 0).obj G
  let R := injectiveResolution G
  have : R.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective R.cochainComplex 0
  obtain ⟨a, ha, ⟨h⟩⟩ := exists_resolution_comparison R.ι' s
  have : QuasiIso a := ha
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff a).1 ha
  have hmap : IsIso (homologyMap (M.map a) 0) := by
    let e' := F.mapHomotopyEquiv e
    have he' : e'.hom = M.map a := congrArg (M.map) he
    rw [← he']
    exact (e'.toHomologyIso 0).isIso_hom
  have hR : IsIso (homologyMap (M.map R.ι') 0) :=
    isIso_map_homology_zero F R.ι' (by simp [CochainComplex.singleFunctor])
      ((CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by omega)).eq_of_src _ _)
  have hs : IsIso (homologyMap (M.map s) 0) := by
    have hh := (F.mapHomotopy h).homologyMap_eq 0
    rw [Functor.map_comp, homologyMap_comp] at hh
    rw [← hh]
    infer_instance
  have hKi : IsIso ((M.obj K).iCycles 0) :=
    (M.obj K).isIso_iCycles 0 1
      ((ComplexShape.up ℤ).next_eq' (show (0 : ℤ) + 1 = 1 by decide))
      (by simp [M, K, CochainComplex.singleFunctor])
  have hKπ : IsIso ((M.obj K).homologyπ 0) :=
    (M.obj K).isIso_homologyπ (-1) 0
      ((ComplexShape.up ℤ).prev_eq' (show (-1 : ℤ) + 1 = 0 by decide))
      (by simp [M, K, CochainComplex.singleFunctor])
  let c : F.obj G ⟶ (M.obj K).cycles 0 :=
    F.map (singleObjXSelf (.up ℤ) 0 G).inv ≫ inv ((M.obj K).iCycles 0)
  have hc : IsIso c := by dsimp [c]; infer_instance
  have hz' : z = c ≫ cyclesMap (M.map s) 0 := by
    apply (cancel_mono ((M.obj I).iCycles 0)).1
    rw [Category.assoc, cyclesMap_i]
    simpa [c, M, K, Functor.map_comp, Category.assoc] using hz
  rw [hz', Category.assoc, ← homologyπ_naturality]
  infer_instance

end AlgebraicGeometry.Etale
