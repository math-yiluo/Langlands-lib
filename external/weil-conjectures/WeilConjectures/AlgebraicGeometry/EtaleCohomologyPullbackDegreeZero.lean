/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux

/-!
# Degree-zero étale cohomology and pullback

Source: Stacks Project, Tags 05TD and 01FA
(blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

/-- The augmentation of any K-injective resolution induces the canonical isomorphism
from global sections to degree-zero cohomology. The factor `z` records well-definedness:
its composite with the inclusion of cycles is precisely the augmentation on sections.
Source: Stacks Tag 05TD (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof:
1. The chain-map identity for `s` makes its degree-zero component a cocycle, giving `z`.
2. A homotopy between lifts of a sheaf map makes their difference a boundary; this gives
   naturality and compatibility with comparisons (cohomology-pullback-functorial).
3. Global sections preserve kernels. Choose a nonnegative injective resolution; then its
   degree-zero cycles are the sections of `G`, with no boundaries (left-exact-injective-
   resolution-degree-zero). It is K-injective (dplus-injective-representative).
4. Transport that isomorphism to `I` by the homotopy equivalence between K-injective
   resolutions (cohomology-resolution-independent). Negative terms of `I` are allowed. -/
theorem exists_degreeZeroCohomology_cycles_iso (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    [QuasiIso s] [I.IsKInjective] :
    ∃ z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
        (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).cycles 0,
      z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
        (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ∧
      IsIso (z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0) := by
  let F := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let M := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let K := M.obj ((CochainComplex.singleFunctor _ 0).obj G)
  let k := F.map (singleObjXSelf (ComplexShape.up ℤ) 0 G).inv
  have hk : k ≫ K.d 0 1 = 0 := by
    dsimp [k, K, M]
    simp
  let w := K.liftCycles k 1 (by simp) hk
  let z := w ≫ cyclesMap (M.map s) 0
  have hz : z ≫ (M.obj I).iCycles 0 =
      F.map ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) := by
    dsimp only [z]
    rw [Category.assoc, cyclesMap_i, ← Category.assoc, liftCycles_i]
    exact (F.map_comp _ _).symm
  exact ⟨z, hz, isIso_degreeZeroCohomology_cycles_factor T G I s z hz⟩

/-- Naturality of the augmentation-to-cohomology map for arbitrary K-injective resolutions.
Taking `G' = G` and `φ = 𝟙 G` gives compatibility with resolution identifications.
Source: Stacks Tag 05TD (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: Lift `φ` to `a` between the resolutions (cohomology-pullback-functorial).
The given homotopy in degree zero says that `a⁰ s⁰ - s'⁰ φ` is `d⁻¹ h⁰`.
After global sections it is a boundary, hence zero in homology. For the identity sheaf
map, the lift induces the resolution comparison (cohomology-resolution-independent).
The existence and bijectivity of the augmentation map are established by the preceding
four-step argument using a nonnegative injective resolution and transport. -/
theorem degreeZeroCohomology_resolution_naturality (T : Scheme.{u})
    (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : G ⟶ G')
    (I I' : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    (s' : (CochainComplex.singleFunctor _ 0).obj G' ⟶ I')
    [QuasiIso s] [QuasiIso s'] [I.IsKInjective] [I'.IsKInjective]
    (a : I ⟶ I')
    (h : Homotopy (s ≫ a) ((CochainComplex.singleFunctor _ 0).map φ ≫ s'))
    (z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (z' : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G' ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').cycles 0)
    (hz : z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0))
    (hz' : z' ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G').inv ≫ s'.f 0)) :
    z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0 ≫
      homologyMap (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a) 0 =
    (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ ≫ z' ≫
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').homologyπ 0 := by
  let F := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let M := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let K := M.obj ((CochainComplex.singleFunctor _ 0).obj G)
  let k := F.map (singleObjXSelf (ComplexShape.up ℤ) 0 G).inv
  have hk : k ≫ K.d 0 1 = 0 := by
    dsimp [k, K, M]
    simp
  let w := K.liftCycles k 1 (by simp) hk
  have hw : w ≫ K.iCycles 0 = k := by
    apply liftCycles_i
  have hs : w ≫ cyclesMap (M.map s) 0 = z := by
    apply (cancel_mono ((M.obj I).iCycles 0)).1
    rw [Category.assoc, cyclesMap_i, ← Category.assoc, hw, hz]
    exact (F.map_comp _ _).symm
  have hs' : w ≫ cyclesMap (M.map ((CochainComplex.singleFunctor _ 0).map φ ≫ s')) 0 =
      F.map φ ≫ z' := by
    apply (cancel_mono ((M.obj I').iCycles 0)).1
    rw [Category.assoc, cyclesMap_i, ← Category.assoc, hw, Category.assoc, hz']
    dsimp [k, M, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    simp only [Functor.map_comp,
      single_map_f_self, Category.assoc]
    rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  have hh := (F.mapHomotopy h).homologyMap_eq 0
  rw [Functor.map_comp, homologyMap_comp] at hh
  calc
    _ = w ≫ K.homologyπ 0 ≫ homologyMap (M.map s) 0 ≫
        homologyMap (M.map a) 0 := by
      change z ≫ (M.obj I).homologyπ 0 ≫ homologyMap (M.map a) 0 = _
      rw [← hs]
      simp only [Category.assoc, homologyπ_naturality_assoc, homologyπ_naturality]
    _ = w ≫ K.homologyπ 0 ≫
        homologyMap (M.map ((CochainComplex.singleFunctor _ 0).map φ ≫ s')) 0 := by
      simpa only [Category.assoc] using congrArg (fun f => w ≫ K.homologyπ 0 ≫ f) hh
    _ = _ := by
      rw [homologyπ_naturality, ← Category.assoc, hs', Category.assoc]

/-- The degree-zero pullback formula on the actual complexes computing cohomology.
Source: Stacks Tag 01FA (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: The chain map on sections is the unit followed by the pushforward/global-sections
identification and the comparison `r`. The chain-map identity makes `s(g)` a cycle.
Naturality of the unit at `s⁰` gives `r(η(s(g))) = (r ∘ u⁻¹s)(η(g))`.
Passing to homology proves the equality. The four-step bounded-below/transport argument
above makes both augmentation maps isomorphisms; homotopy naturality proves compatibility
with every choice of resolution (cohomology-pullback-functorial and
cohomology-resolution-independent). No vanishing of negative terms is assumed. -/
theorem degreeZeroCohomology_resolution_pullback {X Y : Scheme.{u}} (u : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    (r : ((upperStar AddCommGrpCat.{u + 1} u).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso s] [I.IsKInjective] [QuasiIso r] [J.IsKInjective]
    (z : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (z' : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} u).obj G) ⟶
      (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).cycles 0)
    (hz : z ≫ (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0))
    (hz' : z' ≫ (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).iCycles 0 =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStar AddCommGrpCat.{u + 1} u).map
          ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ≫ r.f 0)) :
    z ≫ (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0 ≫
      homologyMap
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
            (Functor.associator (upperStar AddCommGrpCat.{u + 1} u)
              (lowerStar AddCommGrpCat.{u + 1} u)
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).hom ≫
            Functor.whiskerLeft (upperStar AddCommGrpCat.{u + 1} u)
              (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} u).hom)
          (ComplexShape.up ℤ)).app I ≫
          ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map r) 0 =
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G ≫ z' ≫
      (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homologyπ 0 := by
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let F' := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let U := upperStar AddCommGrpCat.{u + 1} u
  let η : F ⟶ U ⋙ F' :=
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit F ≫
      (Functor.associator U (lowerStar AddCommGrpCat.{u + 1} u) F).hom ≫
      Functor.whiskerLeft U (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} u).hom
  let b := (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app I ≫
    (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map r
  have hη : η.app G = globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G := by
    change F.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit.app G) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} u).hom.app (U.obj G) = _
    simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      globalSectionsUpperStarMap]
    dsimp only [F, U]
    erw [← Category.assoc, (Sheaf.ΓNatIsoSheafSections
      X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit.app G)]
    rfl
  change z ≫ _ ≫ homologyMap b 0 = _
  rw [homologyπ_naturality, ← Category.assoc]
  rw [← Category.assoc (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G)]
  apply congrArg (fun f => f ≫
    (((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homologyπ 0))
  apply (cancel_mono
    (((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).iCycles 0)).1
  rw [Category.assoc, cyclesMap_i, ← Category.assoc, hz, Category.assoc, hz']
  change F.map ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ≫
      (η.app (I.X 0) ≫ F'.map (r.f 0)) =
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G ≫
      F'.map (U.map ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ≫ r.f 0)
  rw [← Category.assoc, η.naturality, Category.assoc, Functor.comp_map,
    ← F'.map_comp, hη]


private theorem uliftZ_naturality {A B : AddCommGrpCat.{u + 1}}
    (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ A) (k : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (f ≫ k) =
      k (AddCommGrpCat.uliftZMultiplesAddEquiv A f) := by
  rfl

private theorem homEquiv_comparison {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (A : C) (B : D) (f : L.obj A ⟶ B) :
    adj'.homEquiv A B ((Adjunction.leftAdjointUniq adj adj').inv.app A ≫ f) =
      adj.homEquiv A B f := by
  rw [Adjunction.leftAdjointUniq_inv_app, adj'.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, adj.homEquiv_apply]

/-- Under the canonical degree-zero identification, pullback on étale cohomology is
pullback of a global section by the adjunction unit.
Source: Stacks Tag 01FA (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: For resolutions `s : G[0] → I` and `r : u⁻¹I → J`, the pullback of `[s(g)]` is
`[r(η(s(g)))]`. Naturality of the inverse-image unit gives
`η(s(g)) = (u⁻¹s)(η(g))`, so this is `[t(η(g))]` for `t = r ∘ u⁻¹s`.
The preceding naturality computation permits every choice of K-injective resolution,
by cohomology-pullback-functorial and cohomology-resolution-independent. In the recorded
Ext encoding of cohomology-pullback, the same identity follows by the degree-zero Ext/Hom
identification and the constant-sheaf adjunction defining `Sheaf.H.equiv₀`. -/
theorem cohomologyMap_zero_eq_globalSectionsUpperStarMap {X Y : Scheme.{u}}
    (u : Y ⟶ X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (g : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G) :
    cohomologyMap u G 0
      ((Sheaf.H.equiv₀ G terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g)) =
    (Sheaf.H.equiv₀ ((upperStar AddCommGrpCat.{u + 1} u).obj G) terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).hom.app ((upperStar AddCommGrpCat.{u + 1} u).obj G)
        (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G g)) := by
  apply (Sheaf.H.equiv₀ _ terminalIsTerminal).injective
  simp only [AddEquiv.apply_symm_apply]
  rw [cohomologyMap_apply]
  simp only [Sheaf.H.equiv₀, AddEquiv.symm_trans_apply, AddEquiv.trans_apply]
  simp only [CategoryTheory.Abelian.Ext.addEquiv₀_symm_apply,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  rw [← CategoryTheory.Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  simp only [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_symm_apply]
  simp only [Scheme.upperStarConstantSheafIso, Iso.app_hom, Iso.symm_hom]
  erw [homEquiv_comparison]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let f := (adjX.homEquiv A G).symm
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
      ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g))
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    (adjX.homEquiv A _ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv
      _ _ ((upperStar AddCommGrpCat.{u + 1} u).map f)) ≫
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} u).hom.app _) = _
  erw [(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv_apply,
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit_naturality]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [uliftZ_naturality, uliftZ_naturality, AddEquiv.apply_symm_apply]
  simp only [globalSectionsUpperStarMap, lowerStarCompSheafSectionsTerminalIso,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.symm_hom,
    ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.inv_hom_id_app]
  rfl

end AlgebraicGeometry.Etale
