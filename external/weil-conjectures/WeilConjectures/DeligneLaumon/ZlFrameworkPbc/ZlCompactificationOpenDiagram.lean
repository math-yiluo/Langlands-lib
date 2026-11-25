/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension

/-! # Compactification diagrams with open restriction
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-compactification-open-diagram).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrameworkPbc

/-- The geometric inputs of the comparison, retaining the chosen Cartesian squares.
No structure morphism is required to be separated. The invertibility certificates
are the usual consequences of being over k with l different from its characteristic.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-compactification-open-diagram). -/
structure OpenDiagram (D : FiniteFieldDatum.{u}) (l : ℕ) where
  X : Scheme.{u}
  Y : Scheme.{u}
  U : Scheme.{u}
  V : Scheme.{u}
  [overX : X.Over (Spec (.of D.k))]
  [overY : Y.Over (Spec (.of D.k))]
  [overU : U.Over (Spec (.of D.k))]
  [overV : V.Over (Spec (.of D.k))]
  [finiteX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [compactX : QuasiCompact (X ↘ Spec (.of D.k))]
  [finiteY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [compactY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [finiteU : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [compactU : QuasiCompact (U ↘ Spec (.of D.k))]
  [finiteV : LocallyOfFiniteType (V ↘ Spec (.of D.k))]
  [compactV : QuasiCompact (V ↘ Spec (.of D.k))]
  [qsX : QuasiSeparatedSpace X]
  [qsY : QuasiSeparatedSpace Y]
  [qsU : QuasiSeparatedSpace U]
  [qsV : QuasiSeparatedSpace V]
  [noethX : IsNoetherian X]
  [noethY : IsNoetherian Y]
  [noethU : IsNoetherian U]
  [noethV : IsNoetherian V]
  [dimX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dimY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [dimU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dimV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [invX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [invY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [invU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [invV : Fact (∀ y : V, IsUnit (l : V.presheaf.stalk y))]
  f : X ⟶ Y
  f' : U ⟶ V
  v : V ⟶ Y
  u : U ⟶ X
  [fOver : f.IsOver (Spec (.of D.k))]
  [f'Over : f'.IsOver (Spec (.of D.k))]
  [separatedF : IsSeparated f]
  [finiteF : LocallyOfFiniteType f]
  [compactF : QuasiCompact f]
  [separatedF' : IsSeparated f']
  [finiteF' : LocallyOfFiniteType f']
  [compactF' : QuasiCompact f']
  [openV : IsOpenImmersion v]
  [compactOpenV : QuasiCompact v]
  [openU : IsOpenImmersion u]
  [compactOpenU : QuasiCompact u]
  c : Compactification f
  c' : Compactification f'
  w : c'.Z ⟶ c.Z
  properSquare : ChosenCartesianSquare w c'.g c.g v
  openSquare : OpenImmersionSquare u c'.i c.i w
  [noethT : IsNoetherian c.Z]
  [noethT' : IsNoetherian c'.Z]
  [dimT : Fact (∃ n : ℕ, topologicalKrullDim c.Z ≤ n)]
  [dimT' : Fact (∃ n : ℕ, topologicalKrullDim c'.Z ≤ n)]

attribute [instance] OpenDiagram.overX OpenDiagram.overY OpenDiagram.overU OpenDiagram.overV
  OpenDiagram.finiteX OpenDiagram.compactX OpenDiagram.finiteY OpenDiagram.compactY
  OpenDiagram.finiteU OpenDiagram.compactU OpenDiagram.finiteV OpenDiagram.compactV
  OpenDiagram.qsX OpenDiagram.qsY OpenDiagram.qsU OpenDiagram.qsV
  OpenDiagram.noethX OpenDiagram.noethY OpenDiagram.noethU OpenDiagram.noethV
  OpenDiagram.dimX OpenDiagram.dimY OpenDiagram.dimU OpenDiagram.dimV
  OpenDiagram.invX OpenDiagram.invY OpenDiagram.invU OpenDiagram.invV
  OpenDiagram.fOver OpenDiagram.f'Over
  OpenDiagram.separatedF OpenDiagram.finiteF OpenDiagram.compactF
  OpenDiagram.separatedF' OpenDiagram.finiteF' OpenDiagram.compactF'
  OpenDiagram.openV OpenDiagram.compactOpenV OpenDiagram.openU OpenDiagram.compactOpenU
  OpenDiagram.noethT OpenDiagram.noethT' OpenDiagram.dimT OpenDiagram.dimT'

/-- Use the actual universal pullback isomorphism to choose a Cartesian square.
Source: thm-cbc-qbar.proof.md, identity and iterated open restriction
(blueprint: def-zl-compactification-open-diagram). -/
def chosenSquare {A B C T : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {c : B ⟶ T} {d : C ⟶ T} (h : IsPullback a b c d) :
    ChosenCartesianSquare a b c d where
  toCommSq := h.toCommSq
  isoPullback := h.isoPullback
  hom_fst := h.isoPullback_hom_fst
  hom_snd := h.isoPullback_hom_snd

/-- The identity open restriction of an actual compactification diagram.
Source: thm-cbc-qbar.proof.md, identity and iterated open restriction
(blueprint: def-zl-compactification-open-diagram). -/
def OpenDiagram.identity {D : FiniteFieldDatum.{u}} {l : ℕ}
    (G : OpenDiagram D l) : OpenDiagram D l where
  X := G.X
  Y := G.Y
  U := G.X
  V := G.Y
  f := G.f
  f' := G.f
  u := 𝟙 G.X
  v := 𝟙 G.Y
  c := G.c
  c' := G.c
  w := 𝟙 G.c.Z
  properSquare := chosenSquare IsPullback.of_id_fst
  openSquare := { chosenSquare IsPullback.of_id_fst with
    isOpenImmersion := inferInstance
    isOpenImmersion' := inferInstance }

/-- One further actual open restriction of G, with the shared compactification fixed.
Source: thm-cbc-qbar.proof.md, identity and iterated open restriction
(blueprint: def-zl-compactification-open-diagram). -/
structure FurtherOpen {D : FiniteFieldDatum.{u}} {l : ℕ} (G : OpenDiagram D l) where
  U : Scheme.{u}
  V : Scheme.{u}
  [overU : U.Over (Spec (.of D.k))]
  [overV : V.Over (Spec (.of D.k))]
  [finiteU : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [compactU : QuasiCompact (U ↘ Spec (.of D.k))]
  [finiteV : LocallyOfFiniteType (V ↘ Spec (.of D.k))]
  [compactV : QuasiCompact (V ↘ Spec (.of D.k))]
  [qsU : QuasiSeparatedSpace U]
  [qsV : QuasiSeparatedSpace V]
  [noethU : IsNoetherian U]
  [noethV : IsNoetherian V]
  [dimU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dimV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [invU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [invV : Fact (∀ y : V, IsUnit (l : V.presheaf.stalk y))]
  f : U ⟶ V
  u : U ⟶ G.U
  v : V ⟶ G.V
  [fOver : f.IsOver (Spec (.of D.k))]
  [separatedF : IsSeparated f]
  [finiteF : LocallyOfFiniteType f]
  [compactF : QuasiCompact f]
  [openU : IsOpenImmersion u]
  [compactOpenU : QuasiCompact u]
  [openV : IsOpenImmersion v]
  [compactOpenV : QuasiCompact v]
  c : Compactification f
  w : c.Z ⟶ G.c'.Z
  properSquare : ChosenCartesianSquare w c.g G.c'.g v
  openSquare : OpenImmersionSquare u c.i G.c'.i w
  [noethT : IsNoetherian c.Z]
  [dimT : Fact (∃ n : ℕ, topologicalKrullDim c.Z ≤ n)]

attribute [instance] FurtherOpen.overU FurtherOpen.overV
  FurtherOpen.finiteU FurtherOpen.compactU FurtherOpen.finiteV FurtherOpen.compactV
  FurtherOpen.qsU FurtherOpen.qsV FurtherOpen.noethU FurtherOpen.noethV
  FurtherOpen.dimU FurtherOpen.dimV FurtherOpen.invU FurtherOpen.invV
  FurtherOpen.fOver FurtherOpen.separatedF FurtherOpen.finiteF FurtherOpen.compactF
  FurtherOpen.openU FurtherOpen.compactOpenU FurtherOpen.openV FurtherOpen.compactOpenV
  FurtherOpen.noethT FurtherOpen.dimT

/-- The second open diagram, whose source is literally the first restricted diagram.
Source: thm-cbc-qbar.proof.md, identity and iterated open restriction
(blueprint: def-zl-compactification-open-diagram). -/
def FurtherOpen.second {D : FiniteFieldDatum.{u}} {l : ℕ}
    {G : OpenDiagram D l} (H : FurtherOpen G) : OpenDiagram D l where
  X := G.U
  Y := G.V
  U := H.U
  V := H.V
  f := G.f'
  f' := H.f
  u := H.u
  v := H.v
  c := G.c'
  c' := H.c
  w := H.w
  properSquare := H.properSquare
  openSquare := H.openSquare

/-- The outer diagram uses the actual composite open maps and pasted Cartesian squares.
Source: thm-cbc-qbar.proof.md, identity and iterated open restriction
(blueprint: def-zl-compactification-open-diagram). -/
def FurtherOpen.outer {D : FiniteFieldDatum.{u}} {l : ℕ}
    {G : OpenDiagram D l} (H : FurtherOpen G) : OpenDiagram D l where
  X := G.X
  Y := G.Y
  U := H.U
  V := H.V
  f := G.f
  f' := H.f
  u := H.u ≫ G.u
  v := H.v ≫ G.v
  c := G.c
  c' := H.c
  w := H.w ≫ G.w
  properSquare := chosenSquare
    ((IsPullback.of_iso_pullback H.properSquare.toCommSq H.properSquare.isoPullback
      H.properSquare.hom_fst H.properSquare.hom_snd).paste_horiz
      (IsPullback.of_iso_pullback G.properSquare.toCommSq G.properSquare.isoPullback
        G.properSquare.hom_fst G.properSquare.hom_snd))
  openSquare := { chosenSquare
    ((IsPullback.of_iso_pullback H.openSquare.toCommSq H.openSquare.isoPullback
      H.openSquare.hom_fst H.openSquare.hom_snd).paste_horiz
      (IsPullback.of_iso_pullback G.openSquare.toCommSq G.openSquare.isoPullback
        G.openSquare.hom_fst G.openSquare.hom_snd)) with
    isOpenImmersion := inferInstance
    isOpenImmersion' := inferInstance }

end WeilConjectures.ZlFrameworkPbc
