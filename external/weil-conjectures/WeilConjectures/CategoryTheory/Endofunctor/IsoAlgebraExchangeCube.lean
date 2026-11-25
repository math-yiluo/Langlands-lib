/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightCube
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!

# Base change of transported algebras through exchange morphisms

Let `Lf ⊣ Rf` and `Lf' ⊣ Rf'` be adjunctions with comparisons `θ_e`, `θ_π`, `θ_Φ` of left
adjoints and isomorphisms `c_A`, `c_B` satisfying the cube condition
(`CategoryTheory.Adjunction.CubeCondition`). Let `S ≅ Rf` and `S' ≅ Rf'` be functors identified
with the right adjoints (in the applications, the lower shrieks `Rf_! ≅ Rf_*` of proper
morphisms), with commutation isomorphisms `b : S ⋙ G_B ≅ G_A ⋙ S` and
`t : S' ⋙ Φ_B ≅ Φ_A ⋙ S'` which are the exchange morphisms of `θ_e` and `θ_Φ` under these
identifications (`CategoryTheory.Adjunction.ExchangeCompatible`). If the exchange morphism of
`θ_π` is an isomorphism, then for every algebra `(K, φ)` of `G_A` with invertible structure
morphism, the two transports
```
(P_B S K, c_B ∘ P_B b ∘ P_B S φ)    and    (S' P_A K, t ∘ S' c_A ∘ S' P_A φ)
```
are isomorphic (`CategoryTheory.Adjunction.nonempty_mapOfNatIso_obj_iso_of_cubeCondition`),
through `P_B S K ≅ P_B Rf K ≅ Rf' P_A K ≅ S' P_A K`.

-/

@[expose] public section

open CategoryTheory Endofunctor

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}

/-- A commutation isomorphism `b : S ⋙ G ≅ G' ⋙ S` of a functor `S` identified with the right
adjoint `Rf` through `ι : S ≅ Rf` is *compatible with the exchange* of `θ : G ⋙ Lf ≅ Lf ⋙ G'`
if, under `ι`, it is the exchange morphism `Rf ⋙ G ⟶ G' ⋙ Rf` of `θ`. -/
def ExchangeCompatible {G : B ⥤ B} {G' : A ⥤ A} {S : A ⥤ B} (af : Lf ⊣ Rf)
    (θ : G ⋙ Lf ≅ Lf ⋙ G') (b : S ⋙ G ≅ G' ⋙ S) (ι : S ≅ Rf) : Prop :=
  ∀ K : A, b.hom.app K ≫ ι.hom.app (G'.obj K) = G.map (ι.hom.app K) ≫ (exchangeRight af af θ).app K

variable {GA : A ⥤ A} {GB : B ⥤ B} {PA : A ⥤ A'} {PB : B ⥤ B'} {ΦA : A' ⥤ A'} {ΦB : B' ⥤ B'}
  {S : A ⥤ B} {S' : A' ⥤ B'}

/-- The base change isomorphism `S ⋙ P_B ≅ P_A ⋙ S'`: the exchange morphism of `θ_π`, read
through `ι : S ≅ Rf` and `ι' : S' ≅ Rf'`. -/
noncomputable def exchangeIso (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA)
    [IsIso (exchangeRight af af' θπ)] (ι : S ≅ Rf) (ι' : S' ≅ Rf') : S ⋙ PB ≅ PA ⋙ S' :=
  Functor.isoWhiskerRight ι PB ≪≫ asIso (exchangeRight af af' θπ) ≪≫
    Functor.isoWhiskerLeft PA ι'.symm

lemma exchangeIso_hom_app (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA)
    [IsIso (exchangeRight af af' θπ)] (ι : S ≅ Rf) (ι' : S' ≅ Rf') (K : A) :
    (exchangeIso af af' θπ ι ι').hom.app K =
      PB.map (ι.hom.app K) ≫ (exchangeRight af af' θπ).app K ≫ ι'.inv.app (PA.obj K) := by
  simp [exchangeIso]

/-- **The cube law through the identifications `S ≅ Rf`, `S' ≅ Rf'`.** -/
lemma map_exchangeIso_hom_app_comp_of_cubeCondition (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θe : GB ⋙ Lf ≅ Lf ⋙ GA) (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA) (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA)
    (cA : PA ⋙ ΦA ≅ GA ⋙ PA) (cB : PB ⋙ ΦB ≅ GB ⋙ PB) (h : CubeCondition θe θπ θΦ cA cB)
    [IsIso (exchangeRight af af' θπ)] (ι : S ≅ Rf) (ι' : S' ≅ Rf')
    (b : S ⋙ GB ≅ GA ⋙ S) (t : S' ⋙ ΦB ≅ ΦA ⋙ S') (hb : ExchangeCompatible af θe b ι)
    (ht : ExchangeCompatible af' θΦ t ι') (K : A) :
    ΦB.map ((exchangeIso af af' θπ ι ι').hom.app K) ≫ t.hom.app (PA.obj K) ≫
        S'.map (cA.hom.app K) =
      cB.hom.app (S.obj K) ≫ PB.map (b.hom.app K) ≫
        (exchangeIso af af' θπ ι ι').hom.app (GA.obj K) := by
  have ht' : t.hom.app (PA.obj K) = ΦB.map (ι'.hom.app (PA.obj K)) ≫
      (exchangeRight af' af' θΦ).app (PA.obj K) ≫ ι'.inv.app (ΦA.obj (PA.obj K)) := by
    rw [← reassoc_of% (ht (PA.obj K)), Iso.hom_inv_id_app, Category.comp_id]
  have hb' : b.hom.app K ≫ ι.hom.app (GA.obj K) =
      GB.map (ι.hom.app K) ≫ (exchangeRight af af θe).app K := hb K
  have hc := exchangeRight_app_cube af af' θe θπ θΦ cA cB h K
  have hcB := cB.hom.naturality (ι.hom.app K)
  have hι := ι'.inv.naturality (cA.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hcB hι
  rw [exchangeIso_hom_app, exchangeIso_hom_app, ht']
  have hid : ΦB.map (ι'.inv.app (PA.obj K)) ≫ ΦB.map (ι'.hom.app (PA.obj K)) = 𝟙 _ := by
    rw [← ΦB.map_comp, Iso.inv_hom_id_app, ΦB.map_id]
  simp only [Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hid, ← hι, reassoc_of% hc, ← PB.map_comp_assoc, hb',
    PB.map_comp, Category.assoc, reassoc_of% hcB]

/-- **Base change of transported algebras.** Under the cube condition, for exchange-compatible
commutation isomorphisms `b`, `t` and an isomorphism exchange morphism of `θ_π`, the transports
`(P_B S K, c_B ∘ P_B b ∘ P_B S φ)` and `(S' P_A K, t ∘ S' c_A ∘ S' P_A φ)` of an algebra
`(K, φ)` of `G_A` are isomorphic. -/
theorem nonempty_mapOfNatIso_obj_iso_of_cubeCondition (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θe : GB ⋙ Lf ≅ Lf ⋙ GA) (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA) (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA)
    (cA : PA ⋙ ΦA ≅ GA ⋙ PA) (cB : PB ⋙ ΦB ≅ GB ⋙ PB) (h : CubeCondition θe θπ θΦ cA cB)
    [IsIso (exchangeRight af af' θπ)] (ι : S ≅ Rf) (ι' : S' ≅ Rf')
    (b : S ⋙ GB ≅ GA ⋙ S) (t : S' ⋙ ΦB ≅ ΦA ⋙ S') (hb : ExchangeCompatible af θe b ι)
    (ht : ExchangeCompatible af' θΦ t ι') (K : IsoAlgebra GA) :
    Nonempty ((IsoAlgebra.mapOfNatIso cB).obj ((IsoAlgebra.mapOfNatIso b).obj K) ≅
      (IsoAlgebra.mapOfNatIso t).obj ((IsoAlgebra.mapOfNatIso cA).obj K)) :=
  ⟨ObjectProperty.isoMk _ (Algebra.isoMk ((exchangeIso af af' θπ ι ι').app K.carrier) (by
    have hcube := map_exchangeIso_hom_app_comp_of_cubeCondition af af' θe θπ θΦ cA cB h ι ι' b t
      hb ht K.carrier
    have hn := (exchangeIso af af' θπ ι ι').hom.naturality K.str.hom
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    change ΦB.map ((exchangeIso af af' θπ ι ι').hom.app K.carrier) ≫
        t.hom.app (PA.obj K.carrier) ≫ S'.map (cA.hom.app K.carrier ≫ PA.map K.str.hom) =
      (cB.hom.app (S.obj K.carrier) ≫ PB.map (b.hom.app K.carrier ≫ S.map K.str.hom)) ≫
        (exchangeIso af af' θπ ι ι').hom.app K.carrier
    rw [Functor.map_comp, reassoc_of% hcube, Functor.map_comp, Category.assoc, Category.assoc,
      hn]))⟩

end CategoryTheory.Adjunction
