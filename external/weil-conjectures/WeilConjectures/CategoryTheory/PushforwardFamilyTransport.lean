/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeTransport
public import WeilConjectures.CategoryTheory.PushforwardFamily

/-!

# Transport of base-change morphisms along a pseudonatural comparison

Let `L` and `P` be two families of pullbacks on categories `E X` and `D X`, with composition
isomorphisms `Lc` and `c` and right adjoints `L f ⊣ R_L f`, `P f ⊣ R_P f`, and let
`H X : E X ⥤ D X` be functors commuting with the pullbacks through a pseudonatural family
`θ f : H Y ⋙ P f ≅ L f ⋙ H X` (`CategoryTheory.PullbackPseudonatural`) and with the pushforwards
through `ψ f : H X ⋙ R_P f ≅ R_L f ⋙ H Y`, compatibly with the units and counits. For instance
`E X` is a category of module objects, `D X` the category of underlying sheaves and `H X` the
forgetful functor.

Then for a commutative square `g' ≫ f = f' ≫ g`, the comparisons of the composition isomorphisms
correspond (`CategoryTheory.PullbackPseudonatural.pullbackFamilySquareComparison`), and if the
base-change morphism of `P` is an isomorphism at `H K`, the image under `H` of the base-change
morphism of `L` at `K` is an isomorphism
(`CategoryTheory.PullbackPseudonatural.isIso_map_pushforwardBaseChange_app`).

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {B A B' A' b a b' a' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
  [Category* b] [Category* a] [Category* b'] [Category* a']

/-- If the exchange morphisms of two data correspond through isomorphisms
(`CategoryTheory.Adjunction.map_exchangeRight_app_of_comm`), and the second one is an
isomorphism, then so is the image of the first one. -/
lemma isIso_map_exchangeRight_app_of_comm {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    {lf : b ⥤ a} {rf : a ⥤ b} {lf' : b' ⥤ a'} {rf' : a' ⥤ b'} {g : b ⥤ b'} {g' : a ⥤ a'}
    (ad : lf ⊣ rf) (ad' : lf' ⊣ rf') (t : g ⋙ lf' ≅ lf ⋙ g')
    {HB : B ⥤ b} {HA : A ⥤ a} {HB' : B' ⥤ b'} {HA' : A' ⥤ a'}
    (ψL : HB ⋙ lf ≅ Lf ⋙ HA) (ψR : HA ⋙ rf ≅ Rf ⋙ HB)
    (ψL' : HB' ⋙ lf' ≅ Lf' ⋙ HA') (ψR' : HA' ⋙ rf' ≅ Rf' ⋙ HB')
    (ψG : HB ⋙ g ≅ G ⋙ HB') (ψG' : HA ⋙ g' ≅ G' ⋙ HA')
    (hunit : ∀ K, HB'.map (adj'.unit.app K) =
      ad'.unit.app (HB'.obj K) ≫ rf'.map (ψL'.hom.app K) ≫ ψR'.hom.app (Lf'.obj K))
    (hcounit : ∀ K, lf.map (ψR.hom.app K) ≫ ψL.hom.app (Rf.obj K) ≫ HA.map (adj.counit.app K) =
      ad.counit.app (HA.obj K))
    (hθ : ∀ K, lf'.map (ψG.hom.app K) ≫ ψL'.hom.app (G.obj K) ≫ HA'.map (θ.hom.app K) =
      t.hom.app (HB.obj K) ≫ g'.map (ψL.hom.app K) ≫ ψG'.hom.app (Lf.obj K))
    (K : A) [IsIso ((exchangeRight ad ad' t).app (HA.obj K))] :
    IsIso (HB'.map ((exchangeRight adj adj' θ).app K)) := by
  have h := map_exchangeRight_app_of_comm adj adj' θ ad ad' t ψL ψR ψL' ψR' ψG ψG' hunit hcounit
    hθ K
  have : IsIso (g.map (ψR.hom.app K) ≫ ψG.hom.app (Rf.obj K) ≫
      HB'.map ((exchangeRight adj adj' θ).app K)) := by
    rw [h]
    infer_instance
  rw [← Category.assoc] at this
  exact IsIso.of_isIso_comp_left (g.map (ψR.hom.app K) ≫ ψG.hom.app (Rf.obj K)) _

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {C : Type*} [Category C] {D E : C → Type*} [∀ X, Category (D X)] [∀ X, Category (E X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}
  {L : ∀ {X Y : C}, (X ⟶ Y) → E Y ⥤ E X}
  {Lc : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), L (f ≫ g) ≅ L g ⋙ L f}
  {H : ∀ X : C, E X ⥤ D X} {θ : ∀ {X Y : C} (f : X ⟶ Y), H Y ⋙ P f ≅ L f ⋙ H X}
  {X Y X' Y' : C} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The comparisons of the composition isomorphisms along a commutative square correspond under
a pseudonatural family. -/
lemma PullbackPseudonatural.pullbackFamilySquareComparison (hθ : PullbackPseudonatural c Lc θ)
    (h : g' ≫ f = f' ≫ g) (K : E Y) :
    (P f').map ((θ g).hom.app K) ≫ (θ f').hom.app ((L g).obj K) ≫
        (H X').map ((CategoryTheory.pullbackFamilySquareComparison Lc h).hom.app K) =
      (CategoryTheory.pullbackFamilySquareComparison c h).hom.app ((H Y).obj K) ≫
        (P g').map ((θ f).hom.app K) ≫ (θ g').hom.app ((L f).obj K) := by
  simp only [pullbackFamilySquareComparison_hom_app, Category.assoc, Functor.map_comp]
  rw [← cancel_epi ((c f' g).hom.app ((H Y).obj K)), Iso.hom_inv_id_app_assoc,
    reassoc_of% (hθ.hom_app f' g K), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_map,
    ← reassoc_of% (pullbackPseudonatural_eqToHom (θ := θ) h.symm K), ← hθ.hom_app g' f K]

/-- **Transport of base-change morphisms**: under a pseudonatural family `θ` compatible with the
units and counits through `ψ`, if the base-change morphism of `P` along a commutative square is an
isomorphism at `H K`, then the image under `H` of the base-change morphism of `L` at `K` is an
isomorphism. -/
lemma PullbackPseudonatural.isIso_map_pushforwardBaseChange_app (hθ : PullbackPseudonatural c Lc θ)
    {RL : ∀ {X Y : C}, (X ⟶ Y) → E X ⥤ E Y} {RP : ∀ {X Y : C}, (X ⟶ Y) → D X ⥤ D Y}
    (adjL : ∀ {X Y : C} (f : X ⟶ Y), L f ⊣ RL f) (adjP : ∀ {X Y : C} (f : X ⟶ Y), P f ⊣ RP f)
    (ψ : ∀ {X Y : C} (f : X ⟶ Y), H X ⋙ RP f ≅ RL f ⋙ H Y)
    (hunit : ∀ {X Y : C} (f : X ⟶ Y) (K : E Y), (H Y).map ((adjL f).unit.app K) =
      (adjP f).unit.app ((H Y).obj K) ≫ (RP f).map ((θ f).hom.app K) ≫
        (ψ f).hom.app ((L f).obj K))
    (hcounit : ∀ {X Y : C} (f : X ⟶ Y) (K : E X), (P f).map ((ψ f).hom.app K) ≫
      (θ f).hom.app ((RL f).obj K) ≫ (H X).map ((adjL f).counit.app K) =
        (adjP f).counit.app ((H X).obj K))
    (h : g' ≫ f = f' ≫ g) (hiso : IsIso (pushforwardBaseChange c adjP h)) (K : E X) :
    IsIso ((H Y').map ((pushforwardBaseChange Lc adjL h).app K)) :=
  have : IsIso (Adjunction.exchangeRight (adjP f) (adjP f')
      (CategoryTheory.pullbackFamilySquareComparison c h)) := hiso
  Adjunction.isIso_map_exchangeRight_app_of_comm (adjL f) (adjL f')
    (CategoryTheory.pullbackFamilySquareComparison Lc h) (adjP f) (adjP f')
    (CategoryTheory.pullbackFamilySquareComparison c h) (θ f) (ψ f) (θ f') (ψ f') (θ g) (θ g')
    (hunit f') (hcounit f) (hθ.pullbackFamilySquareComparison h) K

end CategoryTheory
