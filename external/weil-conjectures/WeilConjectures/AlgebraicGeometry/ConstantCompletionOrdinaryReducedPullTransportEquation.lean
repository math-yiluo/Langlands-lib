/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullExistence
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullUniqueness

/-! # Normalized ordinary reduced transport equation

This records the normalized comparison equation after both transports have been
constructed.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

attribute [local irreducible] completed derivedExtension

omit hL in
private theorem pullInsertion_naturality {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) :
    pullInsertion F c M ≫ (underlying S).map ((pull F c).map f) =
      L.map ((underlying R).map f) ≫ pullInsertion F c N := by
  dsimp only [pullInsertion, pull, Functor.comp_map]
  erw [Category.assoc, finiteInsertion_naturality J' c,
    ← Category.assoc, ← (F.algebra R).moduleUnderlying.inv.naturality f, Category.assoc]

private theorem finiteComparison_insertion (K : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (M : Mod (completed K A I)) :
    insertion (quotient K A I n) ((res (coefficientMap K A I)).obj M) ≫
        (underlying (finite K A I n)).map ((finiteComparison K A I n).hom.app M) =
      insertion (projection K A I n) M := by
  ext U m
  change ((finiteComparison K A I n).hom.app M).val.app U
    ((insertion (quotient K A I n) ((res (coefficientMap K A I)).obj M)).hom.app U m) =
    (insertion (projection K A I n) M).hom.app U m
  have hq := (insertion_existsUnique (quotient K A I n)
    ((res (coefficientMap K A I)).obj M)).exists.choose_spec
  have hp := (insertion_existsUnique (projection K A I n) M).exists.choose_spec
  change ∀ U m, (insertion (quotient K A I n)
    ((res (coefficientMap K A I)).obj M)).hom.app U m = _ at hq
  change ∀ U m, (insertion (projection K A I n) M).hom.app U m = _ at hp
  rw [hq, hp]
  exact (finiteComparison_existsUnique K A I n).exists.choose_spec M U 1 m

include V adj hL in
private theorem pullScalar_exists {R S : Sheaf J CommRingCat.{u}}
    {B T : Sheaf J' CommRingCat.{u}} (a : R ⟶ S)
    (c : F.rings.obj R ⟶ B) (b : B ⟶ T) (d : F.rings.obj S ⟶ T)
    (hq : c ≫ b = F.rings.map a ≫ d) :
    ∃ e : pull F c ⋙ change b ≅ change a ⋙ pull F d,
      ∀ M : Mod R, pullInsertion F c M ≫
          insertion b ((pull F c).obj M) ≫ (underlying T).map (e.hom.app M) =
        L.map (insertion a M) ≫ pullInsertion F d ((change a).obj M) := by
  obtain ⟨v, hv⟩ := finiteInverseScalar_exists J (F := F) V adj (a)
  obtain ⟨s, hs⟩ := finiteScalarComposite_exists J' (c) (b)
    (F.rings.map (a) ≫ d) hq
  obtain ⟨t, ht⟩ := finiteScalarComposite_exists J' (F.rings.map (a))
    (d) _ rfl
  let e : pull F (c) ⋙ change (b) ≅
      change (a) ⋙ pull F (d) :=
    Functor.isoWhiskerLeft (F.algebra (R)).modules s ≪≫
      Functor.isoWhiskerLeft (F.algebra (R)).modules t.symm ≪≫
      Functor.isoWhiskerRight v (change (d))
  refine ⟨e, ?_⟩
  intro M
  let N := (F.algebra (R)).modules.obj M
  let B := T
  have ht' :
      insertion (F.rings.map (a) ≫
          d) N ≫ (underlying B).map (t.inv.app N) =
        insertion (F.rings.map (a)) N ≫
          insertion (d)
            ((change (F.rings.map (a))).obj N) := by
    rw [← ht N]
    change (insertion (F.rings.map (a)) N ≫
      insertion (d)
        ((change (F.rings.map (a))).obj N) ≫
      (underlying B).map (t.hom.app N)) ≫ (underlying B).map (t.inv.app N) = _
    simp only [Category.assoc, ← (underlying B).map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id]
  have hn :
      insertion (d)
          ((change (F.rings.map (a))).obj N) ≫
        (underlying B).map
          ((change (d)).map (v.hom.app M)) =
      (underlying (F.rings.obj (S))).map (v.hom.app M) ≫
        insertion (d)
          ((F.algebra (S)).modules.obj ((change (a)).obj M)) := by
    exact finiteInsertion_naturality J' (d)
      (v.hom.app M)
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [pullInsertion, pull, Functor.comp_obj]
  simp only [Category.assoc]
  exact finiteInsertion_chain (hs N) ht' hn (hv M)

omit hL in
private theorem doubleInsertion_ext {R : Sheaf J CommRingCat.{u}}
    {S T : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S) (b : S ⟶ T)
    (M : Mod R) (N : Mod T)
    (f g : (change b).obj ((pull F c).obj M) ⟶ N)
    (h : pullInsertion F c M ≫ insertion b ((pull F c).obj M) ≫
        (underlying T).map f =
      pullInsertion F c M ≫ insertion b ((pull F c).obj M) ≫
        (underlying T).map g) : f = g := by
  apply ((finiteScalarAdj b).homEquiv _ _).injective
  apply ((finiteScalarAdj c).homEquiv _ _).injective
  apply (underlying (F.rings.obj R)).map_injective
  apply (cancel_epi ((F.algebra R).moduleUnderlying.inv.app M)).mp
  erw [finitePull_homEquiv J F c M ((res b).obj N)
      (((finiteScalarAdj b).homEquiv _ _) f),
    finitePull_homEquiv J F c M ((res b).obj N)
      (((finiteScalarAdj b).homEquiv _ _) g),
    finiteScalar_homEquiv b ((pull F c).obj M) N f,
    finiteScalar_homEquiv b ((pull F c).obj M) N g]
  exact h

attribute [local semireducible] completed

omit hL in
private theorem completedMap_projection (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    completedMap F A I ≫ projection J' A I n =
      F.rings.map (projection J A I n) ≫ constantMap F (A ⧸ I ^ (n + 1)) := by
  simp only [completedMap, projection, limit.lift_π]
  rfl

attribute [local irreducible] completed

-- Two adjunction units and four whiskered isomorphisms require extra elaboration heartbeats.
omit hL in
/-- The ordinary comparison admits compatible transports to the canonical finite model.
The source and target isomorphisms are chosen with their insertion normalizations;
arbitrary independently chosen isomorphisms need not satisfy the equation.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL and 093M;
sites-cohomology.tex, Tag 06YY.
Proof: construct normalized scalar reassociation on both sides, use the finite
coefficient comparison on each site, and compare on the two scalar-extension units.
Their adjunctions make that comparison faithful.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_transport_eq
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [hL : PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅
        (change (projection J A I n) ⋙
          pull F (constantMap F (A ⧸ I ^ (n + 1)))))
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
        (change (projection J A I n) ⋙
          pull F (constantMap F (A ⧸ I ^ (n + 1))))),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom := by
  obtain ⟨e, he⟩ := ordinaryFinitePull_exists (J := J) (F := F) V adj A I n
  have hp := completedMap_projection F A I n
  obtain ⟨d, hd⟩ := pullScalar_exists F V adj (projection J A I n)
    (completedMap F A I) (projection J' A I n)
    (constantMap F (A ⧸ I ^ (n + 1))) hp
  let s := Functor.isoWhiskerLeft (res (coefficientMap J A I)) e ≪≫
    Functor.isoWhiskerRight (finiteComparison J A I n)
      (pull F (constantMap F (A ⧸ I ^ (n + 1))))
  let t := Functor.isoWhiskerLeft (pull F (completedMap F A I))
      (finiteComparison J' A I n) ≪≫ d
  refine ⟨s, t, ?_⟩
  apply NatTrans.ext
  funext M
  apply doubleInsertion_ext F (constantMap F A) (quotient J' A I n)
    ((res (coefficientMap J A I)).obj M)
  have hs : pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
      insertion (quotient J' A I n)
        ((pull F (constantMap F A)).obj ((res (coefficientMap J A I)).obj M)) ≫
      (underlying (finite J' A I n)).map (s.hom.app M) =
      L.map (insertion (projection J A I n) M) ≫
        pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
          ((change (projection J A I n)).obj M) := by
    dsimp only [s, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    erw [Functor.map_comp, reassoc_of% he ((res (coefficientMap J A I)).obj M),
      pullInsertion_naturality F (constantMap F (A ⧸ I ^ (n + 1)))
        ((finiteComparison J A I n).hom.app M),
      ← Category.assoc, ← L.map_comp, finiteComparison_insertion J A I n M]
  have ht : pullInsertion F (completedMap F A I) M ≫
      insertion (quotient J' A I n)
        ((res (coefficientMap J' A I)).obj ((pull F (completedMap F A I)).obj M)) ≫
      (underlying (finite J' A I n)).map (t.hom.app M) =
      L.map (insertion (projection J A I n) M) ≫
        pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
          ((change (projection J A I n)).obj M) := by
    dsimp only [t, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    erw [Functor.map_comp, reassoc_of%
      (finiteComparison_insertion J' A I n ((pull F (completedMap F A I)).obj M))]
    exact hd M
  have hq := (ordinaryPullComparison_existsUnique F A I).exists.choose_spec M
  change pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
      (underlying (constant J' A)).map ((ordinaryPullComparison F A I).app M) =
      pullInsertion F (completedMap F A I) M at hq
  change pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
      insertion (quotient J' A I n) _ ≫
      (underlying (finite J' A I n)).map
        ((change (quotient J' A I n)).map ((ordinaryPullComparison F A I).app M) ≫
          t.hom.app M) = _
  erw [Functor.map_comp, reassoc_of%
    (finiteInsertion_naturality J' (quotient J' A I n) ((ordinaryPullComparison F A I).app M))]
  erw [← Category.assoc, hq]
  exact ht.trans hs.symm

end CategoryTheory.ConstantCompletion
