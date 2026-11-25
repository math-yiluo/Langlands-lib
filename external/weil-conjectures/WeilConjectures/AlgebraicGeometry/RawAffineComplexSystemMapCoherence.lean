/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyPullbackLaws

/-! # Coherence of canonical complex cohomology maps

Source: Stacks Project, Tag 0EZM, canonical maps; Tags 015J and 015K.
(blueprint: lem-sbc-raw-affine-complex-system-map-coherence).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private noncomputable def pairMap {X Y : Scheme.{v}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (a : ((upperStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :=
  rawAffineComplexPullback p f K ≫
    (cohomology AddCommGrpCat.{v + 1} Y p).map (DerivedCategory.Q.map a)

private lemma pairMap_spec {X Y : Scheme.{v}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (a : ((upperStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :
    pairMap f K L a p = (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} p).map
      ((rightDerivedGlobalSections AddCommGrpCat.{v + 1} X).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} f).hom.app
            ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategory.obj
              (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y).map
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryFactors.hom.app K ≫
            DerivedCategory.Q.map a)) := by
  simp only [pairMap, rawAffineComplexPullback, cohomology, Functor.comp_map,
    Functor.map_comp, Category.assoc, rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
    lowerStarCompGlobalSectionsIso]

private lemma pairMap_congr {X Y : Scheme.{v}} (f g : Y ⟶ X) (h : f = g)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (a : ((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :
    pairMap f K L
      ((NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) h))
          (ComplexShape.up ℤ)).hom.app K ≫ a) p = pairMap g K L a p := by
  subst g
  simp [NatIso.mapHomologicalComplex]

private lemma pairMap_comp {X Y Z : Scheme.{v}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) (hh : h = g ≫ f)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (M : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (N : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (hK : CochainComplex.plus _ K) (hM : CochainComplex.plus _ M)
    (hN : CochainComplex.plus _ N)
    (a : ((upperStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ M)
    (b : ((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N) (p : ℤ) :
    pairMap h K N
      ((NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{v + 1} g f h hh) (ComplexShape.up ℤ)).hom.app K ≫
        ((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a ≫ b) p =
      pairMap f K M a p ≫ pairMap g M N b p := by
  subst h
  exact (derivedEtaleCohomology_pullback_laws pairMap @pairMap_spec).2
    f g ⟨K, hK⟩ ⟨M, hM⟩ ⟨N, hN⟩ a b p

/-- Canonical cohomology maps of a coherent inverse-image complex system obey
identity, composition and cone-leg equations.
Source: Stacks Project, Tag 0EZM, canonical maps; Tags 015J and 015K.
(blueprint: lem-sbc-raw-affine-complex-system-map-coherence).

Proof: Define the pair map as rawAffineComplexPullback followed by the
coefficient map and identify it with the formula in
derivedEtaleCohomology_pullback_laws. Apply that existing theorem to the
bounded-below stage complexes and the bounded-below cocone vertex. Rewrite
psi using hidentity and hcomposition and transport across D.map_id and
D.map_comp. For the cone-leg equation, precompose cocone naturality with
eG_i.inv, rewrite hG and cancel eG_i.inv followed by eG_i.hom. Apply the
existing composition law to D.map f and c.pi_j; the cone equation identifies
the composite with c.pi_i, and the coefficient equality gives the desired
leg equation. No limiting or colimiting universal property, affineness,
quasi-compactness or cohomology continuity assertion is used. -/
theorem rawAffineComplex_system_map_coherence {J : Type v} [SmallCategory J]
    (D : J ⥤ Scheme.{v}) (c : Cone D)
    (K : ∀ i : J, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (hK : ∀ i : J, CochainComplex.plus _ (K i))
    (ψ : ∀ {i j : J} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : J, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : J) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (G : (J)ᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : J, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : J) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : CochainComplex.plus _ L.pt) (p : ℤ) :
    let m := fun {i j : J} (f : j ⟶ i) ↦
      rawAffineComplexPullback p (D.map f) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (ψ f))
    let b := fun i : J ↦
      rawAffineComplexPullback p (c.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))
    (∀ i : J, m (𝟙 i) = 𝟙 _) ∧
      (∀ (i j k : J) (f : j ⟶ i) (g : k ⟶ j), m (g ≫ f) = m f ≫ m g) ∧
      (∀ (i j : J) (f : j ⟶ i), m f ≫ b j = b i) := by
  have hid := (derivedEtaleCohomology_pullback_laws pairMap @pairMap_spec).1
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change pairMap (D.map (𝟙 i)) (K i) (K i) (ψ (𝟙 i)) p = _
    rw [hidentity, pairMap_congr _ _ (D.map_id i)]
    exact hid (D.obj i) ⟨K i, hK i⟩ p
  · intro i j k f g
    change pairMap (D.map (g ≫ f)) (K i) (K k) (ψ (g ≫ f)) p =
      pairMap (D.map f) (K i) (K j) (ψ f) p ≫
        pairMap (D.map g) (K j) (K k) (ψ g) p
    rw [hcomposition]
    exact pairMap_comp (D.map f) (D.map g) _ (D.map_comp g f)
      (K i) (K j) (K k) (hK i) (hK j) (hK k) (ψ f) (ψ g) p
  · intro i j f
    have hv :
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
          ((upperStar AddCommGrpCat.{v + 1} (c.π.app j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (ψ f) ≫
          (eG j).inv ≫ L.ι.app (op j) = (eG i).inv ≫ L.ι.app (op i) := by
      have hn := L.w f.op
      rw [hG] at hn
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun a ↦ (eG i).inv ≫ a) hn
    change pairMap (D.map f) (K i) (K j) (ψ f) p ≫
      pairMap (c.π.app j) (K j) L.pt ((eG j).inv ≫ L.ι.app (op j)) p =
        pairMap (c.π.app i) (K i) L.pt ((eG i).inv ≫ L.ι.app (op i)) p
    rw [← pairMap_comp (D.map f) (c.π.app j) (c.π.app i) (c.w f).symm
      (K i) (K j) L.pt (hK i) (hK j) hL]
    rw [hv]

end AlgebraicGeometry.Etale
