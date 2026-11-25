/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelReduction
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Connected etale presentations before choosing local stalk markings

## References

* Stacks Project, Tags 09AL, 09B1 and 09C6, before local constancy
* Stacks Project, the paragraph constructing the normalized algebraic diagram, before local
  constancy
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] constantAdicQuotientRealization

/-- Etale origins and scalar-normalized stalk arrows on one connected chart.
The transport field only transports a supplied isomorphism; it asserts no local
markings or covering sieves of markings. -/
structure LisseTowerConnectedEtalePresentation
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (V : Y.Etale) where
  connected : ConnectedSpace V.left
  point : V.left
  level : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  bounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (level n))
  lisse : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj (level n))
  vanishing : ∀ (n : ℕ) (q : ℤ),
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (level n))
  transition : ∀ n : ℕ,
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1))))
      (Functor.additive_of_preserves_binary_products _) _ _).obj (level (n + 1)) ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n))
  universal : ∀ (n : ℕ)
    (N : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
    Function.Bijective (fun k :
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
          (AdicCompletion d.ideal A ⧸
            (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
        (Functor.additive_of_preserves_binary_products _) _ _).obj (level n) ⟶ N ↦
          transition n ≫
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (I := d.ideal.map
                (algebraMap A (AdicCompletion d.ideal A)))
                (Nat.le_succ (n + 1))))).mapDerivedCategory.map k)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (n : ℕ) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj (M.level n))))
  transport : ∀ (n : ℕ) (Z : V.left.Etale),
    Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj (level n) ≅
      (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n))) →
    ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))),
      Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n)) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))

/-- Connected components of affine neighborhoods give pointed connected open charts. -/
private theorem connected_etale_chart (Y : Scheme.{u}) [IsLocallyNoetherian Y] (y : Y) :
    ∃ (V : Y.Etale) (v : V.left), ConnectedSpace V.left ∧ V.hom v = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have : IsAffine U.toScheme := hU
  have : IsNoetherian U.toScheme := ⟨⟩
  let u : U.toScheme := ⟨y, hy⟩
  let C : U.toScheme.Opens :=
    ⟨connectedComponent u, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent u⟩
  have hC : ConnectedSpace C.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := u))
  exact ⟨Etale.mk (C.ι ≫ U.ι), ⟨u, mem_connectedComponent⟩, hC, rfl⟩

/-- Restrict a supplied constant model along one further etale arrow. -/
private def restrict_constant_model
    (Y U W : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (f : U ⟶ Y) (g : W ⟶ U) (h : W ⟶ Y) (hg : g ≫ f = h)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (E : DerivedCategory (ModuleCat.{u + 1} B))
    (e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E) :
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj K ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E :=
  ((Functor.mapDerivedCategoryNatIso
    (AlgebraicGeometry.Etale.upperStarComp (ModuleCat.{u + 1} B) g f h hg.symm)).app K) ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).app K).symm ≪≫
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarConstantSheafIso (ModuleCat.{u + 1} B) g)).app E

/-- Assemble one supplied pointed connected chart before choosing the base cover. -/
private theorem pointed_chart_presentation
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n)))))
    (V : Y.Etale) (v : V.left) (hconn : ConnectedSpace V.left) :
    Nonempty (LisseTowerConnectedEtalePresentation X Y g d M V) := by
  classical
  let D (n : ℕ) := (lisse_finite_quotient_etale_origin X Y g d n
    (M.level n) (hbounded n) (hlisse n) (V)).some
  have hb (n : ℕ) : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (D n).level) := by
    obtain ⟨a, b, hab⟩ := hbounded n
    exact ⟨a, b, fun q hq ↦ (D n).vanishing q (hab q hq)⟩
  let E (n : ℕ) :=
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((V.left.uliftPointSmallEtale v).sheafFiber
        (A := ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
      (Functor.additive_of_preserves_binary_products _) _ _).obj (D n).level
  have hred (n : ℕ) : ∃ t : E (n + 1) ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A)))
          (Nat.le_succ (n + 1))))).mapDerivedCategory.obj (E n),
      ∀ N : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))),
        Function.Bijective (fun k : E n ⟶ N ↦ t ≫
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := d.ideal.map
              (algebraMap A (AdicCompletion d.ideal A)))
              (Nat.le_succ (n + 1))))).mapDerivedCategory.map k) := by
    have : etalePrecoverage.{u}.IsStableUnderComposition :=
      inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderComposition
    have : etalePrecoverage.{u}.IsStableUnderBaseChange :=
      inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange
    have : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
    have hfin (m : ℕ) : Finite (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (m + 1)) := by
      have : Finite (A ⧸ d.ideal ^ (m + 1)) := d.quotientFinite m
      exact Finite.of_surjective (constantAdicQuotientMap d.ideal m)
        (quotient_map_bijective d.ideal d.finitelyGenerated m).2
    let := hfin n
    let := hfin (n + 1)
    let B' := AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1)
    let B := AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)
    obtain ⟨𝒰, h𝒰⟩ :=
      (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy V.left B'
        (D (n + 1)).level (hb (n + 1)) (D (n + 1)).lisse).2.2.2
          hconn _ (V.left.algClosurePoint v)
    obtain ⟨𝒲, h𝒲⟩ :=
      (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy V.left B
        (D n).level (hb n) (D n).lisse).2.2.2
          hconn _ (V.left.algClosurePoint v)
    -- Only these two markings need to coexist over a point.
    let 𝒵 : Cover.{u} etalePrecoverage V.left := 𝒰.inter 𝒲
    obtain ⟨j, z, -⟩ := 𝒵.exists_eq v
    let Z : Y.Etale := Etale.mk (𝒵.f j ≫ V.hom)
    have e' : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B')
        (𝒵.f j)).mapDerivedCategory.obj (D (n + 1)).level ≅
        (constantSheaf (𝒵.X j).smallEtaleTopology
          (ModuleCat.{u + 1} B')).mapDerivedCategory.obj (E (n + 1)) :=
      restrict_constant_model V.left (𝒰.X j.1) (𝒵.X j) B' (𝒰.f j.1)
        (pullback.fst (𝒰.f j.1) (𝒲.f j.2)) (𝒵.f j) rfl
        (D (n + 1)).level (E (n + 1)) (h𝒰 j.1).some
    have e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B)
        (𝒵.f j)).mapDerivedCategory.obj (D n).level ≅
        (constantSheaf (𝒵.X j).smallEtaleTopology
          (ModuleCat.{u + 1} B)).mapDerivedCategory.obj (E n) :=
      restrict_constant_model V.left (𝒲.X j.2) (𝒵.X j) B (𝒲.f j.2)
        (pullback.snd (𝒰.f j.1) (𝒲.f j.2)) (𝒵.f j)
        pullback.condition.symm (D n).level (E n) (h𝒲 j.2).some
    exact constantAdicQuotient_model_reduction X Y g d M n Z z (E (n + 1)) (E n)
      ((D (n + 1)).transport (𝒵.etalePrecoverageToEtale j) (E (n + 1)) ⟨e'⟩
        ((toProEt Y).obj Z) (𝟙 _))
      ((D n).transport (𝒵.etalePrecoverageToEtale j) (E n) ⟨e⟩
        ((toProEt Y).obj Z) (𝟙 _))
  choose t ht using hred
  exact ⟨{ connected := hconn
           point := v
           level := fun n ↦ (D n).level
           bounded := hb
           lisse := fun n ↦ (D n).lisse
           vanishing := fun n ↦ (D n).vanishing
           transition := t
           universal := ht
           refinementLisse := fun W w n q ↦ (D n).refinementLisse W w q
           transport := fun n Z e W w ↦ (D n).transport Z (E n) e W w }⟩

/-- Descend the finite levels on connected charts and take their actual geometric
stalks, retaining the scalar normalization and conditional coefficient transport.
No level is asserted locally isomorphic to its stalk in this theorem. -/
theorem lisse_tower_connected_etale_presentation
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒱.I₀,
      Nonempty (LisseTowerConnectedEtalePresentation X Y g d M
        (𝒱.etalePrecoverageToEtale i)) := by
  classical
  -- Each point supplies its own connected chart, so an empty Y needs no choices.
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X) g
  choose V v hconn hv using connected_etale_chart Y
  let 𝒱 : Cover.{u} etalePrecoverage Y :=
    Cover.mkOfCovers Y (fun y ↦ (V y).left) (fun y ↦ (V y).hom)
      (fun y ↦ ⟨y, v y, hv y⟩) (fun y ↦ (V y).prop)
  refine ⟨𝒱, fun i ↦ ?_⟩
  exact pointed_chart_presentation X Y g d M hbounded hlisse
    (𝒱.etalePrecoverageToEtale i) (v i) (hconn i)

end AlgebraicGeometry.Scheme
