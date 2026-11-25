/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.AffineKoszulFiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.LocalFiniteFreeHomologyNatural
import WeilConjectures.AlgebraicGeometry.AffineKoszulCoefficientHomCoordinates
/-! # Affine sheaf model of the Koszul Ext coefficient morphism

Source: Stacks Project, Tag 0BQZ, affine computation of regular immersion Ext. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry

-- Matching the natural coefficient functors unfolds both derived Hom coefficient objects.
/-- On the affine chart, the two Ext sheaves and their coefficient map are the
sheafifications of the dual Koszul cohomology modules and their reduction map.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext.
(blueprint: new-k1-koszul-ext-coefficient-affine-model).

Proof: The closed immersion on the chart is the quotient spectrum for the kernel
ideal. Augment the Koszul complex by its degree-zero quotient map. Koszul
regularity makes this a resolution, and its exterior terms are finite free and
zero above n. Sheafification on the affine chart is exact, so it resolves the
restricted pushforward of the structure sheaf. Extend the chain complex to
nonpositive integer cochain degrees. Apply the bounded finite free internal Hom
comparison with coefficients O and the quotient sheaf. Use a common K-injective
comparison to make both identifications natural in the coefficient variable.
The supplied equality ha identifies the coefficient map with the quotient map,
which acts on Hom cochains by reduction of values. In degree k the differential
is (-1)^(k+1) times precomposition with the Koszul boundary for both coefficients,
so these are precisely the two recorded natural-number dual complexes after
extension to integer degrees. The degree-m homology comparisons for this
extension commute with the reduction map. Tilde preserves finite limits by
tilde_preserves_finite_limits and colimits by its adjunction, hence is exact.
Restriction along the chart is an exact equivalence. They commute with homology
and its maps, producing the two sheaf isomorphisms and their square.
Work through representatives in the supplied derived universe, so no derived
category on the chart in a different universe is compared. For n=0 the quotient
ideal is zero and the resolution is the degree-zero ring; for m>n both Hom
cohomology modules vanish. These cases require no additional hypotheses. -/
theorem koszulExtCoefficient_affine_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n m : ℕ)
    (U : Y.affineOpens) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let F := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj (SheafOfModules.unit Y.ringCatSheaf)))
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let c : F ⟶ G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).map
        (H.map (𝟙 (op (S.obj B)), S.map a))
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let P := (ExteriorAlgebra.koszulDualComplex A n f).homology m
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m
    let q := HomologicalComplex.homologyMap
      (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m
    ∃ (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj P)
      (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj Q),
      (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map q := by
  obtain ⟨P₀, hP₀⟩ := ExteriorAlgebra.exists_koszul_projective_resolution
    (Γ(Y, U.1) : Type u) (i.ker.ideal U) n f hreg hf
  let ε₀ := eqToHom hP₀.symm ≫ P₀.π
  have : QuasiIso ε₀ := by dsimp [ε₀]; infer_instance
  let ε := HomologicalComplex.extendMap ε₀ ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of (Γ(Y, U.1) : Type u)
        ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)) 0 (0 : ℤ) rfl).hom
  have : QuasiIso ε := by dsimp [ε]; infer_instance
  obtain ⟨hbounded, hfree, b, hb⟩ := affine_koszul_finite_free_resolution i U n f ε
  let := hb
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let K := ExteriorAlgebra.koszulComplex A n f
  let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (K.extend ComplexShape.embeddingDownNat)
  have hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p) := by
    classical
    refine ⟨-(n : ℤ), ?_⟩
    intro p hp
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (show p ≤ 0 by omega)
    have hnk : n < k := by omega
    let b := (Finsupp.basisSingleOne : Module.Basis (Fin n) A
      (Fin n →₀ A)).exteriorPower k
    have : IsEmpty (Set.powersetCard (Fin n) k) := ⟨fun s ↦ by
      have h := Finset.card_le_univ s.val
      have hs : s.val.card = k := s.property
      simp only [Fintype.card_fin, hs] at h
      omega⟩
    have : Subsingleton (⋀[A]^k (Fin n →₀ A)) := b.repr.injective.subsingleton
    have hz : IsZero (ModuleCat.of A (⋀[A]^k (Fin n →₀ A))) :=
      ModuleCat.isZero_of_subsingleton _
    exact (T.map_isZero hz).of_iso
      (T.mapIso (K.extendXIso ComplexShape.embeddingDownNat rfl))
  obtain ⟨e⟩ := local_finite_free_homology_natural U.1
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    E hbounded hbelow hfree b (m : ℤ)
  obtain ⟨eF, eG, hsquare⟩ := affine_koszul_coefficient_hom_coordinates i U n m f a ha
  refine ⟨e.app (SheafOfModules.unit Y.ringCatSheaf) ≪≫ eF,
    e.app ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) ≪≫ eG,
    ?_⟩
  have hn := congrArg (fun t ↦ t ≫ eG.hom) (e.hom.naturality a)
  simp only [Category.assoc] at hn
  have hs := congrArg (fun t ↦ e.hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫ t)
    hsquare
  simpa only [Functor.comp_map, Functor.curry_obj_obj_map, Prod.mkHom,
    Iso.trans_hom, Iso.app_hom, Category.assoc] using hn.trans hs

end AlgebraicGeometry
