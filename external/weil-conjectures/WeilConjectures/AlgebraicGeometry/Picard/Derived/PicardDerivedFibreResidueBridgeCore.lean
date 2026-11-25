/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreResidueGeometricCompatibility
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreResidueAffineData

/-! Fixed-model naturality core for the derived fibre residue bridge.

## Implementation details

Apply the affine residue model naturality theorem to the coefficient
arrow and choose a chain representative by the affine perfect map theorem.
Compose the residue-to-derived-fibre comparisons with the geometric residue
comparisons.  Naturality of the geometric residue comparison gives the two
required equations simultaneously for every index.

## References

* Stacks Project, Tags 01IB, 064K, 06YJ and 0B91
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Compose the two naturality squares before specializing their cohomology groups. -/
private theorem residue_bridge_of_naturality
    {I : Type*} {Φ : I → Type*} (P : ∀ i, Φ i → Prop)
    {M A B : Type*} {N C D : I → Type*}
    [Add M] [Add A] [Add B] [∀ i, Add (N i)] [∀ i, Add (C i)] [∀ i, Add (D i)]
    (eM : M ≃+ A) (eN : ∀ i, N i ≃+ C i)
    (u : ∀ i, A → C i) (v : ∀ i, Φ i → M → N i) (g : ∀ i, B → D i)
    (ha : ∃ φ : ∀ i, Φ i, ∀ i, P i (φ i) ∧
      ∀ z, eN i (v i (φ i) z) = u i (eM z))
    (hg : ∃ (e : A ≃+ B) (ei : ∀ i, C i ≃+ D i),
      ∀ i z, ei i (u i z) = g i (e z)) :
    ∃ (φ : ∀ i, Φ i) (e : A ≃+ B) (ei : ∀ i, C i ≃+ D i), ∀ i,
      P i (φ i) ∧ (∀ z, ei i (u i z) = g i (e z)) ∧
        ∀ z, ((eN i).trans (ei i)) (v i (φ i) z) = g i (eM.trans e z) := by
  obtain ⟨φ, hφ⟩ := ha
  obtain ⟨e, ei, he⟩ := hg
  refine ⟨φ, e, ei, fun i ↦ ⟨(hφ i).1, he i, fun z ↦ ?_⟩⟩
  exact (congrArg (ei i) ((hφ i).2 z)).trans (he i _)

-- The fixed-model naturality traverses derived and residue comparisons.
/-- For fixed strictly perfect affine models, the coefficient arrows have chain
representatives, and the canonical affine residue comparisons followed by geometric fibre
comparisons `e`, `ei` (which intertwine the derived coefficient arrows with structure-sheaf
pullback) intertwine the residue cycle homology maps with structure-sheaf pullback. -/
theorem picard_derived_fibre_residue_bridge_core
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (m : ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅ DerivedCategory.Q.obj K))
    (m' : ∀ i, ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (φ : ∀ i, K ⟶ C i)
      (e : derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (ei : ∀ i, derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
              ((Modules.tensorPullback (ui i)).obj L)))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i, DerivedCategory.Q.map (φ i) = m.inv ≫ (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
            (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (m' i).hom ∧
        (∀ z, ei i ((derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
          structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (e z)) ∧
        ∀ z, ((affineResidueModelEquiv W w U hwU hU p hp _ (C i) (hC i) (m' i)).trans (ei i))
            (affineResidueCycleHomologyMap (φ i) z) =
          structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1
            ((affineResidueModelEquiv W w U hwU hU p hp _ K hK m).trans e z) := by
  refine residue_bridge_of_naturality (Φ := fun i ↦ K ⟶ C i)
    (fun i φ ↦ DerivedCategory.Q.map φ = m.inv ≫
      (SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
        (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (m' i).hom)
    (affineResidueModelEquiv W w U hwU hU p hp _ K hK m)
    (fun i ↦ affineResidueModelEquiv W w U hwU hU p hp _ (C i) (hC i) (m' i))
    (fun i ↦ (derivedFiberCohomologyFunctor W w 1).map
      (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k))
    (fun _ φ z ↦ affineResidueCycleHomologyMap φ z)
    (fun i ↦ structureSheafCohomologyPullback
      (((Over.pullback (S.fromSpecResidueField s)).map
        (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1) ?_ ?_
  · exact picard_derived_fibre_residue_affine_data
      f Xi fi ui hui L W k w s hw τ U hwU hU p hp K C hK hC m m'
  · exact picard_derived_fibre_residue_geometric_compatibility
      f Xi fi ui hui L W k w s hw τ

end AlgebraicGeometry.Scheme
