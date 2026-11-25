/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.PrincipalCechBicomplexComparison

/-! # Finite-column bicomplex models for principal Čech maps

Source: Stacks, Tag 08D1; the finite Čech-degree filtration in Tag 08C2
(blueprint: lem-sc-principal-cech-finite-column-model).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A principal Čech map is a total map of bicomplexes supported in columns 0,...,r-1.
Column quasi-isomorphisms require only the section quasi-isomorphisms on intersections.
No quasi-coherence, K-injectivity or quasi-isomorphism assumption is made on i itself.
Source: Stacks, Tag 08D1, and the finite Čech-degree filtration used in Tag 08C2
(blueprint: lem-sc-principal-cech-finite-column-model).

Proof:
1. In column p, for 0 ≤ p < r, take the finite product of section complexes on D(f_S)
   over subsets S of cardinality p+1. Outside that interval use the zero complex.
   Horizontal maps are alternating sums of restrictions, with the sign determined by
   the position of the deleted index. Vertical maps are the coefficient differentials.
   Two deletions cancel in pairs. Restrictions commute with coefficient differentials,
   so these are commuting double complexes K and L; apply i componentwise to obtain φ.
2. The absent columns give the stated strict support bounds. Module categories have
   all coproducts, so K and L have totals. Each column map is the finite product of the
   section maps. Products of modules are exact, so the intersection hypothesis makes
   every retained column map a quasi-isomorphism. Outside the interval the map is zero
   between zero complexes and is also a quasi-isomorphism.
3. In total degree n, send the summand indexed by (p,n-p) to the coordinates indexed
   by subsets of cardinality p+1 in principalCechTerms. The inverse groups coordinates
   by their cardinalities. Only r columns can be nonzero, so the categorical diagonal
   coproduct and the displayed finite coordinate product agree. The total differential
   is horizontal restriction plus (-1)^p times the vertical differential, exactly
   principalCechDifferentialValue. Thus these degreewise identifications are chain
   isomorphisms. The componentwise equation from principalCechFunctor_exists shows
   that they intertwine the two maps. Compose with principalCechObjIso to obtain the
   arrow isomorphism below. For r=0 all columns and all coordinates are zero; for r=1
   only the singleton row occurs. Empty intersections contribute zero section modules.
   This construction uses no boundedness in the coefficient-complex degree. -/
theorem principalCech_finiteColumn_model
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F G : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (i : F ⟶ G) :
    ∃ (K L : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) (φ : K ⟶ L),
      CochainComplex.IsStrictlyGE K 0 ∧ CochainComplex.IsStrictlyLE K ((r : ℤ) - 1) ∧
      CochainComplex.IsStrictlyGE L 0 ∧ CochainComplex.IsStrictlyLE L ((r : ℤ) - 1) ∧
      (∀ p : ℤ, 0 ≤ p → p ≤ (r : ℤ) - 1 →
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          QuasiIso (((affineOpenSections A
            (principalCechIntersection r f S.val)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map i)) → QuasiIso (φ.f p)) ∧
      Nonempty (Arrow.mk ((principalCechFunctor r f).map i) ≅
        Arrow.mk (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ))) := by
  refine ⟨principalCechBicomplex r f F, principalCechBicomplex r f G,
    (principalCechBicomplexFunctor r f).map i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyGE_iff _ 0).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inl hp) F
  · apply (CochainComplex.isStrictlyLE_iff _ ((r : ℤ) - 1)).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inr hp) F
  · apply (CochainComplex.isStrictlyGE_iff _ 0).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inl hp) G
  · apply (CochainComplex.isStrictlyLE_iff _ ((r : ℤ) - 1)).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inr hp) G
  · intro p _ _ hi
    exact principalCechColumn_quasiIso r f p F G i hi
  · obtain ⟨e⟩ := principalCechBicomplexComparison_exists r f
    exact ⟨Arrow.isoOfNatIso e (Arrow.mk i)⟩

end AlgebraicGeometry
