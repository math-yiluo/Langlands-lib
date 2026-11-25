/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalCechHorizontalSquare
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupNaturality

/-! # The explicit Čech bicomplex and its total comparison

Source: Stacks, Tag 08D1, total differential of the alternating Čech double complex
(blueprint: lem-sc-principal-cech-bicomplex-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

/-- The Čech bicomplex constructed from product columns and alternating restrictions.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-bicomplex-comparison). -/
def principalCechBicomplex
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.of (fun p ↦ (principalCechColumnFunctor r f p).obj F)
    (fun p ↦ (principalCechHorizontal r f p).app F)
    (by exact principalCechHorizontal_square A r f F)

/-- Coefficient maps act on every product column.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-bicomplex-comparison). -/
def principalCechBicomplexFunctor :
    CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  obj := principalCechBicomplex r f
  map i :=
    { f p := (principalCechColumnFunctor r f p).map i
      comm' := by
        intro p q hpq
        obtain rfl : p + 1 = q := hpq
        simp only [principalCechBicomplex, CochainComplex.of_d]
        exact (principalCechHorizontal r f p).naturality i }
  map_id F := by ext p : 1; exact (principalCechColumnFunctor r f p).map_id F
  map_comp i j := by ext p : 1; exact (principalCechColumnFunctor r f p).map_comp i j

/-- Regrouping subset coordinates identifies the two total functors naturally.
Source: Stacks, Tag 08D1, total signs, and finite filtration in Tag 08C2
(blueprint: lem-sc-principal-cech-bicomplex-comparison).

Proof: in degree n, evaluate the categorical product columns degreewise. Column p
is the product of sections on subsets S with card(S)=p+1, in vertical degree n-p.
Identify the diagonal coproduct with the finite product of these coordinates:
only p=0,...,r-1 can contribute. Map each subset coordinate to its column summand;
the inverse reads that coordinate from the summand. These maps are inverse since
products and coproducts of finite module families agree, and all other summands
are zero. The horizontal differential is the displayed alternating restriction
sum; the vertical term has sign (-1)^p. Substituting p=card(S)-1 and n-p=n+1-card(S)
gives exactly principalCechDifferentialValue. Use principalCechDifferential_exists
and its specification to obtain equality with principalCechDifferential, so the
degree identifications are chain isomorphisms to principalCechTotal. Compose with
principalCechObjIso. The componentwise map specification in
principalCechFunctor_exists proves naturality for every coefficient map.
For r=0 every coordinate type is empty and both complexes are zero; for r=1 only
the singleton column occurs. No restriction on the vertical degree is used. -/
theorem principalCechBicomplexComparison_exists :
    Nonempty (principalCechFunctor r f ≅ principalCechBicomplexFunctor r f ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  let B := principalCechBicomplexFunctor r f ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
      (principalCechBicomplex r f F).X p ≅
        (principalCechColumnFunctor r f p).obj F := Iso.refl _
  have he (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
      (principalCechBicomplex r f F).d p (p + 1) ≫ (e F (p + 1)).hom =
        (e F p).hom ≫ (principalCechHorizontal r f p).app F := by
    simp [e, principalCechBicomplex]
  have hi (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ) :
      IsIso (principalCechTotalRegroup r f F (principalCechBicomplex r f F) (e F) n) :=
    principalCechTotalRegroup_isIso r f F _ (e F) n
  let E (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
      B.obj F ≅ (principalCechFunctor r f).obj F :=
    HomologicalComplex.Hom.isoOfComponents
      (C₁ := (principalCechBicomplex r f F).total (ComplexShape.up ℤ))
      (C₂ := principalCechTotal r f F)
      (fun n ↦ asIso (principalCechTotalRegroup r f F
        (principalCechBicomplex r f F) (e F) n)) (by
          intro n m hnm
          obtain rfl : n + 1 = m := hnm
          simpa only [asIso_hom, principalCechTotal, CochainComplex.of_d] using
            principalCechTotalRegroup_comm r f F _ (e F) (he F) n) ≪≫
      (principalCechObjIso r f F).symm
  refine ⟨(NatIso.ofComponents E ?_).symm⟩
  intro F G g
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono ((principalCechObjIso r f G).hom.f n)).1
  have hn := principalCechTotalRegroup_naturality r f F G g
    (principalCechBicomplex r f F) (principalCechBicomplex r f G) (e F) (e G)
    ((principalCechBicomplexFunctor r f).map g)
    (by intro p; simp [e, principalCechBicomplexFunctor]) n
  simpa [E, B, Category.assoc] using hn.symm

end
end AlgebraicGeometry
