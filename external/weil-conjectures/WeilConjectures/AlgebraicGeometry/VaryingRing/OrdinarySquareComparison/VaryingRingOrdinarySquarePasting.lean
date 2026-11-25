/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons

/-! Pasting of two ordinary realization comparison equations.
Source: Zheng, Construction 4.1; functoriality and associativity.
(blueprint: lem-sp-varying-ring-ordinary-square-pasting). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.VaryingRing

/-- Comparison equations for consecutive natural transformations compose.
Source: functoriality and associativity in Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-ordinary-square-pasting).
Proof: apply map_comp to their composite. Substitute the second comparison
at its component, then the first comparison with the remaining factor on the
right. Associativity identifies the result with the required equation. -/
theorem OrdinarySquareComparison.trans
    {A B C D M A' B' C' D' M' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category M] [Category M']
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {R₀ : C ⥤ A} {P₀ : D ⥤ B} {K : A ⥤ B} {I : C ⥤ D}
    {r : C' ⥤ A'} {p : D' ⥤ B'} {k : A' ⥤ B'} {i : C' ⥤ D'}
    (eR : R₀ ⋙ EA ≅ EC ⋙ r) (eP : P₀ ⋙ EB ≅ ED ⋙ p)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eI : I ⋙ ED ≅ EC ⋙ i)
    {EM : M ⥤ M'} {A₀ : C ⥤ M} {B₀ : M ⥤ B}
    {a₀ : C' ⥤ M'} {b₀ : M' ⥤ B'}
    (eA : A₀ ⋙ EM ≅ EC ⋙ a₀) (eB : B₀ ⋙ EB ≅ EM ⋙ b₀)
    (β : I ⋙ P₀ ⟶ A₀ ⋙ B₀) (β' : i ⋙ p ⟶ a₀ ⋙ b₀)
    (θ : A₀ ⋙ B₀ ⟶ R₀ ⋙ K) (θ' : a₀ ⋙ b₀ ⟶ r ⋙ k)
    (hb : OrdinarySquareComparison eA eP eB eI β β')
    (hs : OrdinarySquareComparison eR eB eK eA θ θ') :
    OrdinarySquareComparison eR eP eK eI (β ≫ θ) (β' ≫ θ') := by
  constructor
  intro N
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [hs.equation N, reassoc_of% (hb.equation N)]

end AlgebraicGeometry.ProEtale.VaryingRing
