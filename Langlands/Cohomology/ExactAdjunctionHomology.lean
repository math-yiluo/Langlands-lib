import Langlands.Cohomology.AdditiveAdjunction
import Langlands.Cohomology.DerivedExactComposition

/-! # Exact additive adjunctions and cohomology -/

noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology

namespace ExactAdjunction

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  (adj : F ⊣ G)

/-- The adjunct on cohomology of a cochain map into an exact right adjoint. -/
def homologyAdjunct [G.PreservesHomology]
    {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (t : K ⟶ (G.mapHomologicalComplex _).obj L) (n : ℕ) :
    F.obj ((homologyFunctor C _ n).obj K) ⟶ (homologyFunctor D _ n).obj L :=
  (adj.homEquiv _ _).symm
    ((homologyFunctor C _ n).map t ≫ (DerivedComparison.mapHomologyIso G L n).hom)

section Exact

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity functor has the identity homology comparison. -/
lemma mapHomologyIso_id_hom (S : ShortComplex C) :
    (S.mapHomologyIso (𝟭 C)).hom = 𝟙 S.homology := by
  have hc : (S.mapCyclesIso (𝟭 C)).hom = 𝟙 S.cycles := by
    apply (cancel_mono S.iCycles).1
    have h := ShortComplex.mapCyclesIso_hom_iCycles S (𝟭 C)
    change (S.mapCyclesIso (𝟭 C)).hom ≫ S.iCycles = S.iCycles at h
    erw [Category.id_comp]
    exact h
  apply (cancel_epi S.homologyπ).1
  have h := DerivedPlus.homologyπ_mapHomologyIso_hom (𝟭 C) S
  change S.homologyπ ≫ (S.mapHomologyIso (𝟭 C)).hom =
    (S.mapCyclesIso (𝟭 C)).hom ≫ S.homologyπ at h
  erw [hc, Category.id_comp] at h
  simpa only [Category.comp_id] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cochain unit induces the unit on cohomology through the two exact
homology comparisons. -/
lemma unit_homology (K : CochainComplex C ℕ) (n : ℕ) :
    (homologyFunctor C _ n).map ((complexAdjunction adj _).unit.app K) ≫
        (DerivedComparison.mapHomologyIso G ((F.mapHomologicalComplex _).obj K) n).hom ≫
        G.map (DerivedComparison.mapHomologyIso F K n).hom =
      adj.unit.app ((homologyFunctor C _ n).obj K) := by
  have h := NatTrans.app_homology adj.unit (K.sc n)
  have hc := DerivedPlus.mapHomologyIso_comp_hom F G (K.sc n)
  have hi := mapHomologyIso_id_hom (K.sc n)
  have hii : ((K.sc n).mapHomologyIso (𝟭 C)).inv = 𝟙 (K.sc n).homology := by
    have h := ((K.sc n).mapHomologyIso (𝟭 C)).inv_hom_id
    rw [hi] at h
    erw [Category.comp_id] at h
    exact h
  erw [hii, Category.id_comp] at h
  rw [hc] at h
  have hu :
      (shortComplexFunctor C (ComplexShape.up ℕ) n).map
          ((complexAdjunction adj _).unit.app K) =
        (K.sc n).mapNatTrans adj.unit := by
    ext <;> rfl
  rw [homologyFunctor_map, HomologicalComplex.homologyMap, hu]
  change ShortComplex.homologyMap ((K.sc n).mapNatTrans adj.unit) ≫
      (((K.sc n).map F).mapHomologyIso G).hom ≫
      G.map ((K.sc n).mapHomologyIso F).hom = adj.unit.app (K.sc n).homology
  simpa only [Category.id_comp, Category.assoc] using h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking cohomology commutes with passing to the adjunct, through the
canonical homology comparison for the exact left adjoint. -/
lemma homologyAdjunct_eq
    {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (t : K ⟶ (G.mapHomologicalComplex _).obj L) (n : ℕ) :
    homologyAdjunct adj t n =
      (DerivedComparison.mapHomologyIso F K n).inv ≫
        (homologyFunctor D _ n).map
          ((complexAdjunction adj _).homEquiv K L |>.symm t) := by
  let s := ((complexAdjunction adj _).homEquiv K L).symm t
  have hs : (complexAdjunction adj _).unit.app K ≫
      (G.mapHomologicalComplex _).map s = t :=
    ((complexAdjunction adj _).homEquiv K L).apply_symm_apply t
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor D (ComplexShape.up ℕ) n).map s) G
  change
    (homologyFunctor C _ n).map ((G.mapHomologicalComplex _).map s) ≫
        (DerivedComparison.mapHomologyIso G L n).hom =
      (DerivedComparison.mapHomologyIso G ((F.mapHomologicalComplex _).obj K) n).hom ≫
        G.map ((homologyFunctor D _ n).map s) at hn
  apply (adj.homEquiv _ _).injective
  rw [homologyAdjunct, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change (homologyFunctor C _ n).map t ≫
      (DerivedComparison.mapHomologyIso G L n).hom =
    adj.unit.app ((homologyFunctor C _ n).obj K) ≫
      G.map ((DerivedComparison.mapHomologyIso F K n).inv ≫
        (homologyFunctor D _ n).map s)
  rw [← hs, Functor.map_comp, Category.assoc, hn, ← unit_homology adj K n,
    Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Exact

end ExactAdjunction

end Langlands.Cohomology
