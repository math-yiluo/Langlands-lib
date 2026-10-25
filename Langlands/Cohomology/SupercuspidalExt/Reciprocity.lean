import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Cohomology.DerivedComparison
import Langlands.Cohomology.SmoothExt

/-!
# Ext reciprocity for compact induction from an open subgroup

For an open subgroup `H` of a topological group `G` and a smooth representation
`V` of `H`, Frobenius reciprocity `Hom_G(c-Ind_H^G V, -) ≅ Hom_H(V, -) ∘ restriction`
induces isomorphisms `Ext^n_G(c-Ind_H^G V, -) ≅ Ext^n_H(V, -) ∘ restriction` for
every `n` (`extCompactInductionIso`). Restriction is exact and preserves injective
objects, so the general comparison `DerivedComparison.rightDerivedCompIso` applies.
In degree zero the isomorphism is Frobenius reciprocity itself
(`extCompactInductionIso_hom_app_zero`), by the general compatibility
`DerivedComparison.toRightDerivedZero_comp_rightDerivedCompIso` proved first.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.DerivedComparison

universe vC uC vD uD vE uE vF uF

section DegreeZero

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable {E' : Type uF} [Category.{vF} E'] [Abelian E']

set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving the left homology of a short complex commutes with the
projections from cycles to homology. -/
@[reassoc]
theorem map_homologyπ_comp_mapHomologyIso_inv (S : ShortComplex E) [S.HasHomology]
    (F : E ⥤ E') [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [(S.map F).HasHomology] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F, S.leftHomologyData.mapCyclesIso_eq F]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  rw [← F.map_comp_assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    F.map_comp, Category.assoc, ← ShortComplex.LeftHomologyData.map_π,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

/-- A functor preserving the left homology of a short complex commutes with the
inclusions of cycles. -/
@[reassoc]
theorem mapCyclesIso_inv_iCycles (S : ShortComplex E) [S.HasLeftHomology]
    (F : E ⥤ E') [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, ShortComplex.mapCyclesIso_hom_iCycles]

variable (Φ : C ⥤ E) [Φ.Additive] (P : E ⥤ E') [P.Additive]
variable (T : C ⥤ D) [T.Additive] (Ψ : D ⥤ E') [Ψ.Additive] (e : Φ ⋙ P ≅ T ⋙ Ψ)
variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
variable [P.PreservesHomology] [T.PreservesHomology] [T.PreservesInjectiveObjects]

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero the comparison isomorphism is compatible with `e` through the
canonical maps `Φ ⟶ Φ.rightDerived 0` and `Ψ ⟶ Ψ.rightDerived 0`. -/
theorem toRightDerivedZero_comp_rightDerivedCompIso (X : C) :
    P.map (Φ.toRightDerivedZero.app X) ≫ (rightDerivedCompIso Φ P T Ψ e 0).hom.app X =
      e.hom.app X ≫ Ψ.toRightDerivedZero.app (T.obj X) := by
  set I := injectiveResolution X
  set J := mapInjectiveResolution T I
  set K := (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hcycles : P.map (I.toRightDerivedZero' Φ) ≫ ((K.sc 0).mapCyclesIso P).inv ≫
      HomologicalComplex.cyclesMap (complexIso Φ P T Ψ e I.cocomplex).hom 0 =
        e.hom.app X ≫ J.toRightDerivedZero' Ψ := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc, Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [mapCyclesIso_inv_iCycles_assoc (K.sc 0) P]
    rw [← P.map_comp_assoc]
    erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rw [mapInjectiveResolution_ι_f_zero]
    exact e.hom.naturality (I.ι.f 0)
  have hhomology : P.map (I.toRightDerivedZero' Φ) ≫ P.map (K.homologyπ 0) ≫
      (mapHomologyIso P K 0).inv ≫
        (HomologicalComplex.homologyFunctor E' _ 0).map (complexIso Φ P T Ψ e I.cocomplex).hom =
        e.hom.app X ≫ J.toRightDerivedZero' Ψ ≫ HomologicalComplex.homologyπ _ 0 := by
    erw [map_homologyπ_comp_mapHomologyIso_inv_assoc (K.sc 0) P]
    have hcycles' := reassoc_of% hcycles
    exact (congrArg (fun x => P.map (I.toRightDerivedZero' Φ) ≫
      ((K.sc 0).mapCyclesIso P).inv ≫ x) (HomologicalComplex.homologyπ_naturality
        (complexIso Φ P T Ψ e I.cocomplex).hom 0)).trans (hcycles' _)
  rw [I.toRightDerivedZero_eq Φ, J.toRightDerivedZero_eq Ψ]
  change _ ≫ (compIsoOfResolution Φ P T Ψ e I 0).hom = _
  simp only [compIsoOfResolution, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, CochainComplex.isoHomologyπ₀,
    HomologicalComplex.isoHomologyπ_hom]
  rw [← P.map_comp_assoc (I.isoRightDerivedObj Φ 0).inv, Iso.inv_hom_id, P.map_id,
    Category.id_comp, reassoc_of% hhomology]

end DegreeZero

end Langlands.Cohomology.DerivedComparison

namespace Langlands.Cohomology.SupercuspidalExt

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

section Restriction

variable (H : Subgroup G)

/-- Restriction is additive: it does not change the underlying linear maps. -/
instance restriction_additive : (restriction R G H).Additive where
  map_add := rfl

/-- Restriction is `R`-linear. -/
instance restriction_linear : (restriction R G H).Linear R where
  map_smul _ _ := rfl

/-- Restriction preserves epimorphisms, which are the surjective intertwiners. -/
instance restriction_preservesEpimorphisms : (restriction R G H).PreservesEpimorphisms :=
  Induction.smoothRestriction_preservesEpimorphisms.{u, u, u} R H

variable {H} (hH : IsOpen (H : Set G))

include hH in
/-- Restriction to an open subgroup is exact. -/
theorem restriction_preservesHomology : (restriction R G H).PreservesHomology := by
  have := (compactInductionAdjunction R G H hH).rightAdjoint_preservesLimits
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

include hH in
/-- Restriction to an open subgroup preserves injective objects. -/
theorem restriction_preservesInjectiveObjects :
    (restriction R G H).PreservesInjectiveObjects := by
  have : (compactInduction R G H).PreservesMonomorphisms :=
    Induction.smoothCompactInduction_preservesMonomorphisms.{u, u, u} R H
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (compactInductionAdjunction R G H hH)

end Restriction

section Reciprocity

variable {G} {H : Subgroup G} (hH : IsOpen (H : Set G))

/-- Frobenius reciprocity as an `R`-linear equivalence of Hom modules. -/
def homLinearEquiv (V : SmoothRep.{u, u, u} R H) (W : SmoothRep.{u, u, u} R G) :
    ((compactInduction R G H).obj V ⟶ W) ≃ₗ[R] (V ⟶ (restriction R G H).obj W) where
  __ := (compactInductionAdjunction R G H hH).homEquiv V W
  map_add' f g := by
    change (compactInductionAdjunction R G H hH).homEquiv V W (f + g) =
      (compactInductionAdjunction R G H hH).homEquiv V W f +
        (compactInductionAdjunction R G H hH).homEquiv V W g
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_add, Preadditive.comp_add]
  map_smul' r f := by
    change (compactInductionAdjunction R G H hH).homEquiv V W (r • f) =
      r • (compactInductionAdjunction R G H hH).homEquiv V W f
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

/-- The equivalence is the hom-equivalence of the adjunction `c-Ind ⊣ restriction`. -/
theorem homLinearEquiv_apply (V : SmoothRep.{u, u, u} R H) (W : SmoothRep.{u, u, u} R G)
    (f : (compactInduction R G H).obj V ⟶ W) :
    homLinearEquiv R hH V W f = (compactInductionAdjunction R G H hH).homEquiv V W f :=
  rfl

/-- Frobenius reciprocity as a natural isomorphism of Hom functors into `R`-modules. -/
def homFunctorIso (V : SmoothRep.{u, u, u} R H) :
    SmoothHomComplex.homFunctor R G ((compactInduction R G H).obj V) ⋙ 𝟭 (ModuleCat.{u} R) ≅
      restriction R G H ⋙ SmoothHomComplex.homFunctor R H V :=
  NatIso.ofComponents (fun W => (homLinearEquiv R hH V W).toModuleIso) fun {W W'} f => by
    ext g
    exact (compactInductionAdjunction R G H hH).homEquiv_naturality_right g f

/-- Ext reciprocity: for an open subgroup `H` and a smooth representation `V` of `H`,
`Ext^n_G(c-Ind_H^G V, -) ≅ Ext^n_H(V, -) ∘ restriction`. -/
def extCompactInductionIso (V : SmoothRep.{u, u, u} R H) (n : ℕ) :
    SmoothExt.ext R G ((compactInduction R G H).obj V) n ≅
      restriction R G H ⋙ SmoothExt.ext R H V n := by
  have := restriction_preservesHomology R G hH
  have := restriction_preservesInjectiveObjects R G hH
  exact (Functor.rightUnitor _).symm ≪≫
    DerivedComparison.rightDerivedCompIso _ (𝟭 (ModuleCat.{u} R)) (restriction R G H) _
      (homFunctorIso R hH V) n

/-- In degree zero, Ext reciprocity is Frobenius reciprocity on Hom modules, under the
identifications `Ext^0 ≅ Hom` on both sides. -/
theorem extCompactInductionIso_hom_app_zero (V : SmoothRep.{u, u, u} R H)
    (W : SmoothRep.{u, u, u} R G) :
    (extCompactInductionIso R hH V 0).hom.app W =
      (SmoothExt.extZeroIso R G ((compactInduction R G H).obj V)).hom.app W ≫
        (homLinearEquiv R hH V W).toModuleIso.hom ≫
          (SmoothExt.extZeroIso R H V).inv.app ((restriction R G H).obj W) := by
  have := restriction_preservesHomology R G hH
  have := restriction_preservesInjectiveObjects R G hH
  rw [← cancel_epi ((SmoothExt.extZeroIso R G ((compactInduction R G H).obj V)).inv.app W),
    Iso.inv_hom_id_app_assoc]
  have e1 : (extCompactInductionIso R hH V 0).hom.app W =
      (DerivedComparison.rightDerivedCompIso _ (𝟭 (ModuleCat.{u} R)) (restriction R G H) _
        (homFunctorIso R hH V) 0).hom.app W :=
    Category.id_comp _
  rw [e1]
  exact DerivedComparison.toRightDerivedZero_comp_rightDerivedCompIso _
    (𝟭 (ModuleCat.{u} R)) (restriction R G H) _ (homFunctorIso R hH V) W

end Reciprocity

end Langlands.Cohomology.SupercuspidalExt
