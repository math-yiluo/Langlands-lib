/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModels
import WeilConjectures.AlgebraicGeometry.AdicPerfectHomCochains
import all WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Ordinary quotient-model Hom and algebraic Hom cohomology

Source: Stacks Project, Tags 09C5, 09C6 and 0A8H.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectLocalComplex
  adicPerfectQuotientComplex adicPerfectQuotientStep

open CochainComplex CochainComplex.HomComplex in
private def scalarHomMap
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (Φ : C ⥤ D) [Φ.Additive] {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (a : (Φ.mapHomologicalComplex (.up ℤ)).obj K ≅ K')
    (b : (Φ.mapHomologicalComplex (.up ℤ)).obj L ≅ L') :
    HomComplex K L ⟶ HomComplex K' L' where
  f q := AddCommGrpCat.ofHom
    { toFun := fun z ↦ ((Cochain.ofHom a.inv).comp (z.map Φ) (zero_add q)).comp
        (Cochain.ofHom b.hom) (add_zero q)
      map_zero' := by simp
      map_add' := by intros; simp [Cochain.comp_add, Cochain.add_comp] }
  comm' q r _ := by
    ext z
    change δ q r (((Cochain.ofHom a.inv).comp (z.map Φ) (zero_add q)).comp
        (Cochain.ofHom b.hom) (add_zero q)) =
      ((Cochain.ofHom a.inv).comp ((δ q r z).map Φ) (zero_add r)).comp
        (Cochain.ofHom b.hom) (add_zero r)
    simp only [δ_comp_ofHom, δ_ofHom_comp, δ_map]

open CochainComplex CochainComplex.HomComplex in
private theorem scalarHomMap_ofHom
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (Φ : C ⥤ D) [Φ.Additive] {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (a : (Φ.mapHomologicalComplex (.up ℤ)).obj K ≅ K')
    (b : (Φ.mapHomologicalComplex (.up ℤ)).obj L ≅ L') (f : K ⟶ L) :
    (scalarHomMap Φ a b).f 0 (Cochain.ofHom f) =
      Cochain.ofHom (a.inv ≫ (Φ.mapHomologicalComplex (.up ℤ)).map f ≫ b.hom) := by
  change ((Cochain.ofHom a.inv).comp ((Cochain.ofHom f).map Φ) (zero_add 0)).comp
      (Cochain.ofHom b.hom) (add_zero 0) = _
  apply Cochain.ext
  intro p q hpq
  subst q
  simp

private def cocycleClass (S : ShortComplex AddCommGrpCat.{v})
    (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (S.abCyclesIso.inv ⟨x, hx⟩)

private theorem cocycleClass_map {S T : ShortComplex AddCommGrpCat.{v}}
    (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) (hy : T.g (φ.τ₂ x) = 0) :
    ShortComplex.homologyMap φ (cocycleClass S x hx) =
      cocycleClass T (φ.τ₂ x) hy := by
  have hc : ShortComplex.cyclesMap φ (S.abCyclesIso.inv ⟨x, hx⟩) =
      T.abCyclesIso.inv ⟨φ.τ₂ x, hy⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← AddCommGrpCat.comp_apply, ShortComplex.cyclesMap_i,
      AddCommGrpCat.comp_apply, ShortComplex.abCyclesIso_inv_apply_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
  unfold cocycleClass
  rw [← AddCommGrpCat.comp_apply, ShortComplex.homologyπ_naturality,
    AddCommGrpCat.comp_apply, hc]

private def homologyHomEquiv {C : Type*} [Category C] [Preadditive C]
    (K L : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃
        (CochainComplex.HomComplex K L).homology 0 :=
  (Iso.homCongr (Iso.refl _)
    ((HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app L).symm)).trans
    ((CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := K) (L := L) (n := 0)).toEquiv.symm.trans
        (CochainComplex.HomComplex.homologyAddEquiv K L 0).toEquiv.symm)

private theorem homologyHomEquiv_map {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homologyHomEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      (CochainComplex.HomComplex.leftHomologyData K L 0).homologyIso.inv
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom f)) := by
  let e₀ := CochainComplex.HomComplex.homologyAddEquiv K L 0
  let e₁ := CochainComplex.HomComplex.CohomologyClass.homAddEquiv
    (K := K) (L := L) (n := 0)
  change e₀.symm (e₁.symm _) = e₀.symm
    (CochainComplex.HomComplex.CohomologyClass.mk
      (CochainComplex.HomComplex.Cocycle.ofHom f))
  congr 1
  apply e₁.injective
  rw [AddEquiv.apply_symm_apply]
  simp only [e₁, CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
    Iso.homCongr_apply, Iso.refl_inv, Functor.mapIso_hom, Iso.symm_hom,
    Category.id_comp]
  rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cocycle.rightShift,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq]

open CochainComplex CochainComplex.HomComplex in
private theorem homologyHomEquiv_map_class {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homologyHomEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      cocycleClass ((HomComplex K L).sc 0) (Cochain.ofHom f)
        (by
          change δ 0 ((ComplexShape.up ℤ).next 0) (Cochain.ofHom f) = 0
          exact δ_ofHom f) := by
  rw [homologyHomEquiv_map]
  let h := leftHomologyData K L 0
  have hc : h.cyclesIso.inv (Cocycle.ofHom f) =
      ((HomComplex K L).sc 0).abCyclesIso.inv
        ⟨Cochain.ofHom f, by
          change δ 0 ((ComplexShape.up ℤ).next 0) (Cochain.ofHom f) = 0
          exact δ_ofHom f⟩ := by
    apply (AddCommGrpCat.mono_iff_injective ((HomComplex K L).sc 0).iCycles).mp
      inferInstance
    rw [← AddCommGrpCat.comp_apply, h.cyclesIso_inv_comp_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
    rfl
  change (h.π ≫ h.homologyIso.inv) (Cocycle.ofHom f) = _
  rw [h.π_comp_homologyIso_inv, AddCommGrpCat.comp_apply, hc]
  rfl

open CochainComplex CochainComplex.HomComplex in
private theorem homologyHomEquiv_scalar
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (Φ : C ⥤ D) [Φ.Additive] {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (a : (Φ.mapHomologicalComplex (.up ℤ)).obj K ≅ K')
    (b : (Φ.mapHomologicalComplex (.up ℤ)).obj L ≅ L') (f : K ⟶ L) :
    homologyHomEquiv K' L' ((HomotopyCategory.quotient D (.up ℤ)).map
        (a.inv ≫ (Φ.mapHomologicalComplex (.up ℤ)).map f ≫ b.hom)) =
      HomologicalComplex.homologyMap (scalarHomMap Φ a b) 0
        (homologyHomEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f)) := by
  rw [homologyHomEquiv_map_class, homologyHomEquiv_map_class]
  symm
  have h := cocycleClass_map
      ((HomologicalComplex.shortComplexFunctor _ _ 0).map (scalarHomMap Φ a b))
      (Cochain.ofHom f) (by
        change δ 0 ((ComplexShape.up ℤ).next 0) (Cochain.ofHom f) = 0
        exact δ_ofHom f)
      (by
        change δ 0 ((ComplexShape.up ℤ).next 0) ((scalarHomMap Φ a b).f 0 (Cochain.ofHom f)) = 0
        rw [scalarHomMap_ofHom]
        exact δ_ofHom _)
  dsimp only [HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor'] at h
  simpa only [HomologicalComplex.homology, HomologicalComplex.sc,
    HomologicalComplex.sc', HomologicalComplex.homologyMap,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
    scalarHomMap_ofHom] using h

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Homotopy-category Hom between the ordinary quotient complexes is sections of
algebraic quotient Hom cohomology. Naturality is stated on actual chain maps and
ordinary scalar balancing, without derived localization or derived Hom.

Source: Stacks Tag 09C6, the displayed formula for H_n; Tag 09C5, exact sections;
More on Algebra, Tag 0A8H, the signed Hom differential.
(auxiliary; not a blueprint node).

Proof: adicPerfectHomCochains isolates the chain-level evaluation of ordinary
quotient Hom: constant finite-free evaluation, finite-projective retracts, and the
finite product over the bounded source degrees. Its successor equation uses the
actual ordinary scalar-balancing isomorphisms. Construct the scalar-change map on
Hom cochains by applying the additive functor and conjugating by those balancing
maps; the signed differential identities prove that it is a chain map. Apply
homology to the resulting commuting square of complexes. Sections of constant
module sheaves preserve finite limits and finite colimits on any small site, so
the exact-functor homology comparison identifies the realized degree-zero homology
with constant sections of algebraic quotient cohomology. Mathlib identifies
cohomology classes with homotopy-category maps into a shift; remove the zero shift
using shiftFunctorZero. Its value on an actual chain map is that map's cocycle
class. Naturality of cycles inclusions and homology projections proves that this
class formula commutes with scalar change. Finally, naturality of the exact-functor
homology comparison gives the required successor identity. The weakly contractible
hypothesis and the bounds and projectivity of Q are preserved in the signature,
although this proof only needs the bounded finite-projective source. -/
theorem adicPerfectModelHomCohomology (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P Q : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b c d : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hc : Q.IsStrictlyGE c) (_hd : Q.IsStrictlyLE d)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i))
    (_hQ : ∀ i : ℤ, Module.Finite A (Q.X i) ∧ Module.Projective A (Q.X i)) :
    let F := AdicCohomology.tower J ((CochainComplex.moduleHomComplex P Q).sc 0) ⋙
      AdicCohomology.sections
        ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
      CategoryTheory.forget (ModuleCat A)
    let H := fun n : ℕ ↦ HomotopyCategory.quotient
      (Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)) (.up ℤ)
    ∃ e : ∀ n : ℕ,
        ((H n).obj (adicPerfectQuotientComplex.{u, v} X J U P n) ⟶
          (H n).obj (adicPerfectQuotientComplex.{u, v} X J U Q n)) ≃ F.obj (op n),
      ∀ (n : ℕ) (f : adicPerfectQuotientComplex.{u, v} X J U P (n + 1) ⟶
          adicPerfectQuotientComplex.{u, v} X J U Q (n + 1)),
        e n ((H n).map ((adicPerfectQuotientStep.{u, v} X J U P n).inv ≫
            ((change (adicPerfectQuotientScalarStep.{u, v} X J U n)).mapHomologicalComplex
              (.up ℤ)).map f ≫ (adicPerfectQuotientStep.{u, v} X J U Q n).hom)) =
          F.map (homOfLE (Nat.le_succ n)).op (e (n + 1) ((H (n + 1)).map f)) := by
  let T := (coefficientProEtaleModelTopology.{u, v} X).over U
  let V := Over.mk (𝟙 U)
  let S := (CochainComplex.moduleHomComplex P Q).sc 0
  let Γ := AdicCohomology.sections (R := A) T V
  have : PreservesFiniteLimits Γ := CategoryTheory.section_preservesFiniteLimits T A V
  have : PreservesFiniteColimits Γ := CategoryTheory.section_preservesFiniteColimits T A V
  have : Γ.PreservesHomology := inferInstance
  let G := Γ ⋙ forget₂ (ModuleCat A) AddCommGrpCat
  have : G.PreservesHomology := by dsimp [G]; infer_instance
  let C := fun n : ℕ ↦ CochainComplex.HomComplex
    (adicPerfectQuotientComplex.{u, v} X J U P n)
    (adicPerfectQuotientComplex.{u, v} X J U Q n)
  let D := fun n : ℕ ↦ (G.mapHomologicalComplex (.up ℤ)).obj
    (((AdicCohomology.quotient J (n + 1)).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.moduleHomComplex P Q))
  obtain ⟨e, he⟩ := adicPerfectHomCochains.{u, v} X J U P Q a b _ha _hb _hP
  let r : ∀ n : ℕ, (C n).homology 0 ≅
      G.obj (S.map (AdicCohomology.quotient J (n + 1))).homology := fun n ↦
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (e n) ≪≫
      (S.map (AdicCohomology.quotient J (n + 1))).mapHomologyIso G
  refine ⟨fun n ↦ (homologyHomEquiv _ _).trans
    (r n).addCommGroupIsoToAddEquiv.toEquiv, ?_⟩
  intro n f
  let Φ := change (adicPerfectQuotientScalarStep.{u, v} X J U n)
  let α := adicPerfectQuotientStep.{u, v} X J U P n
  let β := adicPerfectQuotientStep.{u, v} X J U Q n
  let γ := scalarHomMap Φ α β
  let τ := AdicCohomology.transition J (Nat.add_le_add_right (Nat.le_succ n) 1)
  let ψ : D (n + 1) ⟶ D n :=
    (G.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app
        (CochainComplex.moduleHomComplex P Q))
  have hsquare : γ ≫ (e n).hom = (e (n + 1)).hom ≫ ψ := by
    ext q z
    exact he n q z
  have hH := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hsquare
  simp only [HomologicalComplex.homologyMap_comp] at hH
  have hnat : HomologicalComplex.homologyMap γ 0 ≫ (r n).hom =
      (r (n + 1)).hom ≫ G.map (ShortComplex.homologyMap (S.mapNatTrans τ)) := by
    dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor]
    rw [← Category.assoc, hH, Category.assoc]
    exact congrArg (fun k ↦ HomologicalComplex.homologyMap (e (n + 1)).hom 0 ≫ k)
      (ShortComplex.mapHomologyIso_hom_naturality (S.mapNatTrans τ) G)
  have hh := homologyHomEquiv_scalar Φ α β f
  change (r n).hom (homologyHomEquiv _ _
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (α.inv ≫ (Φ.mapHomologicalComplex (.up ℤ)).map f ≫ β.hom))) = _
  rw [hh, ← AddCommGrpCat.comp_apply, hnat, AddCommGrpCat.comp_apply]
  rfl

end AlgebraicGeometry.Scheme
