/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.AdicResidueCoefficientSequence
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.HomologySequence

/-! # Successive quotient vanishing

Source: Stacks Project, More on Algebra, Tag 0G1T, derived vanishing modulo an ideal;
proetale.tex, Tag 09C6, finite reduction argument.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion CategoryTheory.MonoidalCategory

namespace AdicResidueSuccessorProof

universe w
variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
  {R S : Sheaf T CommRingCat.{w}}

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
  SheafOfModules.cochainModulesPreadditive

private def tensorComplex (P : Cx R) : Mod R ⥤ Cx R where
  obj N := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor _).map f) (.up ℤ)).app P
  map_id N := by ext i; simp
  map_comp f g := by ext i; simp

private theorem tensorComplex_additive (P : Cx R) : (tensorComplex P).Additive := by
  constructor
  intro M N f g
  ext i : 1
  change (f + g) ▷ P.X i = f ▷ P.X i + g ▷ P.X i
  exact MonoidalPreadditive.add_whiskerRight _ _

attribute [local instance] tensorComplex_additive

private def tensorRestrictionIso (φ : R ⟶ S) (P : Cx R) (N : Mod S) :
    ((res φ).mapHomologicalComplex (.up ℤ)).obj
        ((tensorComplex (((change φ).mapHomologicalComplex (.up ℤ)).obj P)).obj N) ≅
      (tensorComplex P).obj ((res φ).obj N) := by
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients
    φ).choose
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ e N (P.X i)) ?_
  intro i j hij
  have he := (SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients
    φ).choose_spec (𝟙 N) (P.d i j)
  change (e N (P.X i)).hom ≫ ((res φ).obj N ◁ P.d i j) =
    (res φ).map (N ◁ SheafOfModules.changeOfRingsHom φ (P.X i) (P.d i j)) ≫
      (e N (P.X j)).hom
  have hid : (res φ).map (𝟙 N) = 𝟙 ((res φ).obj N) := (res φ).map_id N
  rw [hid] at he
  simpa only [id_tensorHom] using he.symm

private theorem restriction_acyclic (φ : R ⟶ S) (P : Cx S) :
    (((res φ).mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic := by
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  constructor
  · intro h i
    apply ((P.sc i).exact_map_iff_of_faithful (SheafOfModules.toSheaf _)).mp
    exact (h i).map (SheafOfModules.toSheaf _)
  · intro h i
    exact (h i).map (res φ)

private def tensorUnitIso (P : Cx S) :
    (tensorComplex P).obj (SheafOfModules.unit _) ≅ P :=
  (NatIso.mapHomologicalComplex (leftUnitorNatIso (Mod S)) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P

private theorem tensor_unit_acyclic_iff (φ : R ⟶ S) (P : Cx R) :
    ((tensorComplex P).obj ((res φ).obj (SheafOfModules.unit _))).Acyclic ↔
      (((change φ).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  let E := ((change φ).mapHomologicalComplex (.up ℤ)).obj P
  let e := tensorRestrictionIso φ P (SheafOfModules.unit _)
  constructor
  · intro h
    exact ((restriction_acyclic φ _).1 (h.of_iso e.symm)).of_iso (tensorUnitIso E)
  · intro h
    exact ((restriction_acyclic φ _).2 (h.of_iso (tensorUnitIso E).symm)).of_iso e

private theorem tensor_restricted_acyclic (φ : R ⟶ S) (P : Cx R)
    (hP : P.IsKFlatIndependentCoefficients)
    (hE : (((change φ).mapHomologicalComplex (.up ℤ)).obj P).Acyclic) (N : Mod S) :
    ((tensorComplex P).obj ((res φ).obj N)).Acyclic := by
  let E := ((change φ).mapHomologicalComplex (.up ℤ)).obj P
  have hk : CochainComplex.IsKFlatIndependentCoefficients E :=
    SheafOfModules.changeOfRings_isKFlat_independentCoefficients φ P
      (change φ) (fun _ ↦ rfl) (by intros; simp only [eqToHom_refl,
        Category.id_comp, Category.comp_id]; rfl) hP
  have ht := SheafOfModules.tensor_acyclic_of_isKFlat E hk hE
    ((HomologicalComplex.single (Mod S) (.up ℤ) 0).obj N)
  have ht' : ((tensorComplex E).obj N).Acyclic := ht.of_iso
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) N E)
  exact ((restriction_acyclic φ _).2 ht').of_iso (tensorRestrictionIso φ P N)

private theorem extend_isZero_iff (φ : R ⟶ S) (P : Cx R)
    (hP : P.IsKFlatIndependentCoefficients) :
    IsZero ((extend φ).obj ((Q R).obj P)) ↔
      (((change φ).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  let := HasDerivedCategory.standard (Mod S)
  have : IsIso ((extendComparison φ).app P) := (derivedExtension φ).computation P hP
  exact (asIso ((extendComparison φ).app P)).isZero_iff.trans
    (@DerivedCategory.isZero_Q_obj_iff (Mod S) _ _
      (HasDerivedCategory.standard _) (((change φ).mapHomologicalComplex (.up ℤ)).obj P))

end AdicResidueSuccessorProof

namespace AlgebraicGeometry.Scheme

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Vanishing of the residue and one finite reduction implies vanishing of the next.
No completeness or boundedness is required.

Source: Stacks Project, more-algebra.tex, Tag 0G1T, lemma-derived-vanishing-mod-I;
proetale.tex, Tag 09C6, finite reduction argument.
(auxiliary; not a blueprint node).

Proof: take a termwise-flat K-flat representative P of Q over the completed
coefficient sheaf on the slice. Its ordinary residue and nth scalar extensions
are acyclic by the specified K-flat computation comparisons. The consecutive
coefficient short exact sequence has a residue-module kernel and the regular
successor and nth quotient modules as its middle and last terms. Tensor it
termwise with P; flatness preserves short exactness. Balanced tensor cancellation
identifies the left complex with the restriction of the tensor of the residue
extension of P and the kernel module. That extension is acyclic and remains
K-flat, so this tensor is acyclic. Cancellation with the regular quotient unit
makes the right complex acyclic as well. Exact homology makes the middle complex
acyclic. Cancellation and the K-flat computation comparison identify this with
vanishing of the specified successor reduction. Exact faithful restriction
reflects acyclicity throughout. For J=0 the reductions are identical; for J=top
the quotient categories are zero. No quotient-perfectness hypothesis is used. -/
theorem adicResidue_vanishing_successor
    (X : AlgebraicGeometry.Scheme.{u}) {A : Type (max v (u + 1))}
    [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (Q : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
    (h₀ : IsZero ((adicResidueLocalReduction.{u, v} X J U 0).obj Q))
    (hn : IsZero ((adicResidueLocalReduction.{u, v} X J U n).obj Q)) :
    IsZero ((adicResidueLocalReduction.{u, v} X J U (n + 1)).obj Q) := by
  let B := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  let p := adicResidueLocalProjection.{u, v} X J U
  let := HasDerivedCategory.standard (Mod B)
  let G := (CategoryTheory.ConstantCompletion.Q B).objPreimage Q
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have : QuasiIso f := hf
  let e : (CategoryTheory.ConstantCompletion.Q B).obj P ≅ Q :=
    asIso ((CategoryTheory.ConstantCompletion.Q B).map f) ≪≫
      (CategoryTheory.ConstantCompletion.Q B).objObjPreimageIso Q
  have h₀' : (((change (p 0)).mapHomologicalComplex (.up ℤ)).obj P).Acyclic :=
    (AdicResidueSuccessorProof.extend_isZero_iff (p 0) P hP).1
      (h₀.of_iso ((extend (p 0)).mapIso e))
  have hn' : (((change (p n)).mapHomologicalComplex (.up ℤ)).obj P).Acyclic :=
    (AdicResidueSuccessorProof.extend_isZero_iff (p n) P hP).1
      (hn.of_iso ((extend (p n)).mapIso e))
  obtain ⟨N, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := adicResidue_coefficient_sequence X J U n
  let F := AdicResidueSuccessorProof.tensorComplex P
  have : F.Additive := AdicResidueSuccessorProof.tensorComplex_additive P
  have h₁ : (F.obj S.X₁).Acyclic :=
    (AdicResidueSuccessorProof.tensor_restricted_acyclic (p 0) P hP h₀' N).of_iso
      (F.mapIso e₁).symm
  have h₃ : (F.obj S.X₃).Acyclic :=
    ((AdicResidueSuccessorProof.tensor_unit_acyclic_iff (p n) P).2 hn').of_iso
      (F.mapIso e₃).symm
  have hseq : (S.map F).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    have := (exactFunctor_iff _).1 (hflat i) |>.1
    have := (exactFunctor_iff _).1 (hflat i) |>.2
    change (S.map (tensorRight (P.X i))).ShortExact
    exact hS.map_of_exact (tensorRight (P.X i))
  have h₂ : (F.obj S.X₂).Acyclic := by
    intro i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact (hseq.homology_exact₂ i).isZero_X₂
      ((h₁ i).isZero_homology.eq_of_src _ _) ((h₃ i).isZero_homology.eq_of_tgt _ _)
  have hnext := (AdicResidueSuccessorProof.tensor_unit_acyclic_iff (p (n + 1)) P).1
    (h₂.of_iso (F.mapIso e₂))
  exact ((AdicResidueSuccessorProof.extend_isZero_iff (p (n + 1)) P hP).2 hnext).of_iso
    ((extend (p (n + 1))).mapIso e).symm

end AlgebraicGeometry.Scheme
