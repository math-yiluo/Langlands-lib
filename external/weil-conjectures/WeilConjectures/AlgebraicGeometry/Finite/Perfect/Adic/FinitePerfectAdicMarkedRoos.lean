/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientDiagram
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCanonicalComparison
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLowerStarDerivedLimit

/-! # The Roos calculation for algebraically marked finite-projective quotients

Source: Stacks Project, Tag 09C6, the displayed finite-projective inverse-limit calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- An isomorphism of cone points transports a Roos triangle.
Source: Stacks Tag 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-roos).
Proof: conjugate the first and last arrows by the point isomorphism and its shift. -/
theorem finitePerfectAdicRoos_changeObject
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {K : ℕ → D} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {L L' : D} (e : L ≅ L') (h : IsDerivedLimit f L) : IsDerivedLimit f L' := by
  obtain ⟨p, δ, h⟩ := h
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom, ?_⟩
  apply (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk p _ δ)
      (Pretriangulated.Triangle.mk (e.inv ≫ p) _
        (δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom))
      e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))).mp h

/-- An isomorphism of entire inverse diagrams transports a Roos triangle.
Source: Stacks Tag 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-roos).
Proof: the product of the component isomorphisms conjugates one minus shift;
transport the distinguished triangle through that product isomorphism. -/
theorem finitePerfectAdicRoos_changeDiagram
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasCountableProducts D] (F G : ℕᵒᵖ ⥤ D) (e : F ≅ G) (L : D)
    (h : IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) L) :
    IsDerivedLimit (K := fun n : ℕ ↦ G.obj (op n))
      (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) L := by
  obtain ⟨p, δ, h⟩ := h
  let E := Pi.mapIso (fun n : ℕ ↦ e.app (op n))
  have hE : E.hom ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) =
      towerTransitionEndomorphism
        (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) ≫ E.hom :=
    towerTransitionEndomorphism_natural_backward _ _
      (fun n ↦ (e.app (op n)).hom)
      (fun n ↦ (e.hom.naturality (homOfLE (Nat.le_succ n)).op).symm)
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk p _ δ)
      (Pretriangulated.Triangle.mk (p ≫ E.hom) _ (E.inv ≫ δ))
      (Iso.refl _) E E (by simp) hE.symm (by simp))).mp h

/-- Exact slice restriction is a right adjoint also on unbounded derived categories.
Source: Stacks Tag 03DA and Derived Categories, derived adjunction.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-roos).
Proof: localize the exact extension/restriction adjunction on complexes. -/
theorem finitePerfectAdicRestriction_rightAdjoint
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (U : X.ProEt) :
    (ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
      (completedAdicRing X d) U).IsRightAdjoint := by
  let E := SheafOfModules.localizedSystemExtension.{t + 1, t, 0}
    (completedAdicCommRing X d) U
  let R := SheafOfModules.localizedSystemRestriction.{t + 1, t, 0}
    (completedAdicCommRing X d) U
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := inferInstance
  have : PreservesFiniteColimits E := inferInstance
  have : R.Additive := inferInstance
  have : PreservesFiniteLimits R := inferInstance
  have : PreservesFiniteColimits R := inferInstance
  let adj := SheafOfModules.localizedSystemAdjunction.{t + 1, t, 0}
    (completedAdicCommRing X d) U
  let : CatCommSq (E.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q E.mapDerivedCategory :=
    ⟨E.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  exact ((adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    E.mapDerivedCategory R.mapDerivedCategory).isRightAdjoint

/-- Exact derived slice restriction preserves Roos limit triangles.
Source: Stacks Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-roos). -/
theorem finitePerfectAdicRestriction_roos
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (U : X.ProEt)
    [HasCountableProducts (DerivedCategory (CompletedAdicModules X d))]
    [HasCountableProducts
      (DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (CompletedAdicModules X d))
    (C : DerivedCategory (CompletedAdicModules X d))
    (h : IsDerivedLimit (K := fun n : ℕ ↦ K.obj (op n))
      (fun n : ℕ ↦ K.map (homOfLE n.le_succ).op) C) :
    let R := ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
      (completedAdicRing X d) U
    IsDerivedLimit (K := fun n : ℕ ↦ R.obj (K.obj (op n)))
      (fun n : ℕ ↦ R.map (K.map (homOfLE n.le_succ).op)) (R.obj C) := by
  let R := ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
    (completedAdicRing X d) U
  have : R.IsRightAdjoint := finitePerfectAdicRestriction_rightAdjoint X d U
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1}
    (completedAdicRing X d) U).1
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1}
    (completedAdicRing X d) U).2.1
  have := (ringedOverFunctor_exactGeneral.{t + 1, t, t + 1, t + 1}
    (completedAdicRing X d) U).2.2
  let : R.CommShift ℤ := by
    dsimp only [R, ringedDerivedRestrictionGeneral]
    infer_instance
  have : R.IsTriangulated := by
    dsimp only [R, ringedDerivedRestrictionGeneral]
    infer_instance
  obtain ⟨p, δ, h⟩ := h
  obtain ⟨e, _, h⟩ := R.isDerivedLimitTriangle_map _ _ p δ h
  exact ⟨_, _, h⟩

/-- The canonical algebraic quotient diagram of a bounded finite-projective complex
has its completed constant realization as its Roos limit.

Source: Stacks Project, Tag 09C6, the displayed finite-projective inverse-limit calculation;
Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-roos).

Proof: uniqueness of left adjoints identifies L_n with derived tensor by A/I^(n+1),
preserving its unit. The canonical transitions are transposes of these same units,
so the resulting diagram is the actual quotient diagram of P. A finite-projective
term is an idempotent summand of a finite free module. Its quotient constant sheaves
have sectionwise surjective transitions, and their limit is the same idempotent
summand of the completed coefficient sheaf. These identifications are natural for
linear maps, hence commute with the differentials of P. Thus their ordinary limit
complex is ordinary completed constant realization of P. Apply the termwise
epimorphic-complex Roos theorem. Flatness and bounded projectivity identify ordinary
realization with completed derived scalar extension. Exact slice restriction is a
right adjoint and preserves the Roos triangle. Zero terms and empty slices give zero
triangles. No geometric trivialization, arbitrary algebraic tower or compatible
marking is supplied to this statement, and completeness of A is not required. -/
theorem finitePerfectAdicMarked_roos
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (U : X.ProEt)
    [HasCountableProducts
      (DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)))]
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction d.ideal n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) :
    let F := finitePerfectAdicQuotientDiagram d.ideal L adj (DerivedCategory.Q.obj P) ⋙
      finitePerfectAdicLocalRealization X d U
    IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
      (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op)
      ((finitePerfectAdicLocalRealization X d U).obj (DerivedCategory.Q.obj P)) := by
  classical
  have := finitePerfectAdicModules_exactProducts X d
  obtain ⟨hprod, _, _⟩ := derivedCategory_countableProducts_core.{0}
    (CompletedAdicModules X d)
  let := hprod
  obtain ⟨T, c, hret, ⟨e⟩, ⟨j⟩⟩ :=
    finitePerfectAdicCanonical_comparison X d L adj P a b ha hb hP
  have ht := finitePerfectAdicProjectiveComplex_roos X d T c hret
  have hg := finitePerfectAdicRoos_changeObject _ j
    (finitePerfectAdicRoos_changeDiagram _ _ e _ ht.2)
  have hl := finitePerfectAdicRestriction_roos X d U _ _ hg
  simpa only [finitePerfectAdicLocalRealization, Functor.comp_obj, Functor.comp_map] using hl

end AlgebraicGeometry.Scheme
