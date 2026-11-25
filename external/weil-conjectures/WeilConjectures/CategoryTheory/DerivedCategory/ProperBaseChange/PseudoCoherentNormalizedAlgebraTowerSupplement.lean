/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstruction
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstructionModels
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.RingTheory.PseudoCoherentNilpotentInvariance
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.NilpotentDerivedUpperBoundSupplement
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.NilpotentProjectiveModuleLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.NakayamaNilpotent
import WeilConjectures.RingTheory.FiniteProjectiveFreeModIdeal
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.OrzechProperty
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Algebra.Homology.ProperBaseChange.SurjectiveModuleComplexTowerLimitSupplement
import WeilConjectures.RingTheory.NilpotentMarkedFreeComplexLift
import WeilConjectures.RingTheory.UnmarkedFiniteFreeLift
import WeilConjectures.RingTheory.StablyFreeComplexLift
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal
import WeilConjectures.RingTheory.MarkedFiniteFreeLiftCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeProperties
import WeilConjectures.AlgebraicGeometry.ComplexLiftStrictMap
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeCokernel
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.AcyclicLift
import WeilConjectures.AlgebraicGeometry.ProjectiveClassReducedSplitting
import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower

/-!
# Effectivity of a normalized algebra tower

Source: Stacks Project, More on Algebra, Tags 09AV and 066E,
lemma-Rlim-pseudo-coherent-gives-complete-pseudo-coherent and
lemma-Noetherian-pseudo-coherent
(blueprint: lem-weil-pbc-pseudocoherent-normalized-algebra-tower).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tower_projection_compatible
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {X : ℕ → D} [HasProduct X] (f : ∀ n, X (n + 1) ⟶ X n)
    (E : D) (p : E ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle f E p δ) (m n : ℕ) (h : n ≤ m) :
    p ≫ Pi.π X m ≫ (Functor.ofOpSequence f).map (homOfLE h).op = p ≫ Pi.π X n := by
  have hs (k : ℕ) : p ≫ Pi.π X (k + 1) ≫ f k = p ≫ Pi.π X k := by
    have hz := Pretriangulated.comp_distTriang_mor_zero₁₂
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ) hE
    change p ≫ towerTransitionEndomorphism f = 0 at hz
    have hk := congrArg (fun a ↦ a ≫ Pi.π X k) hz
    have heq : p ≫ Pi.π X k - p ≫ Pi.π X (k + 1) ≫ f k = 0 := by
      simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp] using hk
    exact (sub_eq_zero.mp heq).symm
  let c : (Functor.const ℕᵒᵖ).obj E ⟶ Functor.ofOpSequence f :=
    NatTrans.ofOpSequence (fun n ↦ p ≫ Pi.π X n) (fun n ↦ by
      change 𝟙 E ≫ (p ≫ Pi.π X n) =
        (p ≫ Pi.π X (n + 1)) ≫ (Functor.ofOpSequence f).map (homOfLE _).op
      rw [CategoryTheory.Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ,
        CategoryTheory.Category.assoc]
      exact (hs n).symm)
  have hc := (c.naturality (homOfLE h).op).symm
  change (p ≫ Pi.π X m) ≫ (Functor.ofOpSequence f).map (homOfLE h).op =
    𝟙 E ≫ (p ≫ Pi.π X n) at hc
  simpa only [CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc] using hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedLimit_transport
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {X Y : ℕ → D} [HasProduct X] [HasProduct Y]
    (f : ∀ n, X (n + 1) ⟶ X n) (E : D)
    (p : E ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle f E p δ) (e : ∀ n, Y n ≅ X n) :
    IsDerivedLimit (fun n ↦ (e (n + 1)).hom ≫ f n ≫ (e n).inv) E := by
  let g : ∀ n, Y (n + 1) ⟶ Y n :=
    fun n ↦ (e (n + 1)).hom ≫ f n ≫ (e n).inv
  let a : ∏ᶜ Y ≅ ∏ᶜ X :=
    { hom := Limits.Pi.map (fun n ↦ (e n).hom)
      inv := Limits.Pi.map (fun n ↦ (e n).inv)
      hom_inv_id := by rw [Limits.Pi.map_comp_map]; simp only [Iso.hom_inv_id,
        Limits.Pi.map_id]
      inv_hom_id := by rw [Limits.Pi.map_comp_map]; simp only [Iso.inv_hom_id,
        Limits.Pi.map_id] }
  have ha : a.hom ≫ towerTransitionEndomorphism f =
      towerTransitionEndomorphism g ≫ a.hom := by
    apply towerTransitionEndomorphism_natural_backward g f (fun n ↦ (e n).hom)
    intro n
    simp [g]
  refine ⟨p ≫ a.inv, a.hom ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hE
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl E) a a ?_ ha.symm ?_
  · change (p ≫ a.inv) ≫ a.hom = 𝟙 E ≫ p
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · change (a.hom ≫ δ) ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 E) = a.hom ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem isIso_transpose_of_bijective
    {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {X : A} {Y : B} (t : X ⟶ R.obj Y)
    (ht : ∀ N : B, Function.Bijective (fun a : Y ⟶ N ↦ t ≫ R.map a)) :
    IsIso ((adj.homEquiv X Y).symm t) := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  have he (a : Y ⟶ N) : adj.homEquiv X N ((adj.homEquiv X Y).symm t ≫ a) =
      t ≫ R.map a := by
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  constructor
  · intro a b hab
    apply (ht N).1
    change t ≫ R.map a = t ≫ R.map b
    exact (he a).symm.trans ((congrArg (adj.homEquiv X N) hab).trans (he b))
  · intro b
    obtain ⟨a, ha⟩ := (ht N).2 (adj.homEquiv X N b)
    refine ⟨a, (adj.homEquiv X N).injective ?_⟩
    exact (he a).trans ha

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A normalized tower over an adically complete Noetherian ring is effective without a
perfectness assumption. Index `n` represents the positive level `n + 1`.

Normalization is written as the universal property of derived scalar extension: composing
with the supplied transition gives a bijection against every object over the quotient.
Likewise, `L n` is any left adjoint to exact derived restriction of scalars, hence is derived
scalar extension to `C / J^(n+1)`. The isomorphism `e n` is the adjunct of the given projection,
not an independently chosen isomorphism. The all-level equation gives compatibility with
transitions and their quotient cocycles. The last clause exhibits `E` itself as a derived
limit of its reductions, with transitions transported along these specified isomorphisms.

Source: Stacks Project, More on Algebra, Tags 09AV, 0CQF and 066E
(blueprint: lem-weil-pbc-pseudocoherent-normalized-algebra-tower).

Proof:
1. Quotients of the Noetherian ring C are Noetherian. The Noetherian cohomology criterion
   makes K 0 pseudo-coherent.
2. Adic completeness gives the compatible-tuple universal property of C as the limit of
   C/J^(n+1). Successive quotient maps are surjective with square-zero kernel: its square
   is the image of J^(2n+2), which lies in J^(n+2).
3. Derived scalar restriction has a left adjoint by the module scalar adjunction theorem.
   Normalization makes the transpose of t n an isomorphism, by Yoneda and the adjunction
   Hom equivalence. The canonical derived restriction-composition isomorphism satisfies
   the required normalization on complexes by the two factorization identities.
4. Apply isPseudoCoherent_inverse_ring_reconstruction, with these quotient rings and
   their limit C. It gives pseudo-coherence of E and invertibility of every projection's
   transpose, for any supplied choice of left adjoints.
5. The triangle identity identifies each unit followed by the restriction of that
   transpose with the original projection. A Roos triangle's consecutive arrows compose
   to zero, so its projections commute with consecutive transitions. The resulting
   natural transformation of inverse sequences proves compatibility at every level.
6. Transport the given product and Roos triangle along the isomorphisms of reductions.
   The induced product isomorphism conjugates the two shift operators; the identity on E
   and this product isomorphism identify the triangles. Thus E is a derived limit of its
   reductions, proving derived completeness. -/
theorem pseudoCoherent_normalizedAlgebraTower
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    (J : Ideal C) [IsAdicComplete J C]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} C)]
    [∀ n : ℕ, HasDerivedCategory.{w} (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj (K n))
    (hnorm : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))),
      Function.Bijective (fun a : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map a))
    (f : ∀ n : ℕ,
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.obj
        (K (n + 1)) ⟶
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))
    (hf : ∀ n : ℕ, f n =
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
        (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2))))).symm.inv.app
          (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n))
    [HasProduct (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))]
    (E : DerivedCategory (ModuleCat.{max u v} C))
    (p : E ⟶ ∏ᶜ (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))) ⟶ E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle f E p δ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{max u v} (C ⧸ J ^ (0 + 1))) i).obj (K 0)))
    (hfinite : ∀ i : ℤ, Module.Finite (C ⧸ J ^ (0 + 1))
      ((homologyFunctor (ModuleCat.{max u v} (C ⧸ J ^ (0 + 1))) i).obj (K 0))) :
    IsPseudoCoherent E ∧
      ∀ (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} C) ⥤
          DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1))))
        (adj : ∀ n : ℕ, L n ⊣
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory),
      ∃ e : ∀ n : ℕ, (L n).obj E ≅ K n,
        (∀ n : ℕ, (e n).hom = ((adj n).homEquiv E (K n)).symm (p ≫ Pi.π _ n)) ∧
        (∀ (m n : ℕ) (h : n ≤ m),
          (adj m).unit.app E ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (m + 1)))).mapDerivedCategory.map
              (e m).hom ≫
            (Functor.ofOpSequence (X := fun k : ℕ ↦
              (ModuleCat.restrictScalars.{max u v}
                (Ideal.Quotient.mk (J ^ (k + 1)))).mapDerivedCategory.obj (K k))
              f).map (homOfLE h).op =
          (adj n).unit.app E ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
              (e n).hom) ∧
        HasProduct (fun n : ℕ ↦
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
            ((L n).obj E)) ∧
        (∀ [HasProduct (fun n : ℕ ↦
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
            ((L n).obj E))],
          IsDerivedLimit (fun n : ℕ ↦
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
              (e (n + 1)).hom ≫ f n ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
              (e n).inv) E) := by
  classical
  let R (n : ℕ) := C ⧸ J ^ (n + 1)
  let φ (n : ℕ) : R (n + 1) →+* R n :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))
  let q (n : ℕ) : C →+* R n := Ideal.Quotient.mk (J ^ (n + 1))
  have hq (n : ℕ) : q n = (φ n).comp (q (n + 1)) :=
    (Ideal.Quotient.factor_comp_mk _).symm
  let χ (n : ℕ) : (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso
      (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n)) ≪≫
      (Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars (φ n))
        (ModuleCat.restrictScalars (q (n + 1)))).symm
  have hχ := fun n ↦ restrictScalarsComp_derived_factors (q (n + 1)) (φ n) (q n) (hq n)
  have htri : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (K n)) E p δ := by
    convert hE using 1
    funext n
    simpa only [χ, Iso.trans_inv, NatTrans.comp_app, Category.assoc] using (hf n).symm
  have : IsNoetherianRing (R 0) :=
    inferInstanceAs (IsNoetherianRing (C ⧸ J ^ (0 + 1)))
  have hpc₀ : IsPseudoCoherent (K 0) :=
    (isPseudoCoherent_iff_boundedAbove_finite_homology (R 0) (K 0)).2
      ⟨hbounded, hfinite⟩
  have (n : ℕ) : (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.IsRightAdjoint :=
    ModuleCat.derivedRestrictScalars_isRightAdjoint (φ n)
  have (n : ℕ) : (ModuleCat.restrictScalars (q n)).mapDerivedCategory.IsRightAdjoint :=
    ModuleCat.derivedRestrictScalars_isRightAdjoint (q n)
  let Lφ (n : ℕ) := (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.leftAdjoint
  let adjφ (n : ℕ) : Lφ n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory :=
    Adjunction.ofIsRightAdjoint _
  have hred (n : ℕ) : IsIso (((adjφ n).homEquiv (K (n + 1)) (K n)).symm (t n)) :=
    isIso_transpose_of_bijective (adjφ n) (t n) (hnorm n)
  have reconstruct
      (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} C) ⥤
        DerivedCategory (ModuleCat.{max u v} (R n)))
      (adj : ∀ n, L n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory) :
      IsPseudoCoherent E ∧
        ∀ n, IsIso (((adj n).homEquiv E (K n)).symm (p ≫ Pi.π _ n)) := by
    have hr := isPseudoCoherent_inverse_ring_reconstruction R φ
      (fun n ↦ Ideal.Quotient.factor_surjective _) (fun n ↦ adic_step_nilpotent J n)
      C q hq (adic_quotient_limit J) Lφ adjφ L adj χ hχ K t hred hpc₀ E p δ htri
    exact ⟨hr.1, hr.2.1⟩
  have hcore : IsPseudoCoherent E ∧
      ∀ (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} C) ⥤
          DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1))))
        (adj : ∀ n : ℕ, L n ⊣
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory),
        ∀ n, IsIso (((adj n).homEquiv E (K n)).symm (p ≫ Pi.π _ n)) := by
    let Lq (n : ℕ) := (ModuleCat.restrictScalars (q n)).mapDerivedCategory.leftAdjoint
    exact ⟨(reconstruct Lq (fun n ↦ Adjunction.ofIsRightAdjoint _)).1,
      fun L adj ↦ (reconstruct L adj).2⟩
  refine ⟨hcore.1, ?_⟩
  intro L adj
  have hi := hcore.2 L adj
  let e : ∀ n : ℕ, (L n).obj E ≅ K n :=
    fun n ↦ asIso (((adj n).homEquiv E (K n)).symm (p ≫ Pi.π _ n))
  have he (n : ℕ) : (adj n).unit.app E ≫
      (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map (e n).hom =
      p ≫ Pi.π _ n := by
    exact ((adj n).homEquiv_unit E (K n) (e n).hom).symm.trans
      (((adj n).homEquiv E (K n)).apply_symm_apply _)
  refine ⟨e, (fun n ↦ rfl), ?_, ?_, ?_⟩
  · intro m n h
    rw [← Category.assoc, he m, he n]
    simpa only [Category.assoc] using tower_projection_compatible f E p δ hE m n h
  · exact hasProduct_of_equiv_of_iso
      (fun n ↦ (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj (K n))
      _ (Equiv.refl ℕ)
      (fun n ↦ (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.mapIso (e n))
  · intro hprod
    exact derivedLimit_transport f E p δ hE
      (fun n ↦ (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.mapIso (e n))

end DerivedCategory
