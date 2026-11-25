/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjection
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemEvaluationBound
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCoefficientProjection
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.NumberTheory.Padics.NonunitCoefficientStages
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Nonflat coefficient mates and normalized ordinary étale systems

Source: Zheng, Proposition 2.29(2), Construction 2.26, Lemma 5.22 and Proposition 5.24,
printed pp. 16, 36--37 (blueprint: lem-pur-etale-system-quotient-normalization).

The first theorem identifies the actual coefficient mate by its counit and by the
constant-tensor map. The second uses the recorded evaluated transitions. All inputs
are in ordinary unbounded derived categories; no flatness or Tor bound is imposed.
The system index `n` denotes the positive exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace AlgebraicGeometry.Etale

/-- The coefficient complex D[0] with its C-action through the given ring map.
Source: Zheng, Proposition 2.29(2)
(blueprint: lem-pur-etale-system-quotient-normalization). -/
def quotientCoefficientComplex {C D : Type (u + 1)} [CommRing C] [CommRing D]
    (a : C →+* D) : DerivedCategory (ModuleCat.{u + 1} C) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))

/-- Restricted derived extension is constant tensor, in coefficient-first order.
This is the recorded representative-normalized scalar/tensor iso, the constant-sheaf
comparison, exact descent of the single complex, and the signed tensor symmetry.
Source: Zheng, Proposition 2.29(2); Stacks 03EK, 06YY
(blueprint: lem-pur-etale-system-quotient-normalization). -/
def quotientConstantTensorIso {C D : Type (u + 1)} [CommRing C] [CommRing D]
    (a : C →+* D) (W : Scheme.{u}) (K : DerivedCategoryModule C W) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology a).obj
        ((scalarExtension a W).obj K) ≅
      ((exceptionalCoefficientTensor C W).obj K).obj (quotientCoefficientComplex a) :=
  (scalarTensorIso a W).app K ≪≫
    ((derivedTensor (ModuleCat.{u + 1} C) W).obj K).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        ((constantCommuteCompose W.smallEtaleTopology
          (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
        (Functor.mapDerivedCategorySingleFunctor
          (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
            ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).app K).app
      ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        (quotientCoefficientComplex a))

private def quotientTensorNatIso {C D : Type (u + 1)} [CommRing C] [CommRing D]
    (a : C →+* D) (W : Scheme.{u}) :
    scalarExtension a W ⋙ Sheaf.derivedRestrictScalars W.smallEtaleTopology a ≅
      (exceptionalCoefficientTensor C W).flip.obj (quotientCoefficientComplex a) :=
  (scalarTensorIso a W) ≪≫
    (derivedTensor (ModuleCat.{u + 1} C) W).flip.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        ((constantCommuteCompose W.smallEtaleTopology
          (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
        (Functor.mapDerivedCategorySingleFunctor
          (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
            ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
    (Functor.flipping.functor.mapIso
      (derivedTensorSymmetry (ModuleCat.{u + 1} C) W)).app
      ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        (quotientCoefficientComplex a))

section SingleRing
variable {C D : Type (u + 1)} [CommRing C] [CommRing D]
  (a : C →+* D) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  {gC : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X}
  {gD : DerivedCategoryModule D Y ⥤ DerivedCategoryModule D X}
  (adjC : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ gC)
  (adjD : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c ⊣ gD)
  (q : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⋙
    scalarExtension a Y ≅ scalarExtension a X ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c)

/-- The six natural Hom bijections defining the restriction identification, in order.
Source: Zheng, Lemma 5.22, and the scalar adjunction of Stacks 07A6
(blueprint: lem-pur-etale-system-quotient-normalization). -/
def quotientRestrictionHomChain (K : DerivedCategoryModule C X)
    (H : DerivedCategoryModule D Y) :
    (K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).obj (gD.obj H)) ≃
      (K ⟶ gC.obj ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj H)) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).homEquiv K (gD.obj H)).symm
    |>.trans ((adjD.homEquiv _ H).symm)
    |>.trans (Iso.homCongr (q.app K).symm (Iso.refl H))
    |>.trans ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).homEquiv _ H)
    |>.trans (adjC.homEquiv K _)

/-- The actual coefficient mate, for arbitrary fixed exceptional adjunctions.
Source: Zheng, Construction 2.26, equation (2.26.1)
(blueprint: lem-pur-etale-system-quotient-normalization). -/
def etaleCoefficientQuotientMate :
    gC ⋙ scalarExtension a X ⟶ scalarExtension a Y ⋙ gD :=
  (mateEquiv adjC adjD (.mk _ _ _ _ q.inv))

private def quotientRestrictionIso :
    gD ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ⋙ gC :=
  conjugateIsoEquiv
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).comp adjD)
    (adjC.comp (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))) q

private theorem quotientRestrictionIso_chain
    (K : DerivedCategoryModule C X) (H : DerivedCategoryModule D Y)
    (z : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).obj (gD.obj H)) :
    z ≫ (quotientRestrictionIso a c adjC adjD q).hom.app H =
      quotientRestrictionHomChain a c adjC adjD q K H z := by
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  let j := ax.comp adjD
  let j' := adjC.comp ay
  let h := (j.homEquiv K H).symm z
  have he : j.homEquiv K H h ≫ (conjugateIsoEquiv j j' q).hom.app H =
      j'.homEquiv K H (q.hom.app K ≫ h) := by
    rw [j.homEquiv_unit, j'.homEquiv_unit]
    rw [Category.assoc, (conjugateIsoEquiv j j' q).hom.naturality h,
      ← Category.assoc]
    rw [conjugateIsoEquiv_apply_hom, unit_conjugateEquiv]
    rw [Category.assoc, ← Functor.map_comp]
  rw [show j.homEquiv K H h = z from (j.homEquiv K H).apply_symm_apply z] at he
  convert he using 1 <;>
    simp only [quotientRestrictionIso, quotientRestrictionHomChain, Adjunction.comp_homEquiv,
      Equiv.trans_apply, Equiv.symm_trans_apply, Iso.homCongr, Iso.symm_inv,
      Iso.refl_hom, Category.comp_id, ax, ay, j, j', h, Equiv.coe_fn_mk]
  all_goals rfl

private theorem quotientRestrictionIso_mate
    (r : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology a ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c)
    (hq : ∀ K : DerivedCategoryModule C X,
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).homEquiv _ _
          (q.hom.app K) =
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).unit.app K) ≫
          r.inv.app ((scalarExtension a X).obj K)) :
    (quotientRestrictionIso a c adjC adjD q).hom =
      (mateEquiv adjD adjC (.mk _ _ _ _ r.inv)) := by
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  have hm : mateEquiv ax ay (.mk _ _ _ _ q.hom) = .mk _ _ _ _ r.inv := by
    apply mateEquiv_eq_of_unit
    intro K
    exact (hq K).symm
  have he := iterated_mateEquiv_conjugateEquiv ax ay adjC adjD
    (.mk _ _ _ _ q.hom)
  rw [hm] at he
  exact he.symm

end SingleRing

/-- Finite-ring restriction commutes canonically with the exceptional adjoint. The
coefficient mate is invertible even for nonflat quotients. Its restricted map is exactly
the constant-tensor counit transpose, using the canonical scalar/tensor identifications.
Source: Zheng, Proposition 2.29(2), Construction 2.26 and Lemma 5.22
(blueprint: lem-pur-etale-system-quotient-normalization).

Proof (steps 1--4 of the node):
1. Compose the six adjunction Hom bijections in quotientRestrictionHomChain. Yoneda
produces rho and its inverse from the two identity maps. Naturality gives a natural
isomorphism. The scalar-unit normalization of q identifies this Hom bijection with
transposition of U(epsilon_D) after the inverse singleRestriction map; setting the input
map equal to the identity gives the displayed rho counit equation.
2. On flat-term K-flat representatives, restricted scalar extension is tensor by D[0].
The recorded change-of-rings tensor comparison, constant-sheaf comparison and signed
symmetry give quotientConstantTensorIso, independent of representatives. The coefficient
projection q, after restriction and singleRestriction, is the constant projection P.
3. Define b as the mate of q inverse. Its transpose is q inverse followed by the scalar
image of epsilon_C. Put w = rho after U(b). Apply F_C and epsilon_C. The counit equation
for rho and naturality of singleRestriction turn this into U(T(epsilon_C)) after U(q
inverse) and inverse singleRestriction. Step 2 identifies it with tensor(epsilon_C)
after P inverse. Injectivity of the adjunction Hom bijection proves the last equality.
4. The constant-tensor theorem applies to D[0] without finite projective dimension, so
this transpose is invertible. Thus U(b) is invertible, and exact scalar restriction
reflects isomorphisms: it leaves the underlying cohomology sheaves of the cone unchanged.
Therefore b is invertible. All constructions are natural on the whole unbounded
categories, and their deriving comparisons make them independent of resolutions. -/
theorem etaleCoefficientQuotientNormalization
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ k.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k.k))] [Y.Over (Spec (.of k.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k.k))]
    [QuasiCompact (X ↘ Spec (.of k.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k.k))]
    [QuasiCompact (Y ↘ Spec (.of k.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (C D : Type (u + 1)) [CommRing C] [CommRing D] [Finite C] [Finite D]
    (_hC : ∃ r : ℕ, (l ^ r : C) = 0) (_hD : ∃ r : ℕ, (l ^ r : D) = 0)
    (a : C →+* D)
    (gC : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X)
    (gD : DerivedCategoryModule D Y ⥤ DerivedCategoryModule D X)
    (adjC : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ gC)
    (adjD : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c ⊣ gD) :
    ∃ q : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⋙
        scalarExtension a Y ≅ scalarExtension a X ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c,
      q.hom = compactScalarMap a c ∧
      ∃ r : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c ⋙
          Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ≅
        Sheaf.derivedRestrictScalars X.smallEtaleTopology a ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c,
        r.hom = SystemProjection.singleRestriction (CommRingCat.ofHom a) c ∧
      ∃ rho : gD ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a ≅
          Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ⋙ gC,
        (∀ (K : DerivedCategoryModule C X) (H : DerivedCategoryModule D Y)
          (z : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).obj (gD.obj H)),
          z ≫ rho.hom.app H = quotientRestrictionHomChain a c adjC adjD q K H z) ∧
        (∀ H : DerivedCategoryModule D Y,
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
              (rho.hom.app H) ≫
            adjC.counit.app ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj H) =
          r.inv.app (gD.obj H) ≫
            (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map (adjD.counit.app H)) ∧
        ∃ b : gC ⋙ scalarExtension a X ≅ scalarExtension a Y ⋙ gD,
          b.hom = etaleCoefficientQuotientMate a c adjC adjD q ∧
          (∀ M : DerivedCategoryModule C Y,
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c).map
                (b.hom.app M) ≫ adjD.counit.app ((scalarExtension a Y).obj M) =
              q.inv.app (gC.obj M) ≫ (scalarExtension a Y).map (adjC.counit.app M)) ∧
          ∃ P : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⋙
              (exceptionalCoefficientTensor C Y).flip.obj (quotientCoefficientComplex a) ≅
            (exceptionalCoefficientTensor C X).flip.obj (quotientCoefficientComplex a) ⋙
              rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c,
            (∀ K : DerivedCategoryModule C X, P.hom.app K =
              exceptionalConstantProjectionMap C c (quotientCoefficientComplex a) K) ∧
            ∀ M : DerivedCategoryModule C Y,
              (quotientConstantTensorIso a X (gC.obj M)).inv ≫
                (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).map (b.hom.app M) ≫
                rho.hom.app ((scalarExtension a Y).obj M) ≫
                gC.map (quotientConstantTensorIso a Y M).hom =
              adjC.homEquiv _ _ (P.inv.app (gC.obj M) ≫
                ((exceptionalCoefficientTensor C Y).flip.obj
                  (quotientCoefficientComplex a)).map (adjC.counit.app M)) := by
  classical
  let xadj := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)
  let yadj := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  let FC := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c
  let FD := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c
  let UX := Sheaf.derivedRestrictScalars X.smallEtaleTopology a
  let UY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  let TX := scalarExtension a X
  let TY := scalarExtension a Y
  have hqiso : IsIso (compactScalarMap a c) := by
    suffices ∀ K, IsIso ((compactScalarMap a c).app K) from
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    intro K
    have := proper_scalarMate_isIso a c.g
      ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)
    change IsIso ((scalarMate a c.g).app _ ≫
      (lowerStar (ModuleCat.{u + 1} D) c.g).rightDerivedFunctor.map
        ((ExceptionalCoefficients.openIso a c.i).hom.app K))
    infer_instance
  obtain ⟨r, hr, hu⟩ := (SystemProjection.etaleSingleCoefficientProjection c l).1
    (.of C) (.of D) inferInstance inferInstance _hC _hD (CommRingCat.ofHom a)
  let := hqiso
  let q := asIso (compactScalarMap a c)
  let rho := quotientRestrictionIso a c adjC adjD q
  have hrho : rho.hom = (mateEquiv adjD adjC (.mk _ _ _ _ r.inv)) :=
    quotientRestrictionIso_mate a c adjC adjD q r hu
  have : Fact k.p.Prime := ⟨k.prime⟩
  let := Fintype.ofFinite k.k₀
  have : CharP k.k₀ k.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := k.k₀)).symm.trans
      (k.card_base.trans k.cardinality_eq))
  have : IsAlgClosed k.k := IsAlgClosure.isAlgClosed k.k₀
  have : CharP k.k k.p :=
    charP_of_injective_algebraMap (algebraMap k.k₀ k.k).injective k.p
  obtain ⟨_, htensor⟩ := exceptionalConstantTensor k.k k.p l _hl
    (X ↘ Spec (.of k.k)) (Y ↘ Spec (.of k.k)) f (comp_over f _)
  have htorsion : ∃ n : ℕ, ∀ z : C, (l : C) ^ n * z = 0 := by
    obtain ⟨n, hn⟩ := _hC
    refine ⟨n, fun z ↦ ?_⟩
    rw [show (l : C) ^ n = 0 by simpa only [Nat.cast_pow] using hn, zero_mul]
  obtain ⟨P₀, hP₀, A₀, hA₀⟩ := (htensor c C htorsion).2.2 gC adjC
  let V := quotientCoefficientComplex a
  let P : FC ⋙ (exceptionalCoefficientTensor C Y).flip.obj V ≅
      (exceptionalCoefficientTensor C X).flip.obj V ⋙ FC :=
    NatIso.ofComponents (fun K ↦ (P₀.app K).app V)
      (fun z ↦ congrArg (fun t ↦ t.app V) (P₀.hom.naturality z))
  have hP (K : DerivedCategoryModule C X) :
      P.hom.app K = exceptionalConstantProjectionMap C c V K := hP₀ V K
  let eX := quotientTensorNatIso a X
  let eY := quotientTensorNatIso a Y
  have he (K : DerivedCategoryModule C X) :
      r.inv.app (TX.obj K) ≫ UY.map (q.inv.app K) ≫ eY.hom.app (FC.obj K) =
        FC.map (eX.hom.app K) ≫ P.inv.app K := by
    have hp : UY.map (q.hom.app K) ≫ r.hom.app (TX.obj K) ≫
        FC.map (eX.hom.app K) = eY.hom.app (FC.obj K) ≫ P.hom.app K := by
      rw [hP, hr]
      exact etaleQuotientTensorProjection a c K
    apply (cancel_epi (UY.map (q.hom.app K) ≫ r.hom.app (TX.obj K))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← UY.map_comp_assoc,
      Iso.hom_inv_id_app, UY.map_id, Category.id_comp]
    have hp' := congrArg (fun z ↦ z ≫ P.inv.app K) hp
    simp only [Category.assoc, Iso.hom_inv_id_app] at hp'
    erw [Category.comp_id] at hp'
    exact hp'.symm
  let b₀ := etaleCoefficientQuotientMate a c adjC adjD q
  have hb (M : DerivedCategoryModule C Y) :
      (eX.app (gC.obj M)).inv ≫ UX.map (b₀.app M) ≫ rho.hom.app (TY.obj M) ≫
        gC.map (eY.hom.app M) =
      adjC.homEquiv _ _ (P.inv.app (gC.obj M) ≫
        ((exceptionalCoefficientTensor C Y).flip.obj V).map (adjC.counit.app M)) := by
    have hh := restricted_mate_tensor adjC adjD TX TY UX UY q.inv r.inv
      ((exceptionalCoefficientTensor C X).flip.obj V)
      ((exceptionalCoefficientTensor C Y).flip.obj V) eX eY
      (fun K ↦ P.inv.app K) he M
    have hh' : UX.map (b₀.app M) ≫ rho.hom.app (TY.obj M) =
        eX.hom.app (gC.obj M) ≫
          adjC.homEquiv _ _ (P.inv.app (gC.obj M) ≫
            ((exceptionalCoefficientTensor C Y).flip.obj V).map
              (adjC.counit.app M)) ≫ gC.map (eY.inv.app M) := by
      rw [hrho]
      exact hh
    apply (cancel_epi (eX.hom.app (gC.obj M))).1
    simp only [Iso.app_inv, Iso.hom_inv_id_app_assoc]
    have hh'' := congrArg (fun z ↦ z ≫ gC.map (eY.hom.app M)) hh'
    simp only [Category.assoc, ← gC.map_comp, Iso.inv_hom_id_app] at hh''
    erw [gC.map_id, Category.comp_id] at hh''
    exact hh''
  have hbiso : IsIso b₀ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    have hA : IsIso (adjC.homEquiv _ _ (P.inv.app (gC.obj M) ≫
        ((exceptionalCoefficientTensor C Y).flip.obj V).map (adjC.counit.app M))) := by
      have heq := hA₀ V M
      change (A₀.hom.app M).app V = adjC.homEquiv _ _
        (P.inv.app (gC.obj M) ≫
          ((exceptionalCoefficientTensor C Y).flip.obj V).map
            (adjC.counit.app M)) at heq
      rw [← heq]
      infer_instance
    have hi : IsIso ((eX.app (gC.obj M)).inv ≫ UX.map (b₀.app M) ≫
        rho.hom.app (TY.obj M) ≫ gC.map (eY.hom.app M)) := by
      rw [hb M]
      exact hA
    have hi' : IsIso (UX.map (b₀.app M)) := by
      simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi
    exact isIso_of_reflects_iso (b₀.app M) UX
  let := hbiso
  refine ⟨q, rfl, r, hr, rho, ?_, ?_, asIso b₀, rfl, ?_, P, hP, ?_⟩
  · exact quotientRestrictionIso_chain a c adjC adjD q
  · intro H
    rw [hrho]
    exact mateEquiv_counit adjD adjC (.mk _ _ _ _ r.inv) H
  · intro M
    exact mateEquiv_counit adjC adjD (.mk _ _ _ _ q.inv) M
  · exact hb

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem brownFiniteQuotient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ha : ∃ r : ℕ, (l : A) ^ r = 0) (hb : ∃ r : ℕ, (l : B) ^ r = 0)
    (a : A →+* B)
    (ga : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (gb : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (aa : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ ga)
    (ab : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ gb) :
    ∃ q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c,
      q.hom = Etale.compactScalarMap a c ∧
        IsIso (mateEquiv aa ab (.mk _ _ _ _ q.inv)) := by
  obtain ⟨q, hq, r, _, rho, _, _, b, hb, _⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl f c A B
      (by simpa only [Nat.cast_pow] using ha)
      (by simpa only [Nat.cast_pow] using hb) a ga gb aa ab
  refine ⟨q, hq, ?_⟩
  change IsIso (Etale.etaleCoefficientQuotientMate a c aa ab q)
  rw [← hb]
  infer_instance

private theorem brownInverseWord {C : Type*} [Category C]
    {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ≅ V₃)
    (d : V₃ ≅ V₄) (e : V₄ ≅ V₅) (q : V₀ ≅ V₅)
    (h : a ≫ b ≫ c.hom ≫ d.hom ≫ e.hom = q.hom) :
    e.inv ≫ d.inv ≫ c.inv = q.inv ≫ a ≫ b := by
  apply (cancel_epi q.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    Iso.hom_inv_id]

private theorem brownCubeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [c.ReflectsIsomorphisms]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)))
    (hK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)))
    (hθ : IsIso (mateEquiv adj' adjK' (.mk _ _ _ _ θ'))) :
    IsIso (mateEquiv adj adjK (.mk _ _ _ _ θ)) := by
  have hFapp (M : B) : IsIso ((mateEquiv adj adj'
      (.mk _ _ _ _ pF.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hKapp (M : D) : IsIso ((mateEquiv adjK adjK'
      (.mk _ _ _ _ pK.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hθapp (M : B') : IsIso ((mateEquiv adj' adjK'
      (.mk _ _ _ _ θ')).app M) := NatIso.isIso_app_of_isIso _ M
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc M
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M)) := by
    rw [he]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M))
  exact isIso_of_reflects_iso _ c

private theorem brownQuotientMate_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {O : Type (u + 1)} [CommRing O] {t : O}
    (S : StrictEtaleCompactSupport O t c) (B : StrictEtaleBrownConstruction O t c S)
    (hfinite : ∀ n, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n, ∃ r : ℕ, (l : strictEtaleBrownRing O t n) ^ r = 0)
    (g : ∀ n, DerivedCategory (strictEtaleLevel Y O t n) ⥤
      DerivedCategory (strictEtaleLevel X O t n))
    (adjN : ∀ n, S.levelFunctor n ⊣ g n) {m n : ℕ} (h : n ≤ m) :
    IsIso (strictEtaleBrownQuotientMate B adjN h) := by
  have : Finite (strictEtaleBrownRing O t m) := hfinite m
  have : Finite (strictEtaleBrownRing O t n) := hfinite n
  have := B.realizationX.val.equivalence m
  have := B.realizationY.val.equivalence m
  have := B.realizationX.val.equivalence n
  have := B.realizationY.val.equivalence n
  let Fm := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c
  let Fn := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  have : Fm.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  have : Fn.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  let am : Fm ⊣ Fm.rightAdjoint := Adjunction.ofIsLeftAdjoint Fm
  let an : Fn ⊣ Fn.rightAdjoint := Adjunction.ofIsLeftAdjoint Fn
  obtain ⟨q, hq, hib⟩ := brownFiniteQuotient D l hl f c
    (strictEtaleBrownRing O t m) (strictEtaleBrownRing O t n)
    (htorsion m) (htorsion n) (strictEtaleBrownRingMap O t h)
    Fm.rightAdjoint Fn.rightAdjoint am an
  have him := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN m) am (B.realizationX.derived m) (B.realizationY.derived m)
    (B.levelComparison m).symm
  have hin := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN n) an (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison n).symm
  have hc (P : DerivedCategory (strictEtaleLevel X O t m)) :
      Fn.map ((B.realizationX.scalar h).inv.app P) ≫
        (B.levelComparison n).inv.app ((S.PX.scalar h).derived.obj P) ≫
        (B.realizationY.derived n).map ((B.projection h).hom.app P) =
      q.inv.app ((B.realizationX.derived m).obj P) ≫
        (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
          ((B.levelComparison m).inv.app P) ≫
        (B.realizationY.scalar h).inv.app ((S.levelFunctor m).obj P) := by
    have he := B.projection_recorded_q h P
    rw [← hq] at he
    exact brownInverseWord _ _
      ((B.realizationY.derived n).mapIso ((B.projection h).app P)).symm
      ((B.levelComparison n).app ((S.PX.scalar h).derived.obj P))
      (Fn.mapIso ((B.realizationX.scalar h).app P))
      (q.app ((B.realizationX.derived m).obj P)) he
  exact brownCubeMate_isIso (adjN m) (adjN n) am an
    (B.realizationX.derived m) (B.realizationY.derived m)
    (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison m) (B.realizationX.scalar h)
    (B.realizationY.scalar h) (B.levelComparison n)
    (B.projection h).hom q.inv hc him hin hib

end AlgebraicGeometry
