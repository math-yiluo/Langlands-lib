/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-! # Data for the simultaneous Cartier Kummer map

Source: blueprint main-20261015, lemma-cycle-class-cartier-divisor, paragraphs 1--4.
(blueprint: def-amb-cartier-kummer-data)

The declarations are the original fixed-coefficient interfaces, without changes
of signature or body. They are separate from the existence theorem so that
normalization and transport results can refer to them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme

/-- Reuse the existing left-exact sheafification at each etale module site.
Source: Stacks 00WX (blueprint: def-amb-cartier-kummer-data). -/
instance cartierHasSheafifyEtale (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Cache the existing weak etale sheafification separately from left exactness.
Source: Stacks 00WX (blueprint: def-amb-cartier-kummer-data). -/
instance cartierHasWeakSheafifyEtale (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Reuse abelian sheafification for the cohomological Chern-class realization.
Source: Stacks 00WX (blueprint: def-amb-cartier-kummer-data). -/
instance cartierHasSheafifyAbelian (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  inferInstance

/-- Reuse small Ext for the existing abelian cohomology realization.
Source: Stacks 07A6 (blueprint: def-amb-cartier-kummer-data). -/
instance cartierHasExtAbelian (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Name the existing abelian structure on etale module sheaves.
Source: Stacks 03D0 (blueprint: def-amb-cartier-kummer-data). -/
instance cartierAbelianEtale (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

/-- Name the existing abelian structure used by the Chern-class realization.
Source: Stacks 03D0 (blueprint: def-amb-cartier-kummer-data). -/
instance cartierAbelianGroups (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Cache the existing small Ext instance without changing its universe or category.
Source: Stacks 07A6 (blueprint: def-amb-cartier-kummer-data). -/
instance cartierHasExtEtale (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant-section comparison for the inclusion of sites, specified by adjunction.
Source: Stacks 099R and 00WX (blueprint: def-amb-cartier-kummer-data). -/
def cartierConstantComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (ordinaryFiniteConstant A T) ⟶
      (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).symm
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A)))))

/-- The etale witnesses at every annihilating Kummer exponent.
Source: proof, paragraphs 3--4 (blueprint: def-amb-cartier-kummer-data). -/
def CartierEtaleKummerFamily : Type (u + 1) :=
  ∀ (n r : ℕ) (_hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hT : IsUnit (l : Γ(T, ⊤))),
    Ext ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
      (ordinaryFiniteConstant (finiteTateCoefficient l E n) D))
        (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) _hA) 2

/-- Relative-boundary normalization of all ordinary etale witnesses.
This retains the actual frame torsor and its canonical section on the complement.
Source: proof, paragraphs 1--3 (blueprint: def-amb-cartier-kummer-data). -/
@[irreducible]
def CartierEtaleKummerNormalization (κ : CartierEtaleKummerFamily l E) : Prop :=
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    SupportedKummerBoundary (finiteTateCoefficient l E n) (l ^ (r + 1)) hA i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) (κ n r hA i hI hT)

/-- Compatibility with every finite coefficient reduction at a common Kummer exponent.
SupportedKummerScalar specifies both derived scalar units on all unbounded test objects
and fixes the scalar maps on constants and pure root tensors.
Source: proof, final scalar-extension sentence
(blueprint: def-amb-cartier-kummer-data). -/
@[irreducible]
def CartierEtaleKummerReduction (κ : CartierEtaleKummerFamily l E) : Prop :=
  ∀ (a b : ℕ) (hab : a ≤ b) (r : ℕ)
    (hb : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E b) = 0)
    (ha : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E a) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    SupportedKummerScalar (cartierCoefficientReduction l E a b hab) (l ^ (r + 1)) hb ha i
      (κ b r hb i hI hT) (κ a r ha i hI hT)

/-- Descent of each etale witness to the same arrow in the specified pro-etale twist.
The support comparison is uniquely fixed by the quotient map. The target comparison
is fixed by inverse-limit projection. Quantifying over every r while c is fixed
states independence of the Kummer exponent as equality of derived arrows.
Source: proof, final paragraph (blueprint: def-amb-cartier-kummer-data). -/
@[irreducible]
def CartierKummerRealization (κ : CartierEtaleKummerFamily l E)
    (c : CartierKummerFamily l E) : Prop :=
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∃ (α : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
            (ordinaryFiniteConstant (finiteTateCoefficient l E n) D)) ≅ cartierSupported l E n i)
      (q : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) ≅
            finiteTateProSheaf l E n T 1),
      IsFiniteTateSiteComparison l E n T r hA 1 q ∧
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).map
          (supportedConstantUnit (finiteTateCoefficient l E n) i) ≫ α.hom =
        cartierConstantComparison (finiteTateCoefficient l E n) T ≫
          cartierSupportedUnit l E n i ∧
      (Ext.mk₀ α.hom).comp (c n i hI hT) (zero_add 2) =
        ((κ n r hA i hI hT).mapExactFunctor
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
          (Ext.mk₀ q.hom) (add_zero 2)

/-- The asserted pro-etale base-change equation under the canonical comparisons.
The support comparison is fixed by the constant quotient unit and the twist comparison
by all root projections. No flatness is imposed on h.
Source: proof, paragraph 4 (blueprint: def-amb-cartier-kummer-data). -/
@[irreducible]
def CartierKummerBaseChange (c : CartierKummerFamily l E) : Prop :=
  ∀ (n : ℕ) {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i'] (h : T' ⟶ T) (w : D' ⟶ D)
    (_sq : IsPullback w i' i h) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤))),
    ∃ (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).obj
        (cartierSupported l E n i) ≅ cartierSupported l E n i')
      (t : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).obj
        (finiteTateProSheaf l E n T 1) ≅ finiteTateProSheaf l E n T' 1),
      IsFiniteTateProPullback l E n T h 1 t ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).map
          (cartierSupportedUnit l E n i) ≫ p.hom =
        Scheme.proEtaleConstantInverseImageMap h
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
            (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)) ≫
          cartierSupportedUnit l E n i' ∧
      (Ext.mk₀ p.hom).comp (c n i' hI' hT') (zero_add 2) =
        ((c n i hI hT).mapExactFunctor
          (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h)).comp
            (Ext.mk₀ t.hom) (add_zero 2)

/-- The ordinary first Chern class, transported by the same projection-normalized
comparison, is the composite with the supported quotient map.
The cohomology class is written directly in Ext: the definition of `ordinaryFiniteClass`
reduces to this expression by cancelling `Ext.homEquiv.symm (Ext.homEquiv k)`.
This avoids elaborating the intermediate derived arrow and its inverse realization.
Source: proof, paragraphs 3--4 (blueprint: def-amb-cartier-kummer-data). -/
@[irreducible]
def CartierKummerChern (c : CartierKummerFamily l E) : Prop :=
  ∀ (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0),
      ∃ (k : Ext (ordinaryFiniteConstant (finiteTateCoefficient l E n) T)
        (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) 2)
        (q : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
            (Scheme.finiteEtaleTateLine T (l ^ (r + 1))
              (finiteTateCoefficient l E n) hA) ≅ finiteTateProSheaf l E n T 1),
        IsFiniteTateSiteComparison l E n T r hA 1 q ∧
        (Ext.mk₀ (ordinaryFiniteIntegralGenerator (finiteTateCoefficient l E n) T)).comp
          (k.mapExactFunctor (RawModuleScalarComparison.forget (finiteTateCoefficient l E n) T))
          (zero_add 2) = supportedKummerChern (finiteTateCoefficient l E n)
            (l ^ (r + 1)) hA i hI
              (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) ∧
        (Ext.mk₀ (cartierConstantComparison (finiteTateCoefficient l E n) T)).comp
          ((Ext.mk₀ (cartierSupportedUnit l E n i)).comp (c n i hI hT) (zero_add 2))
            (zero_add 2) =
          (k.mapExactFunctor (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
              (Ext.mk₀ q.hom) (add_zero 2)

end AlgebraicGeometry.Etale
