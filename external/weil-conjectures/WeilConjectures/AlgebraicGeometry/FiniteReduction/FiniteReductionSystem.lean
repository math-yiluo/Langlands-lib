/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Data.ZMod.Basic

/-!
# Fixed scalar extensions and their normalized derived comparison system

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks Tags 06YT, 06YY and 03EL.
The interface is extracted from `FiniteReductionConstructibility` without changing its meaning.
The quotient-composition proof is written explicitly to keep elaboration bounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteReduction

/-- Size lift of the actual quotient ring. Source: blueprint lemma-sp-reduction,
finite coefficients (blueprint: def-per-finite-reduction-coefficients). -/
abbrev Ring (l r : ℕ) := ULift.{u} (ZMod (l ^ r))

/-- Module-size lift of the same coefficient ring. Source: blueprint lemma-sp-reduction,
finite coefficients (blueprint: def-per-finite-reduction-coefficients). -/
abbrev Coeff (l r : ℕ) := ULift.{u + 1} (Ring.{u} l r)

/-- The actual quotient map, lifted to the module universe. Source: blueprint
lemma-sp-reduction (blueprint: def-per-finite-reduction-coefficients). -/
def quotient (l : ℕ) {r m : ℕ} (h : m ≤ r) : Coeff.{u} l r →+* Coeff.{u} l m :=
  ((ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m))).ulift).ulift

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)

/-- Scalar extension is sheafification of sectionwise scalar extension; it does not
assume the quotient is flat. Source: Stacks 06YY
(blueprint: def-pur-finite-reduction-system). -/
def extend : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

/-- The standard tensor/restriction adjunction, fixing all tensor units. Source: Stacks
06YY (blueprint: def-pur-finite-reduction-system). -/
def extendAdjunction : extend J f ⊣ Sheaf.restrictScalars J f :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1} f)

/-- Additivity comes from the tensor/restriction adjunction. Source: Stacks 06YY
(blueprint: def-pur-finite-reduction-system). -/
instance extend_additive : (extend J f).Additive :=
  (extendAdjunction J f).left_adjoint_additive

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universal derived tensor extension, including its canonical K-flat computation.
This records the universal pair, rather than an unspecified functor or isomorphism.
Source: Stacks 06YT and 06YY
(blueprint: def-pur-finite-reduction-system). -/
structure DerivedExtension where
  functor : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))
  counit : DerivedCategory.Q ⋙ functor ⟶
    (extend J f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))
  computation : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → IsIso (counit.app P)

end Site

/-- Canonical ordinary comparison: both sides are left adjoint to the same restriction
functor. Its normalization is the identity on that right adjoint, hence on local pure
tensors. Source: Stacks 03EL
(blueprint: def-pur-finite-reduction-system). -/
def ordinaryComparison (T : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) :
    extend T.smallEtaleTopology f ⋙ ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ extend (Scheme.ProEt.topology T) f :=
  Adjunction.leftAdjointUniq
    ((extendAdjunction T.smallEtaleTopology f).comp (ProEtale.comparisonAdjunction _ T))
    ((ProEtale.comparisonAdjunction _ T).comp
      (extendAdjunction (Scheme.ProEt.topology T) f))

/-- The ordinary tensor associator, fixed by the identity on scalar restriction.
On local tensors it sends c tensor (b tensor q) to (bc) tensor q, equivalently
(q tensor b) tensor c to q tensor bc in the right-tensor convention of the source.
Source: blueprint lemma-sp-reduction, associativity
(blueprint: def-pur-finite-reduction-system). -/
def ordinaryAssociator {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (l : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    extend J (quotient.{u} l hmr) ⋙ extend J (quotient l hnm) ≅
      extend J (quotient l (hnm.trans hmr)) :=
by
  have hq : quotient.{u} l (hnm.trans hmr) =
      (quotient.{u} l hnm).comp (quotient.{u} l hmr) := by
    apply RingHom.ext
    intro x
    change (⟨⟨ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n))
        x.down.down⟩⟩ : Coeff.{u} l n) =
      ⟨⟨ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m)) x.down.down)⟩⟩
    congr 2
    exact DFunLike.congr_fun (Subsingleton.elim
      (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
      ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down
  exact Adjunction.leftAdjointUniq
    (((extendAdjunction J (quotient l hmr)).comp
      (extendAdjunction J (quotient l hnm))).ofNatIsoRight
        (Sheaf.restrictScalarsCompIso J (quotient l hmr) (quotient l hnm)
          (quotient l (hnm.trans hmr)) hq))
    (extendAdjunction J (quotient l (hnm.trans hmr)))

/-- The actual termwise comparison on complexes. Source: Stacks 03EL
(blueprint: def-pur-finite-reduction-system). -/
abbrev ordinaryComparisonComplex (T : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) :=
  NatIso.mapHomologicalComplex (ordinaryComparison T f) (.up ℤ)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical coefficient extension on the two sites, including representative
normalizations of its comparison and its associators. All functors are universal derived
functors of the concrete scalar extensions above. The normalizations remove arbitrary
choices of natural isomorphisms. Source: Stacks 06YT, 06YY and 03EL; blueprint
lemma-sp-reduction (blueprint: def-pur-finite-reduction-system). -/
structure System (T : Scheme.{u}) (l : ℕ) where
  etale : ∀ (r m : ℕ) (h : m ≤ r),
    DerivedExtension T.smallEtaleTopology (quotient.{u} l h)
  proetale : ∀ (r m : ℕ) (h : m ≤ r),
    DerivedExtension (Scheme.ProEt.topology T) (quotient.{u} l h)
  comparison : ∀ (r m : ℕ) (h : m ≤ r),
    (etale r m h).functor ⋙
      (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory ≅
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory ⋙
      (proetale r m h).functor
  comparison_model : ∀ (r m : ℕ) (h : m ≤ r)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (comparison r m h).hom.app (DerivedCategory.Q.obj P) ≫
      (proetale r m h).functor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategoryFactors.hom.app P) ≫
      (proetale r m h).counit.app
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapHomologicalComplex (.up ℤ)).obj P) =
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.map
      ((etale r m h).counit.app P) ≫
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategoryFactors.hom.app
        (((extend T.smallEtaleTopology (quotient l h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((ordinaryComparisonComplex T (quotient l h)).hom.app P)
  etaleAssociator : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m),
    (etale r m hmr).functor ⋙ (etale m n hnm).functor ≅
      (etale r n (hnm.trans hmr)).functor
  proetaleAssociator : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m),
    (proetale r m hmr).functor ⋙ (proetale m n hnm).functor ≅
      (proetale r n (hnm.trans hmr)).functor
  etaleAssociator_model : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (etaleAssociator r m n hmr hnm).hom.app (DerivedCategory.Q.obj P) ≫
      (etale r n (hnm.trans hmr)).counit.app P =
    (etale m n hnm).functor.map ((etale r m hmr).counit.app P) ≫
      (etale m n hnm).counit.app
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryAssociator T.smallEtaleTopology l hmr hnm) (.up ℤ)).hom.app P)
  proetaleAssociator_model : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (P : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (proetaleAssociator r m n hmr hnm).hom.app (DerivedCategory.Q.obj P) ≫
      (proetale r n (hnm.trans hmr)).counit.app P =
    (proetale m n hnm).functor.map ((proetale r m hmr).counit.app P) ≫
      (proetale m n hnm).counit.app
        (((extend (Scheme.ProEt.topology T) (quotient l hmr)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm) (.up ℤ)).hom.app P)

/-- Finiteness of the actual coefficients, derived from primality, not an extra
hypothesis. Source: blueprint lemma-sp-reduction
(blueprint: def-pur-finite-reduction-system). -/
instance ringFinite (l : ℕ) [h : Fact l.Prime] (r : ℕ) : Finite (Ring.{u} l r) := by
  let : NeZero l := ⟨h.out.ne_zero⟩
  infer_instance

/-- The canonical realization in the intrinsic constant-ring presentation, used solely
to apply the recorded intrinsic constructibility and Tor predicates. Source: Stacks 00YV
and 09AL (blueprint: def-pur-finite-reduction-system). -/
def realize (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))) ⥤
      Scheme.proEtaleDerivedCategory T (Ring.{u} l r) :=
  (ProEtale.finiteCoefficientIntrinsicRealization.{u} T (Ring.{u} l r)).mapDerivedCategory

end AlgebraicGeometry.FiniteReduction
