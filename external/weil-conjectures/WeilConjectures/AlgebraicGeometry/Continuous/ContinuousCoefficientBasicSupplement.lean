/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientBasic

/-!
# Continuous coefficient sheaves and immersion restriction

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1,
Lemma 6.8.2 and the paragraph preceding Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme

private theorem commRingForgetReflectsLimit {J : Type v} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Limits.Cone F)
    (hc : Limits.IsLimit ((CategoryTheory.forget CommRingCat).mapCone c)) :
    Nonempty (Limits.IsLimit c) := by
  let ext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    apply (Limits.Types.isLimitEquivSections hc).injective
    exact Subtype.ext (funext h)
  let lift (s : Limits.Cone F) : s.pt ⟶ c.pt := CommRingCat.ofHom
    { toFun := hc.lift ((CategoryTheory.forget CommRingCat).mapCone s)
      map_one' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (1 : s.pt)
      map_mul' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_mul]
        rw [hj, hj, hj, map_mul]
      map_zero' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (0 : s.pt)
      map_add' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_add]
        rw [hj, hj, hj, map_add] }
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply ext
    intro j
    exact (congrArg (fun f : s.pt ⟶ _ ↦ f x) (hm j)).trans
      (ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x).symm

/-- The coefficient extension field equipped with its spectral norm.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
@[instance_reducible]
noncomputable def coefficientExtensionNormedField (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : NormedField E :=
  (Padic.coefficientExtensionAbsoluteValue l E).toNormedField

/-- Integral continuous coefficient sheaf `A_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))

/-- Rational continuous coefficient sheaf `E_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The finite quotient ring at positive level `n+1`, lifted to the pro-etale coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRing (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))

/-- Quotient transition map for positive coefficient levels.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRingMap (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {m n : ℕ} (h : n ≤ m) : finiteCoefficientRing l E m ⟶ finiteCoefficientRing l E n :=
  CommRingCat.ofHom <| RingHom.ulift <|
    Ideal.Quotient.factor (by
      simpa [Padic.coefficientExtensionIdeal] using
        (Ideal.pow_le_pow_right (I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) (Nat.succ_le_succ h)))

/-- The quotient maps satisfy the identity law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: A quotient map induced by the identity acts identically on every representative;
quotient induction proves it is the identity ring map. Apply constantSheaf.map_id.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕᵒᵖ) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (finiteCoefficientRingMap l E (h := le_rfl)) =
      𝟙 ((CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (finiteCoefficientRing l E n.unop)) := by
  have hmap : finiteCoefficientRingMap l E (h := le_rfl (a := n.unop)) =
      𝟙 (finiteCoefficientRing l E n.unop) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl
  rw [hmap, CategoryTheory.Functor.map_id]

private theorem uliftQuotientFactorComp {R : Type u} [CommRing R]
    {I J K : Ideal R} (hIJ : I ≤ J) (hJK : J ≤ K) :
    CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1}
      (Ideal.Quotient.factor (hIJ.trans hJK))) =
      CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor hIJ)) ≫
        CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor hJK)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply ULift.ext
  exact (Ideal.Quotient.factor_comp_apply hIJ hJK x.down).symm

/-- The quotient maps satisfy the composition law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Both quotient maps act identically on representatives of the valuation ring;
quotient induction proves their equality. Apply constantSheaf.map_comp.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_comp (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a b c : ℕᵒᵖ) (f : a ⟶ b) (g : b ⟶ c) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E (f ≫ g).unop.le) =
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E f.unop.le) ≫
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E g.unop.le) := by
  have hmap : finiteCoefficientRingMap l E (f ≫ g).unop.le =
      finiteCoefficientRingMap l E f.unop.le ≫ finiteCoefficientRingMap l E g.unop.le := by
    exact uliftQuotientFactorComp
      (I := Padic.coefficientExtensionIdeal l E (a.unop + 1))
      (J := Padic.coefficientExtensionIdeal l E (b.unop + 1))
      (K := Padic.coefficientExtensionIdeal l E (c.unop + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ f.unop.le))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ g.unop.le))
  rw [hmap, CategoryTheory.Functor.map_comp]

/-- The tower of finite constant coefficient sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientTower (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} where
  obj n := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (finiteCoefficientRing l E n.unop)
  map f := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (finiteCoefficientRingMap l E f.unop.le)
  map_id := by
    intro n
    exact finiteCoefficientTower_map_id l X E n
  map_comp := by
    intro a b c f g
    exact finiteCoefficientTower_map_comp l X E a b c f g

/-- The completed finite-level coefficient sheaf.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientLimit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  Limits.limit (finiteCoefficientTower l X E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Restriction of continuous functions as a ring homomorphism.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousMapRestrictionRingHom (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {U V : Scheme.{u}} (f : V ⟶ U) : C(U, T) →+* C(V, T) :=
  { toFun := fun g => ContinuousMap.comp g f.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

/-- Restriction followed by sectionwise localization.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapRestriction (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    Localization.Away (ContinuousMap.const U.unop.left s) →+*
      Localization.Away (ContinuousMap.const V.unop.left s) := by
  have hs : (continuousMapRestrictionRingHom T f.unop.left)
      (ContinuousMap.const U.unop.left s) = ContinuousMap.const V.unop.left s := by
    ext x
    rfl
  letI : IsLocalization.Away
      ((continuousMapRestrictionRingHom T f.unop.left)
        (ContinuousMap.const U.unop.left s))
      (Localization.Away (ContinuousMap.const V.unop.left s)) := hs ▸ inferInstance
  exact IsLocalization.Away.map
    (S := Localization.Away (ContinuousMap.const U.unop.left s))
    (Q := Localization.Away (ContinuousMap.const V.unop.left s))
    (continuousMapRestrictionRingHom T f.unop.left)
    (ContinuousMap.const U.unop.left s)

/-- Restriction-localization maps satisfy the identity law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: The two ring maps agree on every integral numerator by identity precomposition;
the universal property of Localization.Away makes the ring maps equal.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_id (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U : X.ProEtᵒᵖ) :
    localizedContinuousMapRestriction X T s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
    IsLocalization.map_eq, RingHom.comp_apply, RingHom.id_apply]
  rfl

/-- Restriction-localization maps satisfy the composition law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Successive and composite precomposition agree on every numerator. The universal
property of Localization.Away gives equality on fractions, hence on the ring maps.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_comp (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U V W : X.ProEtᵒᵖ) (f : U ⟶ V) (g : V ⟶ W) :
    localizedContinuousMapRestriction X T s (f ≫ g) =
      RingHom.comp (localizedContinuousMapRestriction X T s g)
        (localizedContinuousMapRestriction X T s f) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, localizedContinuousMapRestriction,
    IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- Sectionwise localization of the continuous-function presheaf on a small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapPresheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (Localization.Away
    (ContinuousMap.const U.unop.left s))
  map {U V} f := CommRingCat.ofHom (localizedContinuousMapRestriction X T s f)
  map_id := by
    intro U
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_id X T s U)
  map_comp := by
    intro U V W f g
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_comp X T s U V W f g)

/-- Sheafification of sectionwise localization on the small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousCoefficientSheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (CategoryTheory.presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (localizedContinuousMapPresheaf X T s)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Localization of the integral coefficient sheaf at the chosen uniformizer.
Source: Bhatt--Scholze, Lemma 6.8.2(2) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientLocalization (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact localizedContinuousCoefficientSheaf X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l E))

/-- The continuous-function sheaf for a finite quotient, with its discrete topology.
Source: Bhatt--Scholze, Lemma 4.2.12, discrete-target clause
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientSheaf (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientSheaf X (finiteCoefficientRing l E n)

/-- Evaluation in the continuous-function presentation; `id` only exposes the carrier.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientValue (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (U : X.ProEtᵒᵖ)
    (s : (continuousCoefficientSheaf X T).obj.obj U) (x : U.unop.left) : T :=
  (@id C(U.unop.left, T) s) x

/-- Evaluation of an integral continuous coefficient section in the valuation ring.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) :
    Padic.coefficientExtensionIntegers l E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) U s x).down

/-- Evaluation of a rational continuous coefficient section in the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) : E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X (ULift.{u + 1, u} E) U s x).down

/-- Evaluation of a discrete finite quotient section, in the site's coefficient universe.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : (finiteContinuousCoefficientSheaf l X E n).obj.obj U) (x : U.unop.left) :
    finiteCoefficientRing l E n := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientValue X (finiteCoefficientRing l E n) U s x

/-- The normalization that specifies pullback of continuous functions uniquely, using
its adjunct on each test object. The variable factor of base change is first.
Source: Bhatt--Scholze, Lemma 6.5.8(1), paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientRestrictionNormalized (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (continuousCoefficientSheaf X T) ⟶ continuousCoefficientSheaf Z T) : Prop :=
  ∀ (U : X.ProEt) (s : C(U.left, T))
    (x : ((proEtaleBaseChange h).obj U).left),
    continuousCoefficientValue Z T (Opposite.op ((proEtaleBaseChange h).obj U))
      ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) c).hom.app
        (Opposite.op U) s) x = s ((CategoryTheory.Limits.pullback.fst U.hom h) x)

/-- Pullback normalization for the integral coefficient ring in its valuation topology.
Source: Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h c

/-- Pullback normalization for the rational coefficient ring in its valuation topology.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def rationalCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized (ULift.{u + 1, u} E) h c

/-- The sectionwise normalization of the coefficient inclusion `A → E`.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralRationalCoefficientNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (a : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E) :
    Prop :=
  ∀ (U : X.ProEt) (s : (integralCoefficientSheaf l X E).obj.obj (Opposite.op U))
    (x : U.left), rationalCoefficientValue l E X (Opposite.op U)
      (a.hom.app (Opposite.op U) s) x =
        (integralCoefficientValue l E X (Opposite.op U) s x).val

/-- Normalization of the localization comparison on integral numerators.
A ring map from a localization is determined by these values, so this specifies the
canonical fraction map, including every power of the uniformizer in the denominator.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientLocalizationNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (b : integralCoefficientLocalization l X E ⟶ rationalCoefficientSheaf l X E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact ∀ (U : X.ProEtᵒᵖ)
    (s : C(U.unop.left, ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    (x : U.unop.left),
    rationalCoefficientValue l E X U (b.hom.app U ((CategoryTheory.toSheafify (ProEt.topology X)
      (localizedContinuousMapPresheaf X
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))).app U
          (algebraMap _ (Localization.Away (ContinuousMap.const U.unop.left
            (ULift.up (Padic.coefficientExtensionUniformizer l E)))) s))) x =
      (s x).down.val

end AlgebraicGeometry.Scheme
