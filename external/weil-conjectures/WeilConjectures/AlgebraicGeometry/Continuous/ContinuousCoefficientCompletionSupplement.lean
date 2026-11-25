/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletion

/-! # Completion of continuous integral coefficients -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal

private theorem continuousCoefficientConstantComparison_unit (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T)) ≫
      (continuousCoefficientConstantComparison X T).hom = continuousCoefficientConstants X T :=
  Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv _ _) _

/-- The residue coefficient rings before taking constant sheaves. -/
noncomputable def finiteCoefficientRingTower (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := finiteCoefficientRing l E n.unop
  map f := finiteCoefficientRingMap l E f.unop.le
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl

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

private theorem coefficientIntegersTopology_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    let := coefficientExtensionNormedField l E
    (inferInstance : TopologicalSpace (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionIntegersTopology l E := by
  have hm : (coefficientExtensionNormedField l E).toPseudoMetricSpace =
      (spectralNorm.normedField ℚ_[l] E).toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      apply Dist.ext
      funext x y
      change spectralNorm ℚ_[l] E (-x + y) = spectralNorm ℚ_[l] E (x - y)
      rw [show -x + y = -(x - y) by abel, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  exact congrArg (fun m : PseudoMetricSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E))
      m.toUniformSpace.toTopologicalSpace) hm

/-- Reduction to each finite quotient is continuous for the valuation topology. -/
theorem continuousCoefficientReduction_continuous (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    let := coefficientExtensionNormedField l E
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    @Continuous (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
      (finiteCoefficientRing l E n) inferInstance ⊥ (fun x ↦
      (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x.down) :
        finiteCoefficientRing l E n)) := by
  let := coefficientExtensionNormedField l E
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  obtain ⟨⟨e, he, htop⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  have hcoord : @Continuous _ _ (Padic.coefficientExtensionIntegersTopology l E) ⊥
      (fun x ↦ (e x).val n) := by
    let : TopologicalSpace (Padic.coefficientExtensionIntegers l E) :=
      Padic.coefficientExtensionIntegersTopology l E
    let : ∀ k : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (k + 1)) :=
      fun _ ↦ ⊥
    let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) :=
      Padic.coefficientExtensionPositiveLimitTopology l E
    exact (continuous_apply n).comp (continuous_induced_dom.comp htop.continuous)
  simp_rw [he] at hcoord
  rw [← coefficientIntegersTopology_eq l E] at hcoord
  have hc : @Continuous _ _ (inferInstance : TopologicalSpace
      (Padic.coefficientExtensionIntegers l E)) ⊥
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := hcoord
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  apply continuous_def.mpr
  intro V _
  exact (hc.comp continuous_uliftDown).isOpen_preimage
    (ULift.up ⁻¹' V) (isOpen_discrete _)

/-- The residue reduction of continuous coefficient sheaves. -/
noncomputable def continuousCoefficientReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    integralCoefficientSheaf l X E ⟶ finiteContinuousCoefficientSheaf l X E n := by
  letI := coefficientExtensionNormedField l E
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  let φ : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      finiteCoefficientRing l E n :=
    { toFun := fun x ↦ ULift.up
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x.down)
      map_one' := by apply ULift.ext; exact map_one _
      map_mul' := by intro x y; apply ULift.ext; exact map_mul _ _ _
      map_zero' := by apply ULift.ext; exact map_zero _
      map_add' := by intro x y; apply ULift.ext; exact map_add _ _ _ }
  exact @continuousCoefficientMap _ _ _ _ _ ⊥ _ _ φ
    (continuousCoefficientReduction_continuous l E n) X

/-- The cone of pointwise continuous reductions. -/
noncomputable def continuousCoefficientResidueCone (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) : CategoryTheory.Limits.Cone
      (finiteCoefficientRingTower l E ⋙ discreteContinuousCoefficientFunctor X) where
  pt := integralCoefficientSheaf l X E
  π :=
    { app := fun n ↦ continuousCoefficientReduction l E X n.unop
      naturality := by
        let := coefficientExtensionNormedField l E
        intro n m f
        let : TopologicalSpace ((finiteCoefficientRingTower l E).obj m) := ⊥
        let : DiscreteTopology ((finiteCoefficientRingTower l E).obj m) := ⟨rfl⟩
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro s
        change C(U.unop.left, ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) at s
        apply ContinuousMap.ext
        intro x
        rfl }

/-- Pointwise lifting of compatible residues makes the continuous residue cone limiting.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-continuous-coefficient-completion). -/
theorem continuousCoefficientResidueCone_isLimit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) : Nonempty (CategoryTheory.Limits.IsLimit
      (continuousCoefficientResidueCone l E X)) := by
  classical
  let := coefficientExtensionNormedField l E
  let : ∀ n : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
    fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    fun _ ↦ ⟨rfl⟩
  let : ∀ n : ℕ, TopologicalSpace (finiteCoefficientRing l E n) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (finiteCoefficientRing l E n) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) :=
    Padic.coefficientExtensionPositiveLimitTopology l E
  obtain ⟨⟨e, he, htop⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  have hec : Continuous e := by
    have hc := @IsHomeomorph.continuous _ _
      (Padic.coefficientExtensionIntegersTopology l E)
      (Padic.coefficientExtensionPositiveLimitTopology l E) _ htop
    rw [← coefficientIntegersTopology_eq l E] at hc
    exact hc
  have heci : Continuous e.symm := by
    have hc : @Continuous _ _ (Padic.coefficientExtensionPositiveLimitTopology l E)
        (Padic.coefficientExtensionIntegersTopology l E) e.symm := by
      let : TopologicalSpace (Padic.coefficientExtensionIntegers l E) :=
        Padic.coefficientExtensionIntegersTopology l E
      exact (e.toEquiv.toHomeomorphOfContinuousOpen htop.continuous
        htop.isOpenMap).symm.continuous
    rw [← coefficientIntegersTopology_eq l E] at hc
    exact hc
  apply Nonempty.intro
  apply CategoryTheory.Limits.isLimitOfReflects
    (sheafToPresheaf (ProEt.topology X) CommRingCat.{u + 1})
  apply CategoryTheory.Limits.evaluationJointlyReflectsLimits
  intro U
  apply Classical.choice
  apply commRingForgetReflectsLimit
  apply Classical.choice
  apply (CategoryTheory.Limits.Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    have hn := congrArg (fun s ↦ ((s.val (Opposite.op n) :
      C(U.unop.left, finiteCoefficientRing l E n)) x).down) hfg
    exact hn
  · intro s
    let t (n : ℕ) : C(U.unop.left, finiteCoefficientRing l E n) := s.val (Opposite.op n)
    let b (x : U.unop.left) : Padic.coefficientExtensionPositiveLimit l E :=
      ⟨fun n ↦ (t n x).down, by
        apply Subring.mem_iInf.mpr
        intro n
        have hn := s.property (CategoryTheory.homOfLE (Nat.le_succ n)).op
        exact congrArg (fun f : C(U.unop.left, finiteCoefficientRing l E n) ↦
          (f x).down) hn⟩
    have hb : Continuous b := by
      apply continuous_induced_rng.mpr
      apply continuous_pi
      intro n
      have hd : @Continuous (finiteCoefficientRing l E n)
          (Padic.coefficientExtensionRing l E (n + 1)) ⊥ ⊥ ULift.down :=
        continuous_of_discreteTopology
      exact hd.comp (t n).continuous
    let f : C(U.unop.left, ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :=
      ⟨fun x ↦ ULift.up (e.symm (b x)), continuous_uliftUp.comp (heci.comp hb)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    funext n
    apply @ContinuousMap.ext U.unop.left (finiteCoefficientRing l E n.unop) _ ⊥
    intro x
    apply ULift.ext
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))
      (e.symm (b x)) = _
    rw [← he]
    exact congrArg (fun t : Padic.coefficientExtensionPositiveLimit l E ↦ t.val n.unop)
      (e.apply_symm_apply (b x))

/-- Continuous integral coefficients are the limit of the positive constant residue tower,
with constants fixed and projections given by pointwise reduction.

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1)
(blueprint: lem-weil-pbc-continuous-coefficient-completion).

Proof: For a discrete finite quotient, the constant presheaf maps to continuous functions
by constant functions. Its map is locally surjective on the open fibres of each function,
and locally injective because equality of constants can be checked on any nonempty
object. The empty object has the unique section forced by the empty cover. These fibre
covers are pro-etale coverings: open immersions are weakly etale, and on each affine
open quasi-compactness supplies a finite affine refinement. Hence sheafification gives
the unique constant-preserving ring isomorphism, naturally in quotient maps.
The profinite-tower theorem for the valuation ring identifies it, topologically and as
a ring, with compatible residues. Composition with this homeomorphism identifies
continuous functions on any test scheme with compatible continuous residue functions.
The inverse is continuous because congruence cosets form a neighbourhood basis; their
inverse images are the open fibres of the coordinates. All ring operations and all
restriction maps agree pointwise. Ring-sheaf limits are computed sectionwise, so these
maps give the stated isomorphism and the displayed projection normalization. -/
theorem continuousCoefficientCompletion (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    ∃ i : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E,
      (∀ n : ℕ, ∃ q : (CategoryTheory.constantSheaf (ProEt.topology X)
          CommRingCat.{u + 1}).obj (finiteCoefficientRing l E n) ≅
          finiteContinuousCoefficientSheaf l X E n,
        (∀ (U : X.ProEtᵒᵖ) (a : finiteCoefficientRing l E n) (x : U.unop.left),
          finiteContinuousCoefficientValue l E X n U
            (q.hom.hom.app U ((CategoryTheory.toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app U a)) x = a) ∧
        (∀ (U : X.ProEtᵒᵖ)
          (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
          (finiteContinuousCoefficientValue l E X n U
            ((i.hom ≫ CategoryTheory.Limits.limit.π (finiteCoefficientTower l X E)
              (Opposite.op n) ≫ q.hom).hom.app U s) x).down =
                Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
                  (integralCoefficientValue l E X U s x))) := by
  classical
  let := coefficientExtensionNormedField l E
  let e := Functor.isoWhiskerLeft (finiteCoefficientRingTower l E)
    (discreteContinuousCoefficientIso X)
  let hc := Classical.choice (continuousCoefficientResidueCone_isLimit l E X)
  let i := hc.conePointsIsoOfNatIso
    (CategoryTheory.Limits.limit.isLimit (finiteCoefficientTower l X E)) e.symm
  refine ⟨i, ?_⟩
  intro n
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  let q := (discreteContinuousCoefficientIso X).app (finiteCoefficientRing l E n)
  refine ⟨q, ?_, ?_⟩
  · intro U a x
    have h := congrArg (fun f ↦ f.app U a)
      (continuousCoefficientConstantComparison_unit X (finiteCoefficientRing l E n))
    exact congrArg (fun s : C(U.unop.left, finiteCoefficientRing l E n) ↦ s x) h
  · have hi : i.hom ≫ CategoryTheory.Limits.limit.π (finiteCoefficientTower l X E)
        (Opposite.op n) ≫ q.hom = continuousCoefficientReduction l E X n := by
      have h := hc.conePointsIsoOfNatIso_hom_comp
        (CategoryTheory.Limits.limit.isLimit (finiteCoefficientTower l X E)) e.symm
        (Opposite.op n)
      change i.hom ≫ _ = _ ≫ q.inv at h
      change i.hom ≫ CategoryTheory.Limits.limit.π (finiteCoefficientTower l X E)
        (Opposite.op n) = continuousCoefficientReduction l E X n ≫ q.inv at h
      calc
        _ = (i.hom ≫ CategoryTheory.Limits.limit.π (finiteCoefficientTower l X E)
            (Opposite.op n)) ≫ q.hom := (Category.assoc _ _ _).symm
        _ = (continuousCoefficientReduction l E X n ≫ q.inv) ≫ q.hom :=
          congrArg (fun f ↦ f ≫ q.hom) h
        _ = continuousCoefficientReduction l E X n ≫ 𝟙
            ((discreteContinuousCoefficientFunctor X).obj (finiteCoefficientRing l E n)) :=
          by rw [Category.assoc, q.inv_hom_id]
        _ = _ := Category.comp_id _
    intro U s x
    rw [hi]
    rfl

end AlgebraicGeometry.Scheme
