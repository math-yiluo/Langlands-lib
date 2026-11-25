/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-!
# Coefficient towers for smooth purity

Source: blueprint main-20261015, chap-Smooth-purity,
`prose-09-21`, paragraphs 1--2
(blueprint: prose-09-21).

## Main definitions

- `spCoefficientRings`: the positive ell-power constant coefficient ring tower.
- `spCoefficientTowers`: module presheaves on the coefficient diagram, sheaves at each level.

The natural number n always denotes the paper's positive level n+1. In the product
category `ℕ × T.ProEt`, presheaf restrictions run from higher levels to lower levels.
Their scalar maps are exactly the quotient maps, so Mathlib's `PresheafOfModules`
encodes the required semilinearity. The full subcategory imposes only the levelwise
sheaf condition. Its morphisms are linear at every (n,U), natural in both variables;
identities and composition are componentwise.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The principal ideal generated by ell in the recorded ring of integers.
Source: blueprint, coefficient convention, paragraph 1
(blueprint: prose-09-21). -/
def spEllIdeal : Ideal (Padic.coefficientExtensionIntegers l E) :=
  Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
    Set (Padic.coefficientExtensionIntegers l E))

/-- The ring sheaf R_(n+1), namely the constant sheaf of O_E/(ell)^(n+1).
The lift places coefficients in a universe containing the small pro-etale site.
Source: blueprint, coefficient convention, paragraph 1
(blueprint: prose-09-21). -/
def spCoefficientRing (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)} :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))))

/-- The reduction q_(n+1): R_(n+2) -> R_(n+1), induced by the identity on O_E.
Source: blueprint, coefficient convention and coefficient-ring tower
(blueprint: prose-09-21). -/
def spCoefficientReduction (n : ℕ) :
    spCoefficientRing l E T (n + 1) ⟶ spCoefficientRing l E T n :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
            ULift.ringEquiv.toRingHom))))

/-- The tower O_(E,T)/ell^bullet with its specified reductions, starting at exponent one.
Source: blueprint, final sentence (blueprint: prose-09-21). -/
def spCoefficientRings :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (spCoefficientReduction l E T)

/-- The actual coefficient presheaf on the product of the level category and the site.
At (n,U) its value is R_(n+1)(U); horizontal maps are quotient reductions and vertical
maps are sheaf restrictions.
Source: blueprint, objects and semilinear transitions, paragraph 2
(blueprint: prose-09-21). -/
def spCoefficientPresheaf : (ℕ × T.ProEt)ᵒᵖ ⥤ RingCat.{max u (t + 1)} :=
  (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
    Functor.uncurry.obj (spCoefficientRings l E T ⋙ sheafToPresheaf _ _)

/-- A coefficient diagram is a tower of sheaves precisely when every vertical slice is
an abelian sheaf. This is the sheaf condition in Mathlib's `SheafOfModules` definition;
there is no condition on surjectivity or on derived scalar extension of transitions.
Source: blueprint, C_n is a sheaf of R_n-modules, paragraph 2
(blueprint: prose-09-21). -/
def spCoefficientTowerSheafCondition :
    ObjectProperty (PresheafOfModules.{max u (t + 1)} (spCoefficientPresheaf l E T)) :=
  fun M ↦ ∀ n : ℕ, Presheaf.IsSheaf (Scheme.ProEt.topology T)
    ((Prod.sectR n T.ProEt).op ⋙ M.presheaf)

/-- Tow(T,O_E). Objects have module-sheaf levels and quotient-semilinear transitions.
Morphisms are the componentwise linear natural maps in `PresheafOfModules`: vertical
naturality gives sheaf maps and horizontal naturality gives s_n phi_(n+1) = phi_n t_n.
The inherited full-subcategory category has componentwise identities and composition.
Source: blueprint, paragraph 2 (blueprint: prose-09-21). -/
abbrev spCoefficientTowers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t}) :=
  (spCoefficientTowerSheafCondition l E T).FullSubcategory

private theorem spEllIdeal_eq_uniformizer_pow :
    ∃ e : ℕ, 1 ≤ e ∧ spEllIdeal l E =
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ e := by
  have hfactor : ∃ e : ℕ, 1 ≤ e ∧
      ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
        (l : Padic.coefficientExtensionIntegers l E) =
          v * Padic.coefficientExtensionUniformizer l E ^ e := by
    let O := Padic.coefficientExtensionIntegers l E
    let π := Padic.coefficientExtensionUniformizer l E
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
    have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
    have hπ : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 (hm.symm.trans hgen.symm)
    have hl0 : (l : O) ≠ 0 := by
      intro heq
      have heq' : (l : E) = 0 := congrArg (fun x : O ↦ (x : E)) heq
      have hq : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
      exact hq ((algebraMap ℚ_[l] E).injective (by simpa only [map_natCast, map_zero]
        using heq'))
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
    refine ⟨e, ?_, v, hv⟩
    have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
      change spectralNorm ℚ_[l] E (l : E) < 1
      simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
    have hnu : ¬ IsUnit (l : O) := by
      intro hu
      exact (ne_of_lt hval) ((h.2.2.1 (l : O)).mp hu)
    by_contra he
    have he0 : e = 0 := by omega
    apply hnu
    rw [hv, he0, pow_zero, mul_one]
    exact v.isUnit
  obtain ⟨e, hepos, v, hv⟩ := hfactor
  refine ⟨e, hepos, ?_⟩
  have hell : spEllIdeal l E =
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ e := by
    unfold spEllIdeal
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow]
  exact hell

/-- The ell-power and chosen uniformizer-power ideals are cofinal.
Source: blueprint, first sentence (blueprint: prose-09-21).

Proof: the DVR description of the ring of integers gives ell = a unit times pi^e
with e positive, since the extending absolute value of ell is strictly less than one.
Thus (ell)^m = (pi)^(em). For the first direction choose m at least n and use e >= 1;
for the second direction choose m = en. Ideal powers are decreasing. The exponent-zero
case is the unit ideal and requires no exception. -/
theorem sp_coefficient_ideals_cofinal :
    (∀ n : ℕ, ∃ m : ℕ, spEllIdeal l E ^ m ≤ Padic.coefficientExtensionIdeal l E n) ∧
    (∀ n : ℕ, ∃ m : ℕ, Padic.coefficientExtensionIdeal l E m ≤ spEllIdeal l E ^ n) := by
  obtain ⟨e, hepos, hell⟩ := spEllIdeal_eq_uniformizer_pow l E
  change Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
    Set (Padic.coefficientExtensionIntegers l E)) = _ at hell
  constructor
  · intro n
    refine ⟨n, ?_⟩
    change Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n ≤
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hell, ← pow_mul]
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n hepos)
  · intro n
    refine ⟨e * n, ?_⟩
    change Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ (e * n) ≤
      Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hell, ← pow_mul]

/-- The constant-scalar quotient into R_(n+1), induced by the quotient of O_E.
This fixes the normalization of the completed-coefficient comparison.
Source: blueprint, reduction a mod ell^(n+1) to a mod ell^n and coefficient convention
(blueprint: prose-09-21). -/
def spCoefficientConstantQuotient (n : ℕ) :
    WeilConjectures.integralConstantRingOfUniverses l E T ⟶ spCoefficientRing l E T n :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))).comp
            ULift.ringEquiv.toRingHom))))

private def spQuotientRings :
    Ideal (Padic.coefficientExtensionIntegers l E) ⥤ CommRingCat.{max u (t + 1)} where
  obj I := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))
  map f := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factor (leOfHom f)).comp ULift.ringEquiv.toRingHom))
  map_id I := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_comp f g := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl

private def spIdealTower
    (I : Ideal (Padic.coefficientExtensionIntegers l E)) :
    ℕᵒᵖ ⥤ Ideal (Padic.coefficientExtensionIntegers l E) where
  obj n := I ^ (n.unop + 1)
  map f := homOfLE (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))

private def spQuotientSheaves :
    Ideal (Padic.coefficientExtensionIntegers l E) ⥤
      Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)} :=
  spQuotientRings.{t, u} l E ⋙ constantSheaf _ _ ⋙ sheafCompose _ (forget₂ CommRingCat _)

private def spEllTowerIso :
    spCoefficientRings l E T ≅ spIdealTower l E (spEllIdeal l E) ⋙
      spQuotientSheaves l E T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    let h : spCoefficientRings l E T ⟶ spIdealTower l E (spEllIdeal l E) ⋙
        spQuotientSheaves l E T :=
      NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp only [spCoefficientRings, Functor.ofOpSequence_map_homOfLE_succ,
          Functor.comp_map, Category.comp_id, Category.id_comp]
        rfl)
    exact h.naturality f)

private def spUniformizerTowerIso :
    WeilConjectures.integralCoefficientSheafSystem l E T ≅
      spIdealTower l E (Ideal.span {Padic.coefficientExtensionUniformizer l E}) ⋙
        spQuotientSheaves l E T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    let h : WeilConjectures.integralCoefficientSheafSystem l E T ⟶
        spIdealTower l E (Ideal.span {Padic.coefficientExtensionUniformizer l E}) ⋙
          spQuotientSheaves l E T :=
      NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp only [WeilConjectures.integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ,
          Functor.comp_map, Category.comp_id, Category.id_comp]
        rfl)
    exact h.naturality f)

private theorem spCompletedLimit_exists :
    ∃ e : WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T ≅
        limit (spCoefficientRings l E T),
      ∀ n : ℕ,
        WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫ e.hom ≫
          limit.π (spCoefficientRings l E T) (op n) =
            spCoefficientConstantQuotient l E T n := by
  obtain ⟨e, he, hell⟩ := spEllIdeal_eq_uniformizer_pow l E
  let a : ℕ → ℕ := fun n ↦ e * (n + 1) - 1
  have ha : Monotone a := by
    intro i j hij
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right hij 1)) 1
  have haFinal : ha.functor.Final := (ha.final_functor_iff).2 (fun n ↦ by
    refine ⟨n, ?_⟩
    dsimp [a]
    have h := Nat.le_mul_of_pos_left (n + 1) he
    omega)
  let K := ha.functor.op
  let : K.Initial := inferInstance
  let J := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
    Set (Padic.coefficientExtensionIntegers l E))
  have hpow (n : ℕᵒᵖ) : J ^ (a n.unop + 1) = spEllIdeal l E ^ (n.unop + 1) := by
    dsimp [a]
    have hpos : 1 ≤ e * (n.unop + 1) :=
      (Nat.succ_le_succ (Nat.zero_le n.unop)).trans
        (Nat.le_mul_of_pos_left (n.unop + 1) he)
    rw [Nat.sub_add_cancel hpos, hell, ← pow_mul]
  let i : K ⋙ spIdealTower l E J ≅ spIdealTower l E (spEllIdeal l E) :=
    NatIso.ofComponents (fun n ↦ eqToIso (hpow n)) (by intros; apply Subsingleton.elim)
  let q := spQuotientSheaves l E T
  let aIso : K ⋙ WeilConjectures.integralCoefficientSheafSystem l E T ≅
      spCoefficientRings l E T :=
    Functor.isoWhiskerLeft K (spUniformizerTowerIso l E T) ≪≫
      (Functor.associator K (spIdealTower l E J) q).symm ≪≫
      Functor.isoWhiskerRight i q ≪≫ (spEllTowerIso l E T).symm
  refine ⟨(Functor.Initial.limitIso K _).symm ≪≫ HasLimit.isoOfNatIso aIso, ?_⟩
  intro n
  change WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫
    (limit.pre (WeilConjectures.integralCoefficientSheafSystem l E T) K ≫
      (HasLimit.isoOfNatIso aIso).hom) ≫ limit.π (spCoefficientRings l E T) (op n) = _
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π,
    limit.pre_π_assoc]
  rw [← Category.assoc]
  change (limit.lift _ (WeilConjectures.integralConstantConeOfUniverses l E T) ≫
    limit.π _ (K.obj (op n))) ≫ aIso.hom.app (op n) = _
  rw [limit.lift_π]
  change WeilConjectures.integralConstantQuotientOfUniverses l E T (a n) ≫
    q.map (eqToHom (hpow (op n))) = spCoefficientConstantQuotient l E T n
  have hscalar (I J : Ideal (Padic.coefficientExtensionIntegers l E)) (h : I = J) :
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)))) ≫
          q.map (eqToHom h) =
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk J).comp ULift.ringEquiv.toRingHom)))) := by
    subst J
    simp [q, spQuotientSheaves, spQuotientRings]
  exact hscalar _ _ (hpow (op n))

/-- The completed coefficient sheaf is also the limit of the ell-power constant sheaves.
It is the existing uniformizer-power completion, whose identification with the pullback
of condensed integers is clause (3) of `sfb_integral_coefficient_limit`.
Source: blueprint, coefficient convention, paragraph 1
(blueprint: prose-09-21).

Proof: `sp_coefficient_ideals_cofinal` gives mutually cofinal positive filtrations.
Their quotient maps, all induced by the identity on the integer ring, induce inverse
maps between the two limits: at each target level choose a deeper source ideal, reduce,
and use compatibility to see independence of the choice. The composites are identities
by the jointly distinguishing limit projections. Apply constant sheafification to all
finite quotient maps. Limits of ring sheaves are computed sectionwise by
`def-pur-sheaf-inverse-limit`, so the same compatible-family argument gives the displayed
ring-sheaf isomorphism. Clause (3) of `lemma-comparison-completed-coefficients--1`
identifies the uniformizer completion with the pulled-back condensed integer ring;
`lemma-comparison-completed-coefficients` supplies the same comparison for finite subextensions.
The comparison agrees with the quotient map on constant scalars at every finite level.
For uniqueness, a ring-sheaf map into R_(n+1) kills ell^(n+1); reduction of the completed
integer sheaf modulo this power is the finite constant sheaf, so this normalization fixes
every projection. No choice of uniformizer affects the comparison: all maps are reductions. -/
theorem sp_completed_coefficient_limit :
    ∃! e : WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T ≅
        limit (spCoefficientRings l E T),
      ∀ n : ℕ,
        WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫ e.hom ≫
          limit.π (spCoefficientRings l E T) (op n) =
            spCoefficientConstantQuotient l E T n := by
  obtain ⟨e, he⟩ := spCompletedLimit_exists l E T
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply limit.hom_ext
  intro n
  rcases n with ⟨n⟩
  obtain ⟨k, hk⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  have hI : ∃ k : ℕ, Padic.coefficientExtensionIdeal l E (k + 1) ≤
      spEllIdeal l E ^ (n + 1) := by
    refine ⟨k, le_trans ?_ hk⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ k)
  exact completedIntegralFiniteQuotientHom_ext l E T
    (spEllIdeal l E ^ (n + 1)) hI
    (d.hom ≫ limit.π _ (op n)) (e.hom ≫ limit.π _ (op n))
    (by simpa only [Category.assoc, spCoefficientConstantQuotient, Functor.comp_map] using hd n)
    (by simpa only [Category.assoc, spCoefficientConstantQuotient, Functor.comp_map] using he n)

end AlgebraicGeometry.ProEtale
