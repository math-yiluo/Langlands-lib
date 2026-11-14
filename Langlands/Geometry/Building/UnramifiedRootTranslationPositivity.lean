import Langlands.Geometry.Building.RootFunctionTranslationPositivity
import Langlands.Geometry.Building.UnramifiedValuationDescentReduction

/-! # Strict root positivity along descended apartment translations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {jT : T.toGrp ⟶ G}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT

private instance positivityExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance positivityExtendedSmooth [Smooth G.X.hom] : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) ω)
  (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)

namespace KPApartmentData

/-- The actual upper apartment point obtained by pushing forward a lower
torus vector. -/
def descentTranslate (x : D.Apartment) (v : V S) : D.Apartment :=
  ⟨descentCocharacterMap k K f hS v +ᵥ x.val, D.vadd_mem x.mem _⟩

@[simp] theorem descentTranslate_val (x : D.Apartment) (v : V S) :
    (D.descentTranslate f hS x v).val =
      descentCocharacterMap k K f hS v +ᵥ x.val := rfl

/-- Every descended translation of a coefficient-fixed point remains
coefficient-fixed. -/
theorem galois_fixed_descentTranslate (x : D.Apartment)
    (hx : ∀ σ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G σ x.val = x.val)
    (v : V S) (σ : K ≃ₐ[k] K) :
    RootFunctionFamily.galoisAction k K T G σ
        (D.descentTranslate f hS x v).val =
      (D.descentTranslate f hS x v).val := by
  simp only [descentTranslate_val, RootFunctionFamily.galoisAction_vadd,
    galoisCocharacterAction_descentCocharacterMap, hx σ]

variable [Smooth G.X.hom]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  (hE : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT))

/-- Nonnegativity near zero along actual descended translation lines in
the supplied upper apartment, evaluated by torus-then-field restriction. -/
def NonnegativeNearDescentTranslations (x : D.Apartment)
    (a : characterLattice S) (g : rationalPoints G) : Prop :=
  ∀ v : V S, ∀ᶠ t : ℝ in 𝓝 0,
    0 ≤ torusFieldRestrictedRootFunctionFamily (k := k) (K := K)
      hS hT hE (D.isRootDatumValuation_of_mem
        (D.descentTranslate f hS x (t • v)).mem)
      ((CommGroupScheme.baseChange b).map f) a g

/-- The restriction of the translated upper point is the translation of
the original restricted family. -/
theorem restricted_descentTranslate (x : D.Apartment) (v : V S) :
    torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE
        (D.isRootDatumValuation_of_mem (D.descentTranslate f hS x v).mem)
        ((CommGroupScheme.baseChange b).map f) =
      v +ᵥ torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE
        (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange b).map f) :=
  torusFieldRestricted_eq_vadd_of_eq_descent_vadd hS hT hE x.isValuation
    (D.descentTranslate f hS x v).isValuation v rfl

/-- Strict positivity of the actual restricted root family is equivalent
to the neighbourhood condition in the original upper apartment.
No valuation axiom on the restricted family is needed. -/
theorem strictPositive_iff_nonnegativeNearDescentTranslations
    (x : D.Apartment) {a : characterLattice S} (ha : a ≠ 0)
    (g : rationalPoints G) :
    0 < torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE
        (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange b).map f) a g ↔
      D.NonnegativeNearDescentTranslations f hS hT hE x a g := by
  rw [RootFunctionFamily.strictPositive_iff_nonnegativeNearTranslations hS _ ha g]
  simp only [RootFunctionFamily.NonnegativeNearTranslations,
    NonnegativeNearDescentTranslations,
    D.restricted_descentTranslate f hS hT hE]

/-- A value-zero element fails the nonnegativity condition along the actual
descended translation lines. -/
theorem not_nonnegativeNearDescentTranslations_of_eq_zero
    (x : D.Apartment) {a : characterLattice S} (ha : a ≠ 0)
    (g : rationalPoints G)
    (hzero : torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange b).map f) a g = 0) :
    ¬ D.NonnegativeNearDescentTranslations f hS hT hE x a g := by
  rw [← D.strictPositive_iff_nonnegativeNearDescentTranslations f hS hT hE x ha g,
    hzero]
  exact lt_irrefl _

end KPApartmentData

end Langlands.Geometry.Building
