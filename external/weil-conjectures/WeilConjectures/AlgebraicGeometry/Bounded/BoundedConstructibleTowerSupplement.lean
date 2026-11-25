/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower

/-!
# Uniformly bounded constructible adic towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-bounded-constructible-tower, order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower).

Positive level n+1 is indexed by n : ℕ. Normalizations are stored for every comparable
pair; their cocycle determines the nonconsecutive ones from the consecutive ones.
Compatibility is expressed on their adjoints M_b→Res(M_a). The tensor-unit normalized
scalar-extension adjunction makes this equivalent to the displayed normalization
identities in the blueprint. This permits restrictions to retain their actual
inverse-image coefficients, without choosing a tensor/pullback comparison.

## Main definitions

* `AdicTower`: a derived strict tower with quotient-linear normalized levels.
* `AdicTowerLocalModel`: one bounded local complex and its compatible reductions.
* `IsUniformlyBoundedConstructibleAdicTower`: common bounds, finite strata and local models.
* `pbcLevelConstantComparison` and `pbcCompletedComparison`: canonical coefficient
  presentation comparisons fixed on constant sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDerivedAdjunction
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ G : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (s : K ⟶ G),
      P K ∧ QuasiIso s)
    (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLD : LD.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)))
    (hε : ∀ K : CochainComplex A ℤ, P K →
      IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    ∃! d : LD ⊣ R.mapDerivedCategory,
      ∀ K : CochainComplex A ℤ, P K →
        d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map
            (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) := by
  have hr (X : HomotopyCategory A (.up ℤ)) :
      ∃ (K : HomotopyCategory A (.up ℤ)) (s : K ⟶ X),
        IsIso (ε.app K) ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ := hres G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, hε K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    L R adj LD ε hLD hr
  have hn (K : CochainComplex A ℤ) :
        d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map
            (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) := by
    have hp := hd ((HomotopyCategory.quotient _ _).obj K)
    change d.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj K)) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj K)) = _ at hp
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
      Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
    simp only [Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at hp ⊢
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id, Category.comp_id] at hp
    have hp' := congrArg (fun f ↦ f ≫ (DerivedCategory.quotientCompQhIso A).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K))) hp
    simp only [Category.assoc, Iso.inv_hom_id_app] at hp'
    erw [Category.comp_id] at hp'
    erw [DerivedCategory.quotientCompQhIso_hom_naturality] at hp'
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
    simp only [Functor.map_comp, Category.assoc]
    have hunit := d.unit.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
    simp only [Functor.id_map, Functor.comp_map] at hunit
    rw [reassoc_of% hunit, ← R.mapDerivedCategory.map_comp_assoc, ← LD.map_comp,
      Iso.hom_inv_id_app]
    erw [LD.map_id, R.mapDerivedCategory.map_id, Category.id_comp]
    exact hp'
  refine ⟨d, fun K _ ↦ hn K, ?_⟩
  intro d' hd'
  have hu (K : CochainComplex A ℤ) (hK : P K) :
      d'.unit.app (DerivedCategory.Q.obj K) = d.unit.app (DerivedCategory.Q.obj K) := by
    have : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj K)) := hε K hK
    apply (cancel_mono (R.mapDerivedCategory.map
      (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
        DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
    simpa only [Category.assoc] using (hd' K hK).trans (hn K).symm
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  obtain ⟨K', s, hK', hs⟩ := hres K
  have : QuasiIso s := hs
  apply (cancel_epi (DerivedCategory.Q.map s)).mp
  change (𝟭 _).map (DerivedCategory.Q.map s) ≫ _ =
    (𝟭 _).map (DerivedCategory.Q.map s) ≫ _
  rw [d'.unit.naturality, d.unit.naturality]
  dsimp only [Functor.comp_map, Functor.id_map]
  rw [hu K' hK']

variable (X : Scheme.{u})

/-- Exact termwise evaluation in the derived tower category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcTowerEvaluation (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :=
  ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).obj (op n)).mapDerivedCategory

variable {X} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

variable {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

include h in
/-- Composition of exact derived scalar restrictions, with its canonical section maps.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedRestrictComp : pbcDerivedRestrict ψ ⋙ pbcDerivedRestrict φ ≅
    pbcDerivedRestrict χ :=
  Functor.mapDerivedCategoryCompIso (pbcRestrict ψ) (pbcRestrict φ) ≪≫
    Functor.mapDerivedCategoryNatIso (pbcRestrictComp φ ψ χ h)

/-- The reduction transition is the adjunct of the direct scalar-extension unit.
This formula is the derived version of b⊗x↦ψ(b)⊗x.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionTransition (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend φ).obj K ⟶
      (pbcDerivedRestrict ψ).obj ((pbcDerivedExtend χ).obj K) :=
  ((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
    ((pbcDerivedScalarAdjunction χ).unit.app K ≫
      (pbcDerivedRestrictComp φ ψ χ h).inv.app ((pbcDerivedExtend χ).obj K))

/-- Its adjunct along ψ is the canonical quotient-reduction normalization map.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionNormalizationHom (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).obj ((pbcDerivedExtend φ).obj K) ⟶
      (pbcDerivedExtend χ).obj K :=
  ((pbcDerivedScalarAdjunction ψ).homEquiv _ _).symm
    (pbcReductionTransition φ ψ χ h K)

/-- Derived balancing is invertible, without flatness of either coefficient map.
Source: blueprint order 1239; Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: resolve K by a K-flat P. Scalar extension Eφ(P) is K-flat over S, since tensoring
it with an acyclic B-complex is P tensored with that complex after restriction. Thus
both derived sides are computed by Eψ(Eφ(P)) and Eχ(P). The displayed adjunct is the
ordinary balancing map s⊗(r⊗x)↦sψ(r)⊗x, by the fixed tensor units. Its inverse sends
s⊗x to s⊗(1⊗x). The balancing relations prove the inverse identities. Local tensor
generation and sheafification give inverse chain maps, hence an isomorphism on localization. -/
theorem pbcReductionNormalization_isIso (K : DerivedCategory (pbcModules X R)) :
    IsIso (pbcReductionNormalizationHom φ ψ χ h K) := by
  let e := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
    (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
    (pbcDerivedRestrictComp φ ψ χ h)
  have he : pbcReductionNormalizationHom φ ψ χ h K = e.hom.app K := by
    dsimp [pbcReductionNormalizationHom, pbcReductionTransition, e]
    simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc]
  rw [he]
  infer_instance

/-- Canonical normalization, retaining its balancing and unit characterization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcReductionNormalization (K : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).obj ((pbcDerivedExtend φ).obj K) ≅
      (pbcDerivedExtend χ).obj K :=
  letI := pbcReductionNormalization_isIso φ ψ χ h K
  asIso (pbcReductionNormalizationHom φ ψ χ h K)

/-- All quotient maps in the coefficient diagram, including equal indices.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcAdicQuotient (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (b a : ℕ) (hab : a ≤ b) :=
  (pbcAdicRings X d).map (homOfLE hab).op

set_option linter.defProp false in
/-- Projection followed by quotient reduction is the lower projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: apply the naturality equation of the limit cone to the arrow b→a. -/
theorem pbcAdicProjection_comp (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (hab : a ≤ b) :
    pbcAdicProjection X d b ≫ pbcAdicQuotient X d b a hab = pbcAdicProjection X d a := by
  exact limit.w (pbcAdicRings X d) (homOfLE hab).op

set_option linter.defProp false in
/-- Quotient maps satisfy the full quotient cocycle.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the coefficient diagram preserves composition, and the opposite poset has a unique
arrow between its comparable endpoints. This includes every equal-index case. -/
theorem pbcAdicQuotient_comp (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    pbcAdicQuotient X d c b hbc ≫ pbcAdicQuotient X d b a hab =
      pbcAdicQuotient X d c a (hab.trans hbc) := by
  exact ((pbcAdicRings X d).map_comp (homOfLE hbc).op (homOfLE hab).op).symm

/-- The natural derived transition between any two evaluations of a strict tower.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcTowerTransition (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (b a : ℕ) (hab : a ≤ b) :
    pbcTowerEvaluation X R b ⟶ pbcTowerEvaluation X R a :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcTowers X R) (.up ℤ)) _ _
    (pbcTowerEvaluation X R b) (pbcTowerEvaluation X R a)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).map (homOfLE hab).op) (.up ℤ))
        DerivedCategory.Q)

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- A normalization's semilinear transition, obtained by its canonical scalar-extension
unit and restriction of its R_a-linear isomorphism.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerSemilinearTransition
    (M : ∀ n : ℕ, DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (ρ : ∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).obj (M b) ≅ M a)
    (b a : ℕ) (hab : a ≤ b) :
    M b ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d b a hab)).obj (M a) :=
  (pbcDerivedScalarAdjunction (pbcAdicQuotient X d b a hab)).unit.app (M b) ≫
    (pbcDerivedRestrict (pbcAdicQuotient X d b a hab)).map (ρ b a hab).hom

/-- An object of D(Tow_A(X)), quotient-linear levels identified with its evaluations,
and normalized derived reductions compatible with its actual transitions. The cocycle
is written on the semilinear adjuncts; the canonical restriction comparison identifies
the two successive scalar restrictions with direct restriction. Invertible normalization
and the equal-index cocycle also force the usual identity normalization.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
structure AdicTower where
  /-- The derived object of strict completed-coefficient towers. -/
  tower : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))
  /-- Each level retains its quotient-ring action. -/
  level : ∀ n : ℕ, DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))
  /-- The scalar restriction is the actual derived evaluation. -/
  evaluation : ∀ n : ℕ,
    (pbcDerivedRestrict (pbcAdicProjection X d n)).obj (level n) ≅
      (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj tower
  /-- Normalization at all pairs, including the consecutive normalizations of the source. -/
  normalization : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).obj (level b) ≅ level a
  /-- The restricted scalar-extension/normalization composite is the tower transition. -/
  transition : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedRestrict (pbcAdicProjection X d b)).map
        (adicTowerSemilinearTransition X d level normalization b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection X d b)
        (pbcAdicQuotient X d b a hab) (pbcAdicProjection X d a)
        (pbcAdicProjection_comp X d b a hab)).hom.app (level a) ≫
      (evaluation a).hom =
    (evaluation b).hom ≫
      (pbcTowerTransition X (pbcAdicCompletion X d) b a hab).app tower
  /-- Direct reduction agrees with reduction through every intermediate level. -/
  cocycle : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
    adicTowerSemilinearTransition X d level normalization c a (hab.trans hbc) =
      adicTowerSemilinearTransition X d level normalization c b hbc ≫
        (pbcDerivedRestrict (pbcAdicQuotient X d c b hbc)).map
          (adicTowerSemilinearTransition X d level normalization b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicQuotient X d c b hbc)
          (pbcAdicQuotient X d b a hab)
          (pbcAdicQuotient X d c a (hab.trans hbc))
          (pbcAdicQuotient_comp X d c b a hab hbc)).hom.app (level a)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The local reduction of a common completed-coefficient complex, retaining the
inverse image of the completed ring rather than completing again after restriction.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerLocalReduction
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ) (n : ℕ) :=
  (pbcDerivedExtend ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
    (DerivedCategory.Q.obj L)

/-- The canonical semilinear transition of the local reduction model. It is the adjunct
of the balancing normalization N_b⊗ᴸR_a≅N_a, as specified by the coefficient datum.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerLocalTransition
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (b a : ℕ) (hab : a ≤ b) :
    adicTowerLocalReduction d g L b ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d b a hab))).obj (adicTowerLocalReduction d g L a) :=
  pbcReductionTransition
    ((adicTowerInverseImage g).map (pbcAdicProjection X d b))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d b a hab))
    ((adicTowerInverseImage g).map (pbcAdicProjection X d a))
    (((adicTowerInverseImage g).map_comp _ _).symm.trans
      (congrArg (adicTowerInverseImage g).map (pbcAdicProjection_comp X d b a hab)))
    (DerivedCategory.Q.obj L)

/-- Restriction of semilinear transitions, using the existing canonical comparison for
exact inverse image and scalar restriction. It is the mate of identity on sections,
so no arbitrary map or coefficient identification occurs.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def adicTowerRestrictedTransition (M : AdicTower X d) (b a : ℕ) (hab : a ≤ b) :
    (adicTowerPullback g ((pbcAdicRings X d).obj (op b))).obj (M.level b) ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d b a hab))).obj
          ((adicTowerPullback g ((pbcAdicRings X d).obj (op a))).obj (M.level a)) :=
  (adicTowerPullback g ((pbcAdicRings X d).obj (op b))).map
      (adicTowerSemilinearTransition X d M.level M.normalization b a hab) ≫
    (proEtaleRingRestrictionDerivedPullback g
      ((pbcAdicRings X d).obj (op b)) ((pbcAdicRings X d).obj (op a))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op b)))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op a)))
      (pbcAdicQuotient X d b a hab)
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d b a hab))
      (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app (M.level a)

/-- A common local bounded model with adic-lisse finite-type terms, finite-lisse
cohomology in every finite reduction, and compatible quotient-linear identifications.
The compatibility equation is the adjoint form of e_aρ=σ(Le_b); scalar-extension Hom
bijections make it equivalent to the blueprint's equation.
Source: blueprint order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
structure AdicTowerLocalModel (M : AdicTower X d) (d₀ d₁ : ℤ) where
  /-- One complex over the restricted completed coefficients, independent of the level. -/
  complex : CochainComplex (pbcModules Y
    ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ
  /-- A uniform termwise window, rather than just cohomological bounds. -/
  bounded : ∀ q : ℤ, (q < d₀ ∨ d₁ < q) → IsZero (complex.X q)
  /-- Terms are completed adic-lisse modules of finite type, without a finite-set condition. -/
  adicLisse : ∀ q : ℤ,
    @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcCompletedComparison X d).hom)).obj (complex.X q))
  /-- Every cohomology sheaf at every finite level is locally a finite constant module. -/
  finiteLisse : ∀ (n : ℕ) (q : ℤ),
    IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj (adicTowerLocalReduction d g complex n)))
  /-- The level identifications are linear over the inverse-image finite coefficient ring. -/
  identification : ∀ n : ℕ,
    (adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n) ≅
      adicTowerLocalReduction d g complex n
  /-- Every reduction agrees with the normalization of the same common local model. -/
  compatible : ∀ (b a : ℕ) (hab : a ≤ b),
    adicTowerRestrictedTransition d g M b a hab ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d b a hab))).map (identification a).hom =
      (identification b).hom ≫ adicTowerLocalTransition d g complex b a hab

/-- Uniformly bounded constructibility means one window and one finite locally closed
stratification, with a pro-etale cover on each stratum carrying common local models.
The coefficient restrictions are along the composite of the stratum immersion and the
covering morphism. The finite-lisse cohomology covers can depend on both level and degree.
Source: blueprint order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
def IsUniformlyBoundedConstructibleAdicTower (M : AdicTower X d) : Prop :=
  ∃ (d₀ d₁ : ℤ), d₀ ≤ d₁ ∧ ∃ S : Stratification X,
    ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
      V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
      ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) M d₀ d₁)

end AlgebraicGeometry.Scheme
