import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedNaturalityReduction

/-! # Construction and uniqueness through an actual cocenter -/

noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- Injectivity of a single cocenter target map gives uniqueness from its square. -/
theorem eq_of_cocenterKottwitzLawAt (c : Cocenter k G)
    (hc : Function.Injective (cocenterTargetMap F k G hG c))
    {κ κ₁ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : CocenterKottwitzLawAt F k G hG c κ)
    (hκ₁ : CocenterKottwitzLawAt F k G hG c κ₁) :
    κ = κ₁ := by
  apply MonoidHom.ext
  intro x
  apply Multiplicative.toAdd.injective
  apply hc
  exact (hκ x).trans (hκ₁ x).symm

/-- The cocenter construction using the inverse of its bijective target map. -/
def cocenterKottwitzCandidate (c : Cocenter k G)
    (hc : Function.Bijective (cocenterTargetMap F k G hG c)) :
    reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG) :=
  let e := LinearEquiv.ofBijective (cocenterTargetMap F k G hG c) hc
  let q := G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F))
  e.symm.toLinearMap.toAddMonoidHom.toMultiplicative.comp
    ((torusKottwitz F k c.torus c.isTorus).comp q)

/-- The inverse-map construction satisfies the actual cocenter square. -/
theorem cocenterKottwitzCandidate_law (c : Cocenter k G)
    (hc : Function.Bijective (cocenterTargetMap F k G hG c)) :
    CocenterKottwitzLawAt F k G hG c (cocenterKottwitzCandidate F k G hG c hc) := by
  intro x
  exact (LinearEquiv.ofBijective (cocenterTargetMap F k G hG c) hc).apply_symm_apply _

/-- Inverting a bijective target map constructs a homomorphism satisfying one square. -/
theorem exists_cocenterKottwitzLawAt (c : Cocenter k G)
    (hc : Function.Bijective (cocenterTargetMap F k G hG c)) :
    ∃ κ, CocenterKottwitzLawAt F k G hG c κ :=
  ⟨cocenterKottwitzCandidate F k G hG c hc,
    cocenterKottwitzCandidate_law F k G hG c hc⟩

variable
  (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
  (hfund : AlgebraicFundamentalGroupMapStatement.{u})
  (htorus : TorusFundamentalComparisonStatement.{u})
  (hmap : FundamentalInertiaMapStatement.{u})
  (hinertia : TorusInertiaComparisonStatement.{u})
  [IsSepClosure k (SeparableClosure F)]

include hcmp hfund htorus hmap hinertia

/-- Naturality for the actual map between two cocenters transports their squares. -/
theorem cocenterKottwitzLawAt_of_torus_naturality
    (c d : Cocenter k G)
    (hnat : ∀ x : torusKPoints F k c.torus,
      (torusKottwitz F k d.torus d.isTorus
        (affinePointsTarget c.torus.toGrp
          (CommGroupScheme.groupHom (c.map d hG (𝟙 G)))
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      torusInertiaMap k (SeparableClosure F) (c.map d hG (𝟙 G))
        (UnramifiedClosure F) (torusKottwitz F k c.torus c.isTorus x).toAdd)
    {κ : reductiveKPoints F k G →* Multiplicative (ReductiveTarget F k G hG)}
    (hκ : CocenterKottwitzLawAt F k G hG c κ) :
    CocenterKottwitzLawAt F k G hG d κ := by
  intro x
  have ht := cocenterTargetMap_natural_of_statements
    hcmp hfund htorus hmap hinertia F k G G hG hG c d (𝟙 G) (κ x).toAdd
  rw [(hmap k (UnramifiedClosure F) (SeparableClosure F)).2.1 G hG,
    LinearMap.id_apply] at ht
  rw [ht, hκ, ← hnat]
  congr 2
  change (x ≫ c.quotient.hom.hom) ≫
      (CommGroupScheme.groupHom (c.map d hG (𝟙 G))).hom.hom =
    x ≫ d.quotient.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, c.quotient_map, Category.id_comp]

/-- The construction part of KP §11.5 reduces to target bijectivity, torus
naturality between cocenters, and surjectivity of one cocenter Kottwitz composite. -/
theorem simplyConnectedDerivedKottwitz_of_cocenter_data
    (hsc : HasSimplyConnectedDerivedGroup G)
    (hbij : ∀ d : Cocenter k G,
      Function.Bijective (cocenterTargetMap F k G hG d))
    (c : Cocenter k G)
    (hnat : ∀ (d : Cocenter k G) (x : torusKPoints F k c.torus),
      (torusKottwitz F k d.torus d.isTorus
        (affinePointsTarget c.torus.toGrp
          (CommGroupScheme.groupHom (c.map d hG (𝟙 G)))
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      torusInertiaMap k (SeparableClosure F) (c.map d hG (𝟙 G))
        (UnramifiedClosure F) (torusKottwitz F k c.torus c.isTorus x).toAdd)
    (hsurj : Function.Surjective
      ((torusKottwitz F k c.torus c.isTorus).comp
        (G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F))))) :
    (∃! κ, IsSimplyConnectedDerivedKottwitzHom F k G hG κ) ∧
    IsSimplyConnectedDerivedKottwitzHom F k G hG
      (simplyConnectedDerivedKottwitz F k G hG hsc) ∧
    Function.Surjective (simplyConnectedDerivedKottwitz F k G hG hsc) ∧
    ∀ d : Cocenter k G,
      Function.Bijective (cocenterTargetMap F k G hG d) ∧
      ∀ κ, CocenterKottwitzLawAt F k G hG d κ ↔
        κ = simplyConnectedDerivedKottwitz F k G hG hsc := by
  obtain ⟨κ, hκ⟩ := exists_cocenterKottwitzLawAt F k G hG c (hbij c)
  have hall : IsSimplyConnectedDerivedKottwitzHom F k G hG κ := by
    intro d
    exact cocenterKottwitzLawAt_of_torus_naturality F k G hG
      hcmp hfund htorus hmap hinertia c d (hnat d) hκ
  have hex : ∃! κ₁, IsSimplyConnectedDerivedKottwitzHom F k G hG κ₁ := by
    refine ⟨κ, hall, ?_⟩
    intro κ₁ hκ₁
    exact eq_of_cocenterKottwitzLawAt F k G hG c (hbij c).1 (hκ₁ c) hκ
  have hselected : IsSimplyConnectedDerivedKottwitzHom F k G hG
      (simplyConnectedDerivedKottwitz F k G hG hsc) :=
    Classical.epsilon_spec hex.exists
  refine ⟨hex, hselected, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hsurj (Multiplicative.ofAdd (cocenterTargetMap F k G hG c y.toAdd))
    refine ⟨x, ?_⟩
    apply Multiplicative.toAdd.injective
    apply (hbij c).1
    exact (hselected c x).trans (congrArg Multiplicative.toAdd hx)
  · intro d
    refine ⟨hbij d, ?_⟩
    intro κ₁
    constructor
    · intro hκ₁
      exact eq_of_cocenterKottwitzLawAt F k G hG d (hbij d).1 hκ₁ (hselected d)
    · rintro rfl
      exact hselected d

end Langlands.Geometry.Building.Kottwitz
