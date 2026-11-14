import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Comparisons and induced maps on fundamental groups with torus target

For a torus target, the canonical comparisons and induced maps on the chosen
presentations `X_*(T)/X_*(T_sc)` of algebraic fundamental groups satisfy their
selection laws unconditionally, with explicit formulas on representatives and
Galois equivariance. -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building.Kottwitz

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

/-- Inner automorphisms of a commutative group scheme are trivial. -/
theorem innerIso_hom_eq_id_of_commGroupScheme {S : Scheme.{u}} (T : CommGroupScheme S)
    (y : Over.mk (𝟙 S) ⟶ T.toGrp.X) : (innerIso T.toGrp y).hom = 𝟙 T.toGrp := by
  apply hom_ext_points
  intro U x
  change x ≫ (innerIso T.toGrp y).hom.hom.hom = x ≫ 𝟙 T.toGrp.X
  rw [comp_innerIso_hom, Category.comp_id, mul_inv_cancel_comm]

variable {k : Type u} [Field k] (E : Type u) [Field E] [Algebra k E]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T.toGrp)

/-- In a torus, the inclusion of the maximal torus of any choice is an isomorphism. -/
def inclusionIso (b : Choice k T.toGrp) : b.torus.toGrp ≅ T.toGrp :=
  @asIso _ _ _ _ b.inclusion (b.isMaximal.isIso_of_torus hT)

/-- The isomorphism `inclusionIso` is the actual inclusion. -/
@[simp]
theorem inclusionIso_hom (b : Choice k T.toGrp) :
    (inclusionIso hT b).hom = b.inclusion := rfl

/-- The actual torus map from a choice `a` of `H` to a choice `c` of a torus,
induced by `f : H ⟶ T`: the composite `a.torus → H → T ≅ c.torus`. -/
def torusTargetHom {H : GroupScheme (Spec (CommRingCat.of k))} (a : Choice k H)
    (c : Choice k T.toGrp) (f : H ⟶ T.toGrp) : a.torus ⟶ c.torus :=
  Additive.ofMul (a.inclusion ≫ f ≫ (inclusionIso hT c).inv)

/-- The defining square of `torusTargetHom`. -/
theorem torusTargetHom_comp_inclusion {H : GroupScheme (Spec (CommRingCat.of k))}
    (a : Choice k H) (c : Choice k T.toGrp) (f : H ⟶ T.toGrp) :
    CommGroupScheme.groupHom (torusTargetHom hT a c f) ≫ c.inclusion = a.inclusion ≫ f := by
  change (a.inclusion ≫ f ≫ (inclusionIso hT c).inv) ≫ c.inclusion = a.inclusion ≫ f
  rw [← inclusionIso_hom hT c]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For one choice of a torus, the induced self-map along the identity is trivial. -/
theorem torusTargetHom_id_self (b : Choice k T.toGrp) :
    torusTargetHom hT b b (𝟙 T.toGrp) = 𝟙 b.torus := by
  apply Additive.toMul.injective
  change b.inclusion ≫ 𝟙 T.toGrp ≫ (inclusionIso hT b).inv = 𝟙 b.torus.toGrp
  rw [Category.id_comp, ← inclusionIso_hom hT b, Iso.hom_inv_id]

/-- The torus isomorphism between the maximal tori of two choices for a torus. -/
def torusChoiceIso (b' b : Choice k T.toGrp) : b'.torus ≅ b.torus where
  hom := torusTargetHom hT b' b (𝟙 T.toGrp)
  inv := torusTargetHom hT b b' (𝟙 T.toGrp)
  hom_inv_id := by
    apply Additive.toMul.injective
    change (b'.inclusion ≫ 𝟙 T.toGrp ≫ (inclusionIso hT b).inv) ≫
      b.inclusion ≫ 𝟙 T.toGrp ≫ (inclusionIso hT b').inv = 𝟙 b'.torus.toGrp
    rw [← inclusionIso_hom hT b, ← inclusionIso_hom hT b']
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  inv_hom_id := by
    apply Additive.toMul.injective
    change (b.inclusion ≫ 𝟙 T.toGrp ≫ (inclusionIso hT b').inv) ≫
      b'.inclusion ≫ 𝟙 T.toGrp ≫ (inclusionIso hT b).inv = 𝟙 b.torus.toGrp
    rw [← inclusionIso_hom hT b, ← inclusionIso_hom hT b']
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- After base change, the torus map is characterized by its composite with the
target inclusion. -/
theorem groupHom_baseChange_torusTargetHom_comp {H : GroupScheme (Spec (CommRingCat.of k))}
    (a : Choice k H) (c : Choice k T.toGrp) (f : H ⟶ T.toGrp) :
    CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map (torusTargetHom hT a c f)) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion =
    (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map f := by
  change (GroupScheme.baseChange (algebraBaseMap k E)).map
      (CommGroupScheme.groupHom (torusTargetHom hT a c f)) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion = _
  rw [← CategoryTheory.Functor.map_comp, torusTargetHom_comp_inclusion,
    CategoryTheory.Functor.map_comp]

include hT in
/-- Morphisms into a base-changed chosen torus are detected after the inclusion. -/
theorem eq_of_groupHom_comp_inclusion (c : Choice k T.toGrp)
    {X : CommGroupScheme (Spec (CommRingCat.of E))}
    (u v : X ⟶ (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus)
    (h : CommGroupScheme.groupHom u ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion =
      CommGroupScheme.groupHom v ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion) : u = v := by
  have : IsIso c.inclusion := c.isMaximal.isIso_of_torus hT
  apply Additive.toMul.injective
  exact (cancel_mono ((GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion)).mp h

include hT in
/-- Two choices of a torus admit a canonical comparison, conjugation by the identity. -/
theorem exists_isCanonicalComparison_of_isTorus (b' b : Choice k T.toGrp) :
    ∃ m, b'.IsCanonicalComparison E b m := by
  have hz : b'.corootImage E = ⊥ := torusChoice_corootImage_eq_bot k E T hT b'
  refine ⟨(b'.corootImage E).liftQ ((b.projection E).comp
      (geometricCocharacterMap k E (torusTargetHom hT b' b (𝟙 T.toGrp))))
      (by rw [hz]; exact bot_le), 1,
    (CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso (torusChoiceIso hT b' b), ?_,
    fun ν => rfl⟩
  change (GroupScheme.baseChange (algebraBaseMap k E)).map b'.inclusion ≫
      (innerIso ((GroupScheme.baseChange (algebraBaseMap k E)).obj T.toGrp) 1).hom =
    CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
          (torusTargetHom hT b' b (𝟙 T.toGrp))) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
  rw [innerIso_one_hom, Category.comp_id, groupHom_baseChange_torusTargetHom_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The selected comparison between two choices of a torus, on representatives. -/
theorem comparison_projection_of_isTorus (b' b : Choice k T.toGrp) (ν : b'.lattice E) :
    b'.comparison E b (b'.projection E ν) =
      b.projection E (geometricCocharacterMap k E (torusTargetHom hT b' b (𝟙 T.toGrp)) ν) := by
  obtain ⟨g, e, hconj, hf⟩ :=
    b'.comparison_spec E b (exists_isCanonicalComparison_of_isTorus E hT b' b)
  rw [hf ν]
  congr 1
  change ν ≫ e.hom = ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
    (torusTargetHom hT b' b (𝟙 T.toGrp))
  congr 1
  apply eq_of_groupHom_comp_inclusion E hT b
  have hi := innerIso_hom_eq_id_of_commGroupScheme
    ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) g
  change (GroupScheme.baseChange (algebraBaseMap k E)).map b'.inclusion ≫
      (innerIso ((GroupScheme.baseChange (algebraBaseMap k E)).obj T.toGrp) g).hom =
    CommGroupScheme.groupHom e.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion at hconj
  rw [← hconj, groupHom_baseChange_torusTargetHom_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [hi]
  exact Category.comp_id _

include hT in
/-- The selected self-comparison of a choice of a torus is the identity. -/
theorem comparison_self_of_isTorus (b : Choice k T.toGrp) :
    b.comparison E b = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (b.corootImage E).mkQ_surjective x
  change b.comparison E b (b.projection E ν) = b.projection E ν
  rw [comparison_projection_of_isTorus E hT b b ν]
  congr 1
  change ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
    (torusTargetHom hT b b (𝟙 T.toGrp)) = ν
  rw [torusTargetHom_id_self, CategoryTheory.Functor.map_id, Category.comp_id]

section InducedMap

variable {H : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k H) (c : Choice k T.toGrp) (f : H ⟶ T.toGrp)

/-- The map to a torus kills the coroot torus `T_sc` of the source choice. -/
theorem scToTorus_comp_torusTargetHom : a.scToTorus ≫ torusTargetHom hT a c f = 0 := by
  let : IsAffineHom T.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  have h1 : a.derivedInclusion ≫ f = 1 := a.isCover.isDerivedSubgroup.comp_eq_one f
  apply Additive.toMul.injective
  change subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion ≫
      a.inclusion ≫ f ≫ (inclusionIso hT c).inv = 1
  rw [← Category.assoc, ← subgroupIntersection_condition]
  simp only [Category.assoc]
  rw [← Category.assoc a.derivedInclusion f, h1]
  apply hom_ext_points
  intro U x
  simp

/-- The map `X_*(T_a)/X_*(T_sc) → X_*(T_c)/0` induced by the actual torus map. -/
def torusTargetInducedMap : a.atChoice E →ₗ[ℤ] c.atChoice E :=
  (a.corootImage E).liftQ
    ((c.projection E).comp (geometricCocharacterMap k E (torusTargetHom hT a c f))) (by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      change c.projection E ((y ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
          a.scToTorus) ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
          (torusTargetHom hT a c f)) = 0
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, scToTorus_comp_torusTargetHom,
        CategoryTheory.Functor.map_zero, Limits.comp_zero, map_zero])

/-- The explicit torus-target map on representatives. -/
@[simp]
theorem torusTargetInducedMap_projection (ν : a.lattice E) :
    torusTargetInducedMap E hT a c f (a.projection E ν) =
      c.projection E (geometricCocharacterMap k E (torusTargetHom hT a c f) ν) := rfl

/-- The base change of the actual torus map is a geometric torus factorization of `f`. -/
theorem isTorusFactorization_torusTargetHom :
    a.IsTorusFactorization E c f
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map (torusTargetHom hT a c f)) :=
  (groupHom_baseChange_torusTargetHom_comp E hT a c f).symm

/-- Every geometric torus factorization of `f`, followed by the selected comparison,
gives the actual torus map on representatives. -/
theorem comparison_projection_of_isTorusFactorization (b : Choice k T.toGrp)
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
    (he : a.IsTorusFactorization E b f e) (ν : a.lattice E) :
    b.comparison E c (b.projection E (ν ≫ e)) =
      c.projection E (geometricCocharacterMap k E (torusTargetHom hT a c f) ν) := by
  rw [comparison_projection_of_isTorus E hT b c]
  congr 1
  change (ν ≫ e) ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map
      (torusTargetHom hT b c (𝟙 T.toGrp)) =
    ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map (torusTargetHom hT a c f)
  rw [Category.assoc]
  congr 1
  apply eq_of_groupHom_comp_inclusion E hT c
  change CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
        (torusTargetHom hT b c (𝟙 T.toGrp))) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion = _
  rw [groupHom_baseChange_torusTargetHom_comp, groupHom_baseChange_torusTargetHom_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact he.symm

/-- The explicit torus-target map satisfies the induced-map law. -/
theorem isInducedMap_torusTargetInducedMap :
    a.IsInducedMap E c f (torusTargetInducedMap E hT a c f) :=
  ⟨⟨c, _, isTorusFactorization_torusTargetHom E hT a c f⟩, fun b e he ν =>
    (comparison_projection_of_isTorusFactorization E hT a c f b e he ν).symm⟩

include hT in
/-- The selected induced map into a torus satisfies its induced-map law. -/
theorem isInducedMap_mapTo_of_isTorus : a.IsInducedMap E c f (a.mapTo E c f) :=
  a.mapTo_spec E c f ⟨_, isInducedMap_torusTargetInducedMap E hT a c f⟩

/-- The selected induced map into a torus, on representatives. -/
theorem mapTo_projection_of_isTorus (ν : a.lattice E) :
    a.mapTo E c f (a.projection E ν) =
      c.projection E (geometricCocharacterMap k E (torusTargetHom hT a c f) ν) := by
  rw [(isInducedMap_mapTo_of_isTorus E hT a c f).2 c _
      (isTorusFactorization_torusTargetHom E hT a c f) ν,
    comparison_projection_of_isTorusFactorization E hT a c f c _
      (isTorusFactorization_torusTargetHom E hT a c f) ν]

/-- The selected induced map into a torus is the explicit torus-target map. -/
theorem mapTo_eq_torusTargetInducedMap :
    a.mapTo E c f = torusTargetInducedMap E hT a c f := by
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  exact mapTo_projection_of_isTorus E hT a c f ν

include hT in
/-- The selected induced map into a torus is equivariant for the actual Galois actions. -/
theorem mapTo_galois_of_isTorus (σ : E ≃ₐ[k] E) (x : a.atChoice E) :
    a.mapTo E c f (a.galoisRepresentation E σ x) =
      c.galoisRepresentation E σ (a.mapTo E c f x) := by
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  change a.mapTo E c f (a.galoisRepresentation E σ (a.projection E ν)) =
    c.galoisRepresentation E σ (a.mapTo E c f (a.projection E ν))
  rw [galoisRepresentation_projection, mapTo_projection_of_isTorus E hT,
    mapTo_projection_of_isTorus E hT, galoisRepresentation_projection,
    geometricCocharacterMap_galois]

end InducedMap

end Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice
