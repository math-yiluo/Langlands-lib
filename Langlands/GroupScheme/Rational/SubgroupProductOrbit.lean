import Langlands.GroupScheme.Products
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.SchemeActionOrbit
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.AffineClosedOrbit

/-! # Subgroup products as actual scheme orbits -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupProductOrbit

variable {S : Scheme.{u}} {V C U : GroupScheme S}

/-- Left multiplication by the first subgroup and inverse right multiplication
by the second subgroup. -/
def actionHom (j : V ⟶ U) (c : C ⟶ U) : (V ⊗ C).X ⊗ U.X ⟶ U.X :=
  ((fst (V.X ⊗ C.X) U.X ≫ fst V.X C.X ≫ j.hom.hom) *
    snd (V.X ⊗ C.X) U.X) *
      (fst (V.X ⊗ C.X) U.X ≫ snd V.X C.X ≫ c.hom.hom)⁻¹

theorem comp_actionHom (j : V ⟶ U) (c : C ⟶ U)
    {T : Over S} (g : T ⟶ (V ⊗ C).X) (x : T ⟶ U.X) :
    lift g x ≫ actionHom j c =
      ((g ≫ fst V.X C.X ≫ j.hom.hom) * x) *
        (g ≫ snd V.X C.X ≫ c.hom.hom)⁻¹ := by
  change lift (show T ⟶ V.X ⊗ C.X from g) x ≫ actionHom j c = _
  simp only [actionHom, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd]

/-- The product group acts on the ambient scheme by two-sided multiplication.
No commutativity or normalization of the subgroups is required. -/
@[instance_reducible]
def action (j : V ⟶ U) (c : C ⟶ U) : SchemeAction (V ⊗ C) U.X :=
  schemeActionOfPointLaws (actionHom j c)
    (by
      intro T x
      simp only [comp_actionHom, MonObj.one_comp, one_mul, inv_one, mul_one])
    (by
      intro T g h x
      simp only [comp_actionHom, MonObj.mul_comp, mul_inv_rev]
      group)

theorem act_eq (j : V ⟶ U) (c : C ⟶ U)
    {T : Over S} (g : T ⟶ (V ⊗ C).X) (x : T ⟶ U.X) :
    (action j c).act g x =
      ((g ≫ fst V.X C.X ≫ j.hom.hom) * x) *
        (g ≫ snd V.X C.X ≫ c.hom.hom)⁻¹ :=
  comp_actionHom j c g x

/-- The diagonal inclusion of the actual scheme-theoretic intersection into
the product group. -/
def intersectionDiagonal (j : V ⟶ U) (c : C ⟶ U) :
    subgroupIntersection j c ⟶ V ⊗ C :=
  lift (subgroupIntersectionFst j c) (subgroupIntersectionSnd j c)

@[reassoc (attr := simp)]
theorem intersectionDiagonal_fst (j : V ⟶ U) (c : C ⟶ U) :
    (intersectionDiagonal j c).hom.hom ≫ fst V.X C.X =
      (subgroupIntersectionFst j c).hom.hom := by
  change (lift (subgroupIntersectionFst j c) (subgroupIntersectionSnd j c) ≫
    fst V C).hom.hom = _
  rw [lift_fst]

@[reassoc (attr := simp)]
theorem intersectionDiagonal_snd (j : V ⟶ U) (c : C ⟶ U) :
    (intersectionDiagonal j c).hom.hom ≫ snd V.X C.X =
      (subgroupIntersectionSnd j c).hom.hom := by
  change (lift (subgroupIntersectionFst j c) (subgroupIntersectionSnd j c) ≫
    snd V C).hom.hom = _
  rw [lift_snd]

/-- The stabilizer diagonal has the expected all-test membership criterion. -/
theorem mem_range_intersectionDiagonal_iff (j : V ⟶ U) (c : C ⟶ U)
    {T : Over S} (g : T ⟶ (V ⊗ C).X) :
    g ∈ (SubgroupFunctor.range (intersectionDiagonal j c)).carrier T ↔
      g ≫ fst V.X C.X ≫ j.hom.hom =
        g ≫ snd V.X C.X ≫ c.hom.hom := by
  constructor
  · intro hg
    obtain ⟨e, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    simp only [Category.assoc, intersectionDiagonal_fst_assoc,
      intersectionDiagonal_snd_assoc]
    exact congrArg (fun f => e ≫ f) (subgroupIntersection_isPullback j c).w
  · intro hg
    refine SubgroupFunctor.mem_range.mpr
      ⟨(subgroupIntersection_isPullback j c).lift
        (g ≫ fst V.X C.X) (g ≫ snd V.X C.X) hg, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, intersectionDiagonal_fst]
      exact (subgroupIntersection_isPullback j c).lift_fst _ _ _
    · rw [Category.assoc, intersectionDiagonal_snd]
      exact (subgroupIntersection_isPullback j c).lift_snd _ _ _

/-- The orbit through the identity is the original product with the second
coordinate inverted. -/
theorem comp_orbitMap_one (j : V ⟶ U) (c : C ⟶ U)
    {T : Over S} (g : T ⟶ (V ⊗ C).X) :
    g ≫ (action j c).orbitMap 1 =
      (g ≫ fst V.X C.X ≫ j.hom.hom) *
        (g ≫ snd V.X C.X ≫ c.hom.hom)⁻¹ := by
  rw [SchemeAction.comp_orbitMap, act_eq, MonObj.comp_one, mul_one]

/-- Equality of orbit points is exactly a coset of the actual intersection
diagonal, on arbitrary scheme tests. -/
theorem orbit_fibers (j : V ⟶ U) (c : C ⟶ U)
    (T : Over S) (g h : T ⟶ (V ⊗ C).X) :
    g ≫ (action j c).orbitMap 1 = h ≫ (action j c).orbitMap 1 ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range (intersectionDiagonal j c)).carrier T := by
  rw [comp_orbitMap_one, comp_orbitMap_one, mem_range_intersectionDiagonal_iff]
  simp only [MonObj.mul_comp, GrpObj.inv_comp]
  constructor <;> intro he
  · apply (inv_mul_eq_iff_eq_mul).2
    calc
      _ = ((h ≫ fst V.X C.X ≫ j.hom.hom) *
          (h ≫ snd V.X C.X ≫ c.hom.hom)⁻¹) *
            (h ≫ snd V.X C.X ≫ c.hom.hom) := by group
      _ = _ := by rw [← he]; group
  · have hh := (inv_mul_eq_iff_eq_mul).1 he
    calc
      _ = (g ≫ fst V.X C.X ≫ j.hom.hom) *
          ((g ≫ snd V.X C.X ≫ c.hom.hom)⁻¹ *
            (h ≫ snd V.X C.X ≫ c.hom.hom)) *
          (h ≫ snd V.X C.X ≫ c.hom.hom)⁻¹ := by group
      _ = _ := by rw [← hh]

/-- The diagonal stabilizer is closed when the second subgroup is closed
and its source is separated over the base. -/
theorem closed_intersectionDiagonal (j : V ⟶ U) (c : C ⟶ U)
    [IsSeparated C.X.hom] (hc : IsClosedSubgroup c) :
    IsClosedSubgroup (intersectionDiagonal j c) := by
  have : IsSeparated (fst V.X C.X).left := by
    change IsSeparated (pullback.fst V.X.hom C.X.hom)
    infer_instance
  have he : (intersectionDiagonal j c).hom.hom.left ≫ (fst V.X C.X).left =
      (subgroupIntersectionFst j c).hom.hom.left :=
    congrArg Over.Hom.left (intersectionDiagonal_fst j c)
  have : IsClosedImmersion
      ((intersectionDiagonal j c).hom.hom.left ≫ (fst V.X C.X).left) := by
    rw [he]
    exact isClosedSubgroup_subgroupIntersectionFst j hc
  exact IsClosedImmersion.of_comp _ (fst V.X C.X).left

section ClosedOrbit

variable {k : Type u} [Field k] [IsAlgClosed k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]

/-- The actual closed product orbit is a smooth surjective homogeneous quotient
by the scheme-theoretic diagonal intersection. -/
def closedOrbitQuotient (j : V ⟶ U) (c : C ⟶ U)
    (hc : IsClosedSubgroup c)
    (hE : Smooth (subgroupIntersection j c).X.hom)
    (hclosed : IsClosed (Set.range ((action j c).orbitMap 1).left)) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient
      (intersectionDiagonal j c) := by
  let : Smooth (V ⊗ C).X.hom :=
    prop_tensor_hom (@Smooth) V.X C.X inferInstance inferInstance
  let : IsAffineHom (V ⊗ C).X.hom :=
    prop_tensor_hom (@IsAffineHom) V.X C.X inferInstance inferInstance
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  exact (action j c).quotientOfClosedAffineOrbit 1 (intersectionDiagonal j c)
    (closed_intersectionDiagonal j c hc) hE (orbit_fibers j c) hclosed

end ClosedOrbit

end Langlands.GroupScheme.SubgroupProductOrbit
