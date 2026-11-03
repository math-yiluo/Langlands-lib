import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Actual torus transporters and the orbit of their subgroup functors -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G : GroupScheme B}

/-- Base points act on subgroup functors by actual inner conjugation. -/
instance basePointConjugation : MulAction (Over.mk (𝟙 B) ⟶ G.X) (SubgroupFunctor G) where
  smul g F := F.comap (G.innerIso g⁻¹).hom
  one_smul F := by
    change F.comap (G.innerIso (1 : Over.mk (𝟙 B) ⟶ G.X)⁻¹).hom = F
    rw [inv_one, innerIso_one_hom, comap_id]
  mul_smul g h F := by
    change F.comap (G.innerIso (g * h)⁻¹).hom =
      (F.comap (G.innerIso h⁻¹).hom).comap (G.innerIso g⁻¹).hom
    rw [mul_inv_rev, innerIso_mul_hom, comap_comp]

/-- Membership in the conjugate is tested by inverse conjugation on every test scheme. -/
theorem mem_basePoint_smul (g : Over.mk (𝟙 B) ⟶ G.X) (F : SubgroupFunctor G)
    {U : Over B} (x : U ⟶ G.X) :
    x ∈ (g • F).carrier U ↔
      (G.constantPoint g U)⁻¹ * x * G.constantPoint g U ∈ F.carrier U := by
  change x ≫ (G.innerIso g⁻¹).hom.hom.hom ∈ F.carrier U ↔ _
  rw [comp_innerIso_hom, constantPoint_inv, inv_inv]

/-- The stabilizer for conjugation is exactly the all-test normalizer at the base. -/
theorem stabilizer_basePointConjugation (F : SubgroupFunctor G) :
    MulAction.stabilizer (Over.mk (𝟙 B) ⟶ G.X) F =
      F.normalizer.carrier (Over.mk (𝟙 B)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg V a x hx
    rw [comp_eq_constantPoint]
    have hmem (y : V ⟶ G.X) :
        (G.constantPoint g V)⁻¹ * y * G.constantPoint g V ∈ F.carrier V ↔
          y ∈ F.carrier V := by
      rw [← mem_basePoint_smul, hg]
    refine ⟨(hmem _).mp ?_, (hmem x).mpr hx⟩
    simpa only [inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
      inv_mul_cancel, mul_one] using hx
  · intro hg
    apply SubgroupFunctor.ext
    intro V
    ext x
    rw [mem_basePoint_smul]
    have h := hg V (Over.homMk V.hom (by simp))
    simp only [comp_eq_constantPoint] at h
    constructor
    · intro hx
      have h' := (h _ hx).1
      simpa only [mul_inv_cancel_left, inv_mul_cancel_right, mul_assoc,
        mul_inv_cancel, mul_one] using h'
    · intro hx
      exact (h x hx).2

/-- The conjugation action on an actual subgroup range agrees with postcomposition
of the actual inclusion by the same inner isomorphism. -/
theorem basePoint_smul_range {H : GroupScheme B} (i : H ⟶ G)
    (g : Over.mk (𝟙 B) ⟶ G.X) :
    g • range i = range (i ≫ (G.innerIso g).hom) := by
  ext U x
  rw [mem_basePoint_smul, mem_range, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, hy]
    group
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    group

end SubgroupFunctor

section Transporters

variable {B : Scheme.{u}} {T T' : CommGroupScheme B} {G : GroupScheme B}
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
    {g h : Over.mk (𝟙 B) ⟶ G.X} {e_g e_h : T ≅ T'}

/-- Two actual transporters to the same embedded torus differ by a source normalizer.
The induced source automorphism is `e_g` followed by `e_h` inverse. -/
theorem isNormalizingPoint_inv_mul_of_transporters
    (hg : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e_g.hom ≫ j)
    (hh : i ≫ (G.innerIso h).hom = CommGroupScheme.groupHom e_h.hom ≫ j) :
    IsNormalizingPoint i (h⁻¹ * g) (e_g ≪≫ e_h.symm) := by
  have hinv : j ≫ (G.innerIso h⁻¹).hom = CommGroupScheme.groupHom e_h.inv ≫ i := by
    rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, hh, ← Category.assoc]
    change j = CommGroupScheme.groupHom (e_h.inv ≫ e_h.hom) ≫ j
    rw [Iso.inv_hom_id]
    exact (Category.id_comp j).symm
  rw [IsNormalizingPoint, innerIso_mul_hom, ← Category.assoc, hg, Category.assoc,
    hinv, ← Category.assoc]
  rfl

/-- The same difference belongs to the published actual normalizer point subgroup. -/
theorem inv_mul_mem_normalizerPoints_of_transporters
    (hg : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e_g.hom ≫ j)
    (hh : i ≫ (G.innerIso h).hom = CommGroupScheme.groupHom e_h.hom ≫ j) :
    h⁻¹ * g ∈ normalizerPoints i :=
  ⟨e_g ≪≫ e_h.symm, isNormalizingPoint_inv_mul_of_transporters hg hh⟩

end Transporters

section Orbit

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The stabilizer of the actual range subgroup functor is the published normalizer. -/
theorem stabilizer_range_eq_normalizerPoints :
    MulAction.stabilizer (Over.mk (𝟙 B) ⟶ G.X) (SubgroupFunctor.range i) =
      normalizerPoints i := by
  rw [SubgroupFunctor.stabilizer_basePointConjugation]
  exact torusNormalizer_carrier_base i

/-- The orbit of the actual subgroup functor is parametrized by the set of left
cosets of its actual normalizer points. This is a quotient of points. -/
def torusRangeOrbitEquivQuotient :
    MulAction.orbit (Over.mk (𝟙 B) ⟶ G.X) (SubgroupFunctor.range i) ≃
      (Over.mk (𝟙 B) ⟶ G.X) ⧸ normalizerPoints i :=
  (MulAction.orbitEquivQuotientStabilizer _ _).trans
    (Subgroup.quotientEquivOfEq (stabilizer_range_eq_normalizerPoints i))

/-- A coset represented by `g` maps back to the literal range conjugated by `g`. -/
@[simp] theorem torusRangeOrbitEquivQuotient_symm_mk
    (g : Over.mk (𝟙 B) ⟶ G.X) :
    ((torusRangeOrbitEquivQuotient i).symm (QuotientGroup.mk g) : SubgroupFunctor G) =
      SubgroupFunctor.range (i ≫ (G.innerIso g).hom) := by
  change (((MulAction.orbitEquivQuotientStabilizer
    (Over.mk (𝟙 B) ⟶ G.X) (SubgroupFunctor.range i)).symm
      (QuotientGroup.mk g)).val) = _
  rw [MulAction.orbitEquivQuotientStabilizer_symm_apply,
    SubgroupFunctor.basePoint_smul_range]

end Orbit

end Langlands.GroupScheme
