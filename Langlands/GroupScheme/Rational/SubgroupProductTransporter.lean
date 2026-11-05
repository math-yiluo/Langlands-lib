import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Transporting conjugates through a faithfully flat subgroup product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H U V C : GroupScheme S}
    {T : CommGroupScheme S}

/-- The actual conjugation morphism for two homomorphisms into a common group. -/
def subgroupConjugation (n : U ⟶ G) (t : T.toGrp ⟶ G) : U.X ⊗ T.X ⟶ G.X :=
  (fst U.X T.X ≫ n.hom.hom) * (snd U.X T.X ≫ t.hom.hom) *
    (fst U.X T.X ≫ n.hom.hom)⁻¹

/-- Evaluation of the actual conjugation morphism on any test scheme. -/
theorem comp_subgroupConjugation (n : U ⟶ G) (t : T.toGrp ⟶ G)
    {R : Over S} (u : R ⟶ U.X) (x : R ⟶ T.X) :
    lift u x ≫ subgroupConjugation n t =
      (u ≫ n.hom.hom) * (x ≫ t.hom.hom) * (u ≫ n.hom.hom)⁻¹ := by
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd_assoc]

/-- If a subgroup product covers `U` faithfully flatly, its first factor
lies in `H`, and its second factor centralizes `T`, every `U`-conjugate of
`T` lies in `H`, on every relative scheme test. -/
theorem conj_mem_of_fpqc_subgroupProduct
    (h : H ⟶ G) [Mono h.hom.hom]
    (n : U ⟶ G) (j : V ⟶ U) (c : C ⟶ U) (t : T.toGrp ⟶ G)
    [Flat (subgroupMultiplication j c).left]
    [Surjective (subgroupMultiplication j c).left]
    [QuasiCompact (subgroupMultiplication j c).left]
    (hj : SubgroupFunctor.range (j ≫ n) ≤ SubgroupFunctor.range h)
    (ht : SubgroupFunctor.range t ≤ SubgroupFunctor.range h)
    (hc : SubgroupFunctor.range (c ≫ n) ≤ torusCentralizer t)
    (R : Over S) (u : R ⟶ U.X) (x : R ⟶ G.X)
    (hx : x ∈ (SubgroupFunctor.range t).carrier R) :
    (u ≫ n.hom.hom) * x * (u ≫ n.hom.hom)⁻¹ ∈
      (SubgroupFunctor.range h).carrier R := by
  let m := subgroupMultiplication j c
  let W : Over S := pullback u m
  let p : W ⟶ R := pullback.fst u m
  let a : W ⟶ V.X ⊗ C.X := pullback.snd u m
  have hpb := (IsPullback.of_hasPullback u m).map (Over.forget S)
  let : Flat p.left := MorphismProperty.of_isPullback hpb.flip
    (inferInstanceAs (Flat (subgroupMultiplication j c).left))
  let : Surjective p.left := MorphismProperty.of_isPullback hpb.flip
    (inferInstanceAs (Surjective (subgroupMultiplication j c).left))
  let : QuasiCompact p.left := MorphismProperty.of_isPullback hpb.flip
    (inferInstanceAs (QuasiCompact (subgroupMultiplication j c).left))
  let : EffectiveEpi p.left := inferInstance
  apply SubgroupFunctor.mem_range_of_comp_mem_range h p
  let v : W ⟶ V.X := a ≫ fst V.X C.X
  let z : W ⟶ C.X := a ≫ snd V.X C.X
  have hu : p ≫ u = (v ≫ j.hom.hom) * (z ≫ c.hom.hom) := by
    change pullback.fst u m ≫ u = _
    rw [pullback.condition]
    change a ≫ subgroupMultiplication j c = _
    simp only [subgroupMultiplication, MonObj.comp_mul, v, z, Category.assoc]
  have hux : p ≫ (u ≫ n.hom.hom) =
      (v ≫ (j ≫ n).hom.hom) * (z ≫ (c ≫ n).hom.hom) := by
    rw [← Category.assoc, hu, MonObj.mul_comp]
    rfl
  have hv : v ≫ (j ≫ n).hom.hom ∈ (SubgroupFunctor.range h).carrier W :=
    hj W (SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩)
  have hz : z ≫ (c ≫ n).hom.hom ∈ (torusCentralizer t).carrier W :=
    hc W (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩)
  have hx' : p ≫ x ∈ (SubgroupFunctor.range h).carrier W :=
    ht W ((SubgroupFunctor.range t).comp_mem p hx)
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  have hcomm : Commute (z ≫ (c ≫ n).hom.hom) (p ≫ x) := by
    rw [← hy, ← Category.assoc]
    simpa only [Category.id_comp] using hz W (𝟙 W) (p ≫ y)
  have heq : p ≫ ((u ≫ n.hom.hom) * x * (u ≫ n.hom.hom)⁻¹) =
      (v ≫ (j ≫ n).hom.hom) * (p ≫ x) * (v ≫ (j ≫ n).hom.hom)⁻¹ := by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hux]
    calc
      _ = (v ≫ (j ≫ n).hom.hom) *
          ((z ≫ (c ≫ n).hom.hom) * (p ≫ x)) *
          (z ≫ (c ≫ n).hom.hom)⁻¹ * (v ≫ (j ≫ n).hom.hom)⁻¹ := by group
      _ = _ := by rw [hcomm.eq]; group
  rw [heq]
  exact (SubgroupFunctor.range h).carrier W |>.mul_mem
    ((SubgroupFunctor.range h).carrier W |>.mul_mem hv hx')
    ((SubgroupFunctor.range h).carrier W |>.inv_mem hv)

end Langlands.GroupScheme
