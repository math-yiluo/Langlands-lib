import Langlands.FieldTheory.RealAlgebraicClosure
import Langlands.GroupScheme.CocycleFpqcBaseCover
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Torus.Maximal
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates
import Mathlib.FieldTheory.Galois.Basic

/-! # Toral representatives on a quadratic cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.FieldTheory
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- On an algebraically closed quadratic cover in characteristic zero, a
cocycle of a connected reductive group is represented by a cocycle of a
maximal torus over the base field. -/
def QuadraticToralRepresentativesStatement : Prop :=
  ∀ (K M : Type u) [Field K] [CharZero K] [Field M] [Algebra K M]
    [Algebra.IsQuadraticExtension K M] [IsAlgClosed M]
    (G : GroupScheme (Spec (CommRingCat.of K))), IsConnectedReductive G →
    ∀ (ξ : Cocycle G (ringTest K M)),
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of K))) (j : T.toGrp ⟶ G)
        (_ : IsMaximalTorus (T := T) j) (d : Cocycle T.toGrp (ringTest K M)),
        (d.map j).Cohomologous ξ

namespace Cocycle

variable {S : Scheme.{u}} {G H : GroupScheme S} {U V : Over S}

/-- With maps in both directions, a representative on an fpqc cover of
the base gives a representative on the original cover by refinement. -/
theorem cohomologous_map_refine_of_refine (ξ : Cocycle G U) (d : Cocycle H V)
    (j : H ⟶ G) (p : V ⟶ U) (t : U ⟶ V)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (h : (d.map j).Cohomologous (ξ.refine p)) :
    ((d.refine t).map j).Cohomologous ξ := by
  have hd : (((d.refine t).map j).refine p).Cohomologous (d.map j) := by
    obtain ⟨f, hf⟩ := cohomologous_refine_maps (d.map j) (p ≫ t) (𝟙 V)
    exact ⟨f, fun a b => by
      simpa only [refine_toFun, map, twist, Category.assoc, Category.comp_id] using hf a b⟩
  exact (hd.trans h).of_refine_fpqcCover p

end Cocycle

set_option backward.isDefEq.respectTransparency false in
/-- A field cover containing a square root of `-1` admits toral representatives
after pullback to a copy of the real numbers, given the quadratic-cover result. -/
theorem toralRepresentative_realBaseChange_of_quadratic
    (hrep : QuadraticToralRepresentativesStatement.{u})
    (F K E : Type u) [Field F] [Field K] [Field E] [CharZero K]
    [Algebra F K] [Algebra F E] [Algebra.IsAlgebraic F E]
    (eK : K ≃+* ℝ) {i : E} (hi : i ^ 2 = -1)
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G)
    (c : Cocycle G (ringBaseChange F K (ringTest F E))) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of K))) (j : T.toGrp ⟶ G)
      (_ : IsMaximalTorus (T := T) j)
      (d : Cocycle T.toGrp (ringBaseChange F K (ringTest F E))),
      (d.map j).Cohomologous c := by
  let M := AlgebraicClosure K
  let : Algebra.IsQuadraticExtension K M :=
    { toFree := inferInstance
      finrank_eq_two' := finrank_algebraicClosure_of_equiv_real eK }
  let U := ringBaseChange F K (ringTest F E)
  let V := ringTest K M
  let f : E →ₐ[F] M := IsAlgClosed.lift
  let p : V ⟶ U := ringPointBaseChangeEquiv F K M (ringTest F E) (ringTestMap F f)
  let r : E →ₐ[F] (K ⊗[F] E) := Algebra.TensorProduct.includeRight
  have hr : r i ^ 2 = -1 := by
    rw [← map_pow, hi, map_neg, map_one]
  obtain ⟨g⟩ := nonempty_algHom_algebraicClosure_of_sq_eq_neg_one eK hr
  let t : U ⟶ V := (ringBaseChangeSpectrumIso F K E).hom ≫ ringTestMap K g
  have hfpqc := fieldExtension_fpqc K M
  let : Surjective V.hom := hfpqc.1
  let : Flat V.hom := hfpqc.2.1
  let : QuasiCompact V.hom := hfpqc.2.2
  obtain ⟨T, j, hj, d, hd⟩ := hrep K M G hG (c.refine p)
  exact ⟨T, j, hj, d.refine t, Cocycle.cohomologous_map_refine_of_refine c d j p t hd⟩

end Langlands.GroupScheme
