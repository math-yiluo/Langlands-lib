import Langlands.GroupScheme.Dynamic.LeviParabolicExtension
import Langlands.GroupScheme.Dynamic.LeviCocharacterRealizationProof
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Actual points of a dynamic extension inside its represented Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Extension

variable {S : Scheme.{u}} {G L : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j) [IsSeparated G.X.hom]

/-- Intersecting an exact extension with the represented Levi recovers the
actual image of the original subgroup, on every test scheme. -/
theorem centralizer_inf_extendFromCentralizer (F : SubgroupFunctor L) :
    centralizer χ ⊓ extendFromCentralizer χ j hj F = F.map j := by
  rw [← hj.2, ← SubgroupFunctor.map_comap,
    comap_extendFromCentralizer χ j hj F]

/-- The original subgroup points identify with the literal intersection of
their exact extension and the represented Levi. -/
def extendFromCentralizerPointsEquiv (F : SubgroupFunctor L) (T : Over S) :
    F.carrier T ≃*
      ((extendFromCentralizer χ j hj F).carrier T).subgroupOf ((centralizer χ).carrier T) := by
  let f : F.carrier T →*
      ((extendFromCentralizer χ j hj F).carrier T).subgroupOf
        ((centralizer χ).carrier T) :=
    { toFun x := ⟨hj.pointsEquiv T x, (mem_extendFromCentralizer χ j hj F T _).mpr
        ⟨x, x.property, 1, ((unipotent χ).carrier T).one_mem, mul_one _⟩⟩
      map_one' := by
        apply Subtype.ext
        exact (hj.pointsEquiv T).map_one
      map_mul' x y := by
        apply Subtype.ext
        exact (hj.pointsEquiv T).map_mul x y }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply (hj.pointsEquiv T).injective
    exact congrArg Subtype.val h
  · intro y
    have hy : ((y : (centralizer χ).carrier T) : T ⟶ G.X) ∈ (F.map j).carrier T := by
      rw [← centralizer_inf_extendFromCentralizer χ j hj F]
      exact ⟨y.val.property, y.property⟩
    obtain ⟨x, hx, heq⟩ := SubgroupFunctor.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact heq

@[simp]
theorem extendFromCentralizerPointsEquiv_apply_coe
    (F : SubgroupFunctor L) (T : Over S) (x : F.carrier T) :
    ((extendFromCentralizerPointsEquiv χ j hj F T x :
      (centralizer χ).carrier T) : T ⟶ G.X) = x.val ≫ j.hom.hom := rfl

end Extension

section Realization

variable {S : Scheme.{u}} {G L : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j) [IsSeparated G.X.hom]
    (ν : (Gm S).toGrp ⟶ L) (ψ : (Gm S).toGrp ⟶ G)

/-- The realized ambient parabolic and the directly mapped cocharacter have
the same literal parabolic inside the outer Levi. -/
theorem realized_parabolic_subgroupOf (hjc : IsClosedSubgroup j)
    (hP : parabolic ψ = extendFromCentralizer χ j hj (parabolic ν))
    (T : Over S) :
    ((parabolic ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
      ((parabolic (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) := by
  have h : centralizer χ ⊓ parabolic ψ = centralizer χ ⊓ parabolic (ν ≫ j) := by
    rw [hP, centralizer_inf_extendFromCentralizer,
      ← range_inf_parabolic ν j hjc, hj.2]
  have h' := congrArg (fun F : SubgroupFunctor G =>
    (F.carrier T).subgroupOf ((centralizer χ).carrier T)) h
  simpa only [SubgroupFunctor.inf_carrier, Subgroup.inf_subgroupOf_left] using h'

/-- The realized ambient radical has the exact inner radical of the original
Levi cocharacter, read inside the outer Levi. -/
theorem realized_unipotent_subgroupOf (hjc : IsClosedSubgroup j)
    (hU : unipotent ψ = extendFromCentralizer χ j hj (unipotent ν))
    (T : Over S) :
    ((unipotent ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
      ((unipotent (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) := by
  have h : centralizer χ ⊓ unipotent ψ = centralizer χ ⊓ unipotent (ν ≫ j) := by
    rw [hU, centralizer_inf_extendFromCentralizer,
      ← range_inf_unipotent ν j hjc, hj.2]
  have h' := congrArg (fun F : SubgroupFunctor G =>
    (F.carrier T).subgroupOf ((centralizer χ).carrier T)) h
  simpa only [SubgroupFunctor.inf_carrier, Subgroup.inf_subgroupOf_left] using h'

include hj in
omit [IsSeparated G.X.hom] in
/-- The realized ambient centralizer has the exact inner Levi of the original
Levi cocharacter. -/
theorem realized_centralizer_subgroupOf (hjc : IsClosedSubgroup j)
    (hZ : centralizer ψ = (centralizer ν).map j)
    (T : Over S) :
    ((centralizer ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
      ((centralizer (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) := by
  have hle : (centralizer ν).map j ≤ SubgroupFunctor.range j :=
    SubgroupFunctor.map_le_range j _
  have h : centralizer χ ⊓ centralizer ψ = centralizer χ ⊓ centralizer (ν ≫ j) := by
    rw [hZ, ← hj.2, range_inf_centralizer ν j hjc]
    apply SubgroupFunctor.ext
    intro X
    exact inf_eq_right.mpr (hle X)
  have h' := congrArg (fun F : SubgroupFunctor G =>
    (F.carrier T).subgroupOf ((centralizer χ).carrier T)) h
  simpa only [SubgroupFunctor.inf_carrier, Subgroup.inf_subgroupOf_left] using h'

end Realization

/-- Simultaneous dynamic realization also supplies all three literal
inside-Levi subgroup identifications, with no additional structural premise. -/
theorem exists_realization_with_inside_subgroups
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G)
    (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L) :
    ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
        centralizer ψ = (centralizer ν).map j ∧
        unipotent ψ = extendFromCentralizer χ j hj (unipotent ν)) ∧
      ∀ T : Over (Spec (CommRingCat.of k)),
        ((parabolic ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
            ((parabolic (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) ∧
          ((centralizer ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
            ((centralizer (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) ∧
          ((unipotent ψ).carrier T).subgroupOf ((centralizer χ).carrier T) =
            ((unipotent (ν ≫ j)).carrier T).subgroupOf ((centralizer χ).carrier T) := by
  have := hG.isAffineHom
  obtain ⟨ψ, hP, hZ, hU⟩ :=
    dynamicLeviCocharacterRealization k G hG χ L j hjc hj ν
  exact ⟨ψ, ⟨hP, hZ, hU⟩, fun T =>
    ⟨realized_parabolic_subgroupOf χ j hj ν ψ hjc hP T,
      realized_centralizer_subgroupOf χ j hj ν ψ hjc hZ T,
      realized_unipotent_subgroupOf χ j hj ν ψ hjc hU T⟩⟩

end Langlands.GroupScheme.Dynamic
