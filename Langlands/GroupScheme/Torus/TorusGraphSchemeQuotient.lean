import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.Products

/-! # A smooth graph relation for a representation with central kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusGraphQuotient

open HomogeneousQuotientFromEmbedding
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
open SelfCentralizingConjugacyClosedEmbeddingReduction (exists_torus_point_of_comp_eq)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G L : GroupScheme S} {T D : CommGroupScheme S}

/-- The subgroup of `G × D` given by `τ ↦ (t(τ), π(τ)⁻¹)`. -/
def graph (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) : T.toGrp ⟶ G ⊗ D.toGrp :=
  Grp.homMk (lift t.hom.hom (π.hom.hom ≫ ι[D.X]))

@[simp, reassoc]
theorem graph_fst (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) :
    (graph t π).hom.hom ≫ fst G.X D.X = t.hom.hom := lift_fst _ _

@[simp, reassoc]
theorem graph_snd (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) :
    (graph t π).hom.hom ≫ snd G.X D.X = π.hom.hom ≫ ι[D.X] := lift_snd _ _

private theorem comp_graph_snd (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp)
    {U : Over S} (τ : U ⟶ T.X) :
    (τ ≫ (graph t π).hom.hom) ≫ snd G.X D.X = (τ ≫ π.hom.hom)⁻¹ := by
  rw [Category.assoc, graph_snd, ← Category.assoc]
  rfl

instance (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) [Mono t.hom.hom] :
    Mono (graph t π).hom.hom := mono_of_mono_fac (graph_fst t π)

/-- The underlying scheme map `(g,d) ↦ ρ(g)e(d)`. No commutation of the two
factors in `L` is assumed. -/
def productMap (ρ : G ⟶ L) (e : D.toGrp ⟶ L) : (G ⊗ D.toGrp).X ⟶ L.X :=
  (fst G.X D.X ≫ ρ.hom.hom) * (snd G.X D.X ≫ e.hom.hom)

@[reassoc]
theorem comp_productMap (ρ : G ⟶ L) (e : D.toGrp ⟶ L) {U : Over S}
    (x : U ⟶ (G ⊗ D.toGrp).X) :
    x ≫ productMap ρ e = (x ≫ fst G.X D.X ≫ ρ.hom.hom) *
      (x ≫ snd G.X D.X ≫ e.hom.hom) := by
  simp only [productMap, MonObj.comp_mul]

variable (ρ : G ⟶ L) (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) (e : D.toGrp ⟶ L)
variable [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
  [LocallyOfFinitePresentation π.hom.hom.left]
variable (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
variable (hcent : (torusCentralizer t).IsRepresentedBy t) (he : Mono e.hom.hom)
variable (hπe : π ≫ e = t ≫ ρ)

include hρ hcent he hπe

/-- A point of `G` over a supplied point of `D` lifts to a point of `T` with
both coordinates prescribed. -/
theorem exists_graph_coordinate {U : Over S} (y : U ⟶ G.X) (d : U ⟶ D.X)
    (hy : y ≫ ρ.hom.hom = d ≫ e.hom.hom) :
    ∃ τ : U ⟶ T.X, τ ≫ t.hom.hom = y ∧ τ ≫ π.hom.hom = d := by
  let : Mono e.hom.hom := he
  obtain ⟨τ, hτ⟩ := exists_torus_point_of_comp_eq ρ t π e hρ hcent hπe y d hy
  have hc : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun φ => φ.hom.hom) hπe
  refine ⟨τ, hτ, (cancel_mono e.hom.hom).mp ?_⟩
  rw [Category.assoc, hc, ← Category.assoc, hτ, hy]

/-- The full scheme-valued fibres of `productMap` are exactly the right cosets
of the graph subgroup. -/
theorem productMap_fibers (U : Over S) (x y : U ⟶ (G ⊗ D.toGrp).X) :
    x ≫ productMap ρ e = y ≫ productMap ρ e ↔
      x⁻¹ * y ∈ (SubgroupFunctor.range (graph t π)).carrier U := by
  let g := x ≫ fst G.X D.X
  let h := y ≫ fst G.X D.X
  let d := x ≫ snd G.X D.X
  let d' := y ≫ snd G.X D.X
  simp only [comp_productMap, SubgroupFunctor.mem_range]
  change (g ≫ ρ.hom.hom) * (d ≫ e.hom.hom) = (h ≫ ρ.hom.hom) * (d' ≫ e.hom.hom) ↔ _
  have hc : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun φ => φ.hom.hom) hπe
  constructor
  · intro hx
    have hz : (g⁻¹ * h) ≫ ρ.hom.hom = (d * d'⁻¹) ≫ e.hom.hom := by
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
      calc
        (g ≫ ρ.hom.hom)⁻¹ * (h ≫ ρ.hom.hom) =
            (g ≫ ρ.hom.hom)⁻¹ * ((h ≫ ρ.hom.hom) * (d' ≫ e.hom.hom)) *
              (d' ≫ e.hom.hom)⁻¹ := by group
        _ = _ := by rw [← hx]; group
    obtain ⟨τ, hτ, hτ'⟩ := exists_graph_coordinate ρ t π e hρ hcent he hπe _ _ hz
    refine ⟨τ, CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
    · simpa only [Category.assoc, graph_fst, MonObj.mul_comp, GrpObj.inv_comp] using hτ
    · have hh : (τ ≫ π.hom.hom)⁻¹ = d⁻¹ * d' := by
        rw [hτ', mul_inv_rev, inv_inv, mul_comm]
      rw [comp_graph_snd, MonObj.mul_comp, GrpObj.inv_comp]
      exact hh
  · rintro ⟨τ, hτ⟩
    have h₁ : τ ≫ t.hom.hom = g⁻¹ * h := by
      simpa only [Category.assoc, graph_fst, MonObj.mul_comp, GrpObj.inv_comp] using
        congrArg (fun a => a ≫ fst G.X D.X) hτ
    have h₂ : (τ ≫ π.hom.hom)⁻¹ = d⁻¹ * d' := by
      have hz := congrArg (fun a => a ≫ snd G.X D.X) hτ
      rw [comp_graph_snd, MonObj.mul_comp, GrpObj.inv_comp] at hz
      exact hz
    have hp : τ ≫ π.hom.hom = d * d'⁻¹ := by
      simpa only [inv_inv, mul_inv_rev, mul_comm] using congrArg Inv.inv h₂
    have hz : (g ≫ ρ.hom.hom)⁻¹ * (h ≫ ρ.hom.hom) = (d ≫ e.hom.hom) * (d' ≫ e.hom.hom)⁻¹ := by
      calc
        _ = (g⁻¹ * h) ≫ ρ.hom.hom := by rw [MonObj.mul_comp, GrpObj.inv_comp]
        _ = (τ ≫ π.hom.hom) ≫ e.hom.hom := by
          rw [← h₁, Category.assoc, Category.assoc, hc]
        _ = _ := by rw [hp, MonObj.mul_comp, GrpObj.inv_comp]
    calc
      (g ≫ ρ.hom.hom) * (d ≫ e.hom.hom) =
          (g ≫ ρ.hom.hom) * ((d ≫ e.hom.hom) * (d' ≫ e.hom.hom)⁻¹) *
            (d' ≫ e.hom.hom) := by group
      _ = _ := by rw [← hz]; group

/-- The scheme quotient of the smooth graph relation inside `G × D`. Its
projection is smooth and surjective, even when the kernel of `ρ` is not smooth. -/
def graphSchemeQuotient (hG : LocallyOfFiniteType G.X.hom) (hD : LocallyOfFiniteType D.X.hom)
    (hT : Smooth T.X.hom) :
    SchemeQuotientEmbedding (arrowSpace (graph t π)) (source (graph t π)) (target (graph t π))
      L.X (productMap ρ e) := by
  letI : Mono t.hom.hom := hcent.1
  haveI : LocallyOfFiniteType G.X.hom := hG
  haveI : LocallyOfFiniteType D.X.hom := hD
  have H : LocallyOfFiniteType (G ⊗ D.toGrp).X.hom := by
    change LocallyOfFiniteType (G.X ⊗ D.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  exact schemeQuotientOfMapKernel (isEquivalenceRelation (graph t π))
    (hasSmoothProjections (graph t π) hT) H L.X (productMap ρ e)
    (fun U x y => (productMap_fibers ρ t π e hρ hcent he hπe U x y).trans
      (relation_iff (graph t π) U x y).symm)

end Langlands.GroupScheme.TorusGraphQuotient
