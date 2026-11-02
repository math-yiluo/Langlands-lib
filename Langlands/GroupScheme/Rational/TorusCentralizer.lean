import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.HomConjugacy

/-! # The centralizer of a torus on all test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- The centralizer of a torus homomorphism, tested after every refinement of the
test scheme. The construction also makes sense for any commutative group scheme. -/
def torusCentralizer (i : T.toGrp ⟶ G) : SubgroupFunctor G where
  carrier U :=
    { carrier := {g | ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
        Commute (a ≫ g) (t ≫ i.hom.hom)}
      one_mem' := by
        intro V a t
        rw [MonObj.comp_one]
        exact Commute.one_left _
      mul_mem' := by
        intro g h hg hh V a t
        rw [MonObj.comp_mul]
        exact (hg V a t).mul_left (hh V a t)
      inv_mem' := by
        intro g hg V a t
        rw [GrpObj.comp_inv]
        exact (hg V a t).inv_left }
  comp_mem a g hg V b t := by
    rw [← Category.assoc]
    exact hg V (b ≫ a) t

theorem mem_torusCentralizer (i : T.toGrp ⟶ G) {U : Over S} {g : U ⟶ G.X} :
    g ∈ (torusCentralizer i).carrier U ↔
      ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
        Commute (a ≫ g) (t ≫ i.hom.hom) :=
  Iff.rfl

/-- It suffices to test commutation against the universal torus point. -/
theorem mem_torusCentralizer_iff_universal (i : T.toGrp ⟶ G)
    {U : Over S} {g : U ⟶ G.X} :
    g ∈ (torusCentralizer i).carrier U ↔
      Commute (fst U T.X ≫ g) (snd U T.X ≫ i.hom.hom) := by
  constructor
  · intro hg
    exact hg _ (fst U T.X) (snd U T.X)
  · intro hg V a t
    have h := congrArg (fun f => lift a t ≫ f) hg.eq
    change (a ≫ g) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (a ≫ g)
    simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc] using h

/-- At the base scheme the centralizer consists exactly of the points whose
inner automorphism fixes the torus homomorphism. -/
theorem mem_torusCentralizer_base_iff (i : T.toGrp ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    g ∈ (torusCentralizer i).carrier (Over.mk (𝟙 S)) ↔
      i ≫ (G.innerIso g).hom = i := by
  constructor
  · intro hg
    apply hom_ext_points
    intro U t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    have hc := hg U (Over.homMk U.hom (by simp)) t
    change G.constantPoint g U * (t ≫ i.hom.hom) =
      (t ≫ i.hom.hom) * G.constantPoint g U at hc
    rw [hc, mul_inv_cancel_right]
  · intro hg U a t
    have h := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom) hg
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    have ha : a ≫ g = G.constantPoint g U := by
      simpa only [constantPoint_self] using G.constantPoint_naturality g a
    change (a ≫ g) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (a ≫ g)
    rw [ha]
    exact (mul_inv_eq_iff_eq_mul).mp h

/-- For the multiplicative group, the whole-group centralizer is exactly the
published dynamic centralizer of the cocharacter. -/
theorem torusCentralizer_gm_eq_dynamicCentralizer (χ : (Gm S).toGrp ⟶ G) :
    torusCentralizer χ = Dynamic.centralizer χ := by
  apply SubgroupFunctor.ext
  intro U
  ext g
  rw [mem_torusCentralizer_iff_universal, Dynamic.mem_centralizer, Dynamic.orbit]
  constructor
  · intro hg
    rw [hg.symm.eq, mul_inv_cancel_right]
  · intro hg
    exact ((mul_inv_eq_iff_eq_mul).mp hg).symm

/-- The centralizer of the whole torus lies in the dynamic centralizer of every
cocharacter that factors through that torus. -/
theorem torusCentralizer_le_dynamicCentralizer (i : T.toGrp ⟶ G)
    (χ : (Gm S).toGrp ⟶ T.toGrp) :
    torusCentralizer i ≤ Dynamic.centralizer (χ ≫ i) := by
  intro U g hg
  rw [Dynamic.mem_centralizer, Dynamic.orbit, Grp.comp_hom_hom]
  have hc := hg (U ⊗ (Gm S).X) (fst U (Gm S).X)
    (snd U (Gm S).X ≫ χ.hom.hom)
  rw [Category.assoc] at hc
  rw [hc.symm.eq, mul_inv_cancel_right]

end Langlands.GroupScheme
