import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Stabilizers of closed subsets under left translation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The points `g` of `G` such that left translation by `g` and by `g⁻¹` keeps every point with
image in `Z` inside `Z`. -/
def stabilizer (Z : Set G.X.left) : SubgroupFunctor G where
  carrier Y :=
    { carrier := {g | ∀ (W : Over (Spec (CommRingCat.of k))) (y : W ⟶ Y) (z : W ⟶ G.X),
        Set.range z.left.base ⊆ Z →
          Set.range ((y ≫ g) * z).left.base ⊆ Z ∧ Set.range ((y ≫ g)⁻¹ * z).left.base ⊆ Z}
      mul_mem' := by
        intro g h hg hh W y z hz
        have e1 : (y ≫ (g * h)) * z = (y ≫ g) * ((y ≫ h) * z) := by
          rw [MonObj.comp_mul, mul_assoc]
        have e2 : (y ≫ (g * h))⁻¹ * z = (y ≫ h)⁻¹ * ((y ≫ g)⁻¹ * z) := by
          rw [MonObj.comp_mul, mul_inv_rev, mul_assoc]
        rw [e1, e2]
        exact ⟨(hg W y _ (hh W y z hz).1).1, (hh W y _ (hg W y z hz).2).2⟩
      one_mem' := by
        intro W y z hz
        simp only [MonObj.comp_one, one_mul, inv_one]
        exact ⟨hz, hz⟩
      inv_mem' := by
        intro g hg W y z hz
        simp only [Set.mem_ofPred_eq] at hg ⊢
        rw [GrpObj.comp_inv, inv_inv]
        exact ⟨(hg W y z hz).2, (hg W y z hz).1⟩ }
  comp_mem := by
    intro T T' a x hx W y z hz
    rw [← Category.assoc]
    exact hx W (y ≫ a) z hz

theorem mem_stabilizer {Z : Set G.X.left} {Y : Over (Spec (CommRingCat.of k))} {g : Y ⟶ G.X} :
    g ∈ (stabilizer Z).carrier Y ↔ ∀ (W : Over (Spec (CommRingCat.of k))) (y : W ⟶ Y)
      (z : W ⟶ G.X), Set.range z.left.base ⊆ Z →
        Set.range ((y ≫ g) * z).left.base ⊆ Z ∧ Set.range ((y ≫ g)⁻¹ * z).left.base ⊆ Z :=
  Iff.rfl

/-! ### Translation by a smooth connected group -/

section Action

variable (H G' : GroupScheme (Spec (CommRingCat.of k)))

/-- The product `H ×ₖ G` as a scheme over `k`, through its second projection. -/
abbrev prodOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.snd H.X.hom G'.X.hom ≫ G'.X.hom)

/-- The first projection of the product. -/
def prodFst : prodOver H G' ⟶ H.X :=
  Over.homMk (pullback.fst H.X.hom G'.X.hom) (by simp [pullback.condition])

/-- The second projection of the product. -/
def prodSnd : prodOver H G' ⟶ G'.X :=
  Over.homMk (pullback.snd H.X.hom G'.X.hom) rfl

variable {H G'} in
/-- The point of the product with prescribed coordinates. -/
def prodLift {W : Over (Spec (CommRingCat.of k))} (h : W ⟶ H.X) (z : W ⟶ G'.X) :
    W ⟶ prodOver H G' :=
  Over.homMk (pullback.lift h.left z.left (by rw [Over.w h, Over.w z]))
    (by simp only [Over.mk_hom]; rw [pullback.lift_snd_assoc, Over.w z])

variable {H G'}

@[simp] theorem prodLift_fst {W : Over (Spec (CommRingCat.of k))} (h : W ⟶ H.X) (z : W ⟶ G'.X) :
    prodLift h z ≫ prodFst H G' = h := by
  apply Over.OverMorphism.ext
  simp only [prodLift, prodFst, Over.comp_left, Over.homMk_left, pullback.lift_fst]

@[simp] theorem prodLift_snd {W : Over (Spec (CommRingCat.of k))} (h : W ⟶ H.X) (z : W ⟶ G'.X) :
    prodLift h z ≫ prodSnd H G' = z := by
  apply Over.OverMorphism.ext
  simp only [prodLift, prodSnd, Over.comp_left, Over.homMk_left, pullback.lift_snd]

/-- **Translation by a smooth connected group preserves a maximal closed irreducible subset of
the complement of an open set.** Let `H` be a smooth connected affine group mapping to `G`, let
`V` be open and let `Z` be irreducible. Assume that every closed irreducible set containing `Z`
and disjoint from `V` is contained in `Z` (neither closedness of `Z` nor disjointness of `Z`
from `V` is assumed). If translating points of `Z` by points of `H` never lands in `V`, then
translation by points of `H` keeps `Z` stable. -/
theorem range_subset_of_maximal [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) {Z V : Set G.X.left} (hV : IsOpen V) (hZ : IsIrreducible Z)
    (hmax : ∀ T : Set G.X.left, IsIrreducible T → IsClosed T → Z ⊆ T → Disjoint T V → T ⊆ Z)
    (hyp : ∀ (W : Over (Spec (CommRingCat.of k))) (h : W ⟶ H.X) (z : W ⟶ G.X) (w : W.left),
      z.left.base w ∈ Z → ((h ≫ j.hom.hom) * z).left.base w ∉ V)
    {W : Over (Spec (CommRingCat.of k))} (h : W ⟶ H.X) (z : W ⟶ G.X)
    (hz : Set.range z.left.base ⊆ Z) : Set.range ((h ≫ j.hom.hom) * z).left.base ⊆ Z := by
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  let T := ⇑(pullback.snd H.X.hom G.X.hom) ⁻¹' Z
  have hT : IsIrreducible T :=
    (pullback.snd H.X.hom G.X.hom).isIrreducible_preimage
      (pullback.snd H.X.hom G.X.hom).isOpenMap hZ
  let act : prodOver H G ⟶ G.X := (prodFst H G ≫ j.hom.hom) * prodSnd H G
  have hact : ∀ {W' : Over (Spec (CommRingCat.of k))} (h' : W' ⟶ H.X) (z' : W' ⟶ G.X),
      (h' ≫ j.hom.hom) * z' = prodLift h' z' ≫ act := by
    intro W' h' z'
    rw [MonObj.comp_mul, ← Category.assoc, prodLift_fst, prodLift_snd]
  have hC : IsIrreducible (closure (act.left.base '' T)) :=
    (hT.image _ act.left.base.hom.continuous.continuousOn).closure
  have hZC : Z ⊆ closure (act.left.base '' T) := by
    intro x hx
    apply subset_closure
    let sec : G.X ⟶ prodOver H G := prodLift 1 (𝟙 G.X)
    have hsec : sec ≫ act = 𝟙 G.X := by
      rw [← hact, MonObj.one_comp, one_mul]
    refine ⟨sec.left.base x, ?_, ?_⟩
    · change (sec ≫ prodSnd H G).left.base x ∈ Z
      rw [prodLift_snd]
      exact hx
    · change (sec ≫ act).left.base x = x
      rw [hsec]
      rfl
  have hdisj : Disjoint (closure (act.left.base '' T)) V := by
    refine Disjoint.closure_left ?_ hV
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩
    exact hyp (prodOver H G) (prodFst H G) (prodSnd H G) p hp
  have hCZ := hmax _ hC isClosed_closure hZC hdisj
  rintro _ ⟨w, rfl⟩
  apply hCZ
  apply subset_closure
  refine ⟨(prodLift h z).left.base w, ?_, ?_⟩
  · change (prodLift h z ≫ prodSnd H G).left.base w ∈ Z
    rw [prodLift_snd]
    exact hz ⟨w, rfl⟩
  · rw [hact]
    rfl

end Action

end Langlands.GroupScheme.SplitFactorial
