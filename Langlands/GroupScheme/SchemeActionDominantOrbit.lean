import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Action kernels and normal subgroup fixedness on dominant orbits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {G H : GroupScheme S} {X : Over S}
variable (a : SchemeAction G X)

/-- The full action kernel: its points act trivially after every refinement
of the test scheme, on every point of the acted-on scheme. -/
def kernel : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over S) (b : T' ⟶ T) (y : T' ⟶ X),
        a.act (b ≫ g) y = y}
      one_mem' := by
        intro T' b y
        rw [MonObj.comp_one, a.act_one]
      mul_mem' := by
        intro g g' hg hg' T' b y
        rw [MonObj.comp_mul, a.act_mul, hg', hg]
      inv_mem' := by
        intro g hg T' b y
        calc
          a.act (b ≫ g⁻¹) y = a.act (b ≫ g⁻¹) (a.act (b ≫ g) y) := by
            rw [hg T' b y]
          _ = a.act ((b ≫ g⁻¹) * (b ≫ g)) y := (a.act_mul _ _ _).symm
          _ = y := by rw [GrpObj.comp_inv, inv_mul_cancel, a.act_one] }
  comp_mem b g hg := by
    intro T'' c y
    simpa only [Category.assoc] using hg T'' (c ≫ b) y

/-- The full action kernel is normal on every test scheme. -/
theorem kernel_isNormal : a.kernel.IsNormal := by
  intro T g h _ hh T' b y
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    a.act_mul, a.act_mul, hh T' b (a.act (b ≫ g)⁻¹ y),
    ← a.act_mul, mul_inv_cancel, a.act_one]

/-- Membership in the full kernel implies fixedness of every scheme-valued point. -/
theorem act_eq_of_mem_kernel {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ a.kernel.carrier T) (y : T ⟶ X) : a.act g y = y := by
  simpa only [Category.id_comp] using hg T (𝟙 T) y

/-- A subgroup lies in the full action kernel exactly when its restricted
action morphism is the second projection. -/
theorem range_le_kernel_iff (j : H ⟶ G) :
    SubgroupFunctor.range j ≤ a.kernel ↔ (a.restrict j).hom = snd H.X X := by
  constructor
  · intro hj
    have hm : (fst H.X X ≫ j.hom.hom) ∈
        (SubgroupFunctor.range j).carrier (H.X ⊗ X) := ⟨fst H.X X, rfl⟩
    have h := a.act_eq_of_mem_kernel (hj (H.X ⊗ X) hm) (snd H.X X)
    rw [← a.restrict_act j] at h
    simpa only [act, lift_fst_snd, Category.id_comp] using h
  · intro he T g hg
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    intro T' b y
    rw [← Category.assoc, ← restrict_act, act, he, lift_snd]

/-- A normal subgroup fixing the orbit's base section fixes every point of
that orbit, with arbitrary scheme tests. -/
theorem restrict_act_orbitMap_eq (j : H ⟶ G)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (x : 𝟙_ (Over S) ⟶ X) (hx : (a.restrict j).IsFixed x)
    {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (a.restrict j).act h (g ≫ a.orbitMap x) = g ≫ a.orbitMap x := by
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.mp
    (hn T g⁻¹ (h ≫ j.hom.hom) (by trivial) ⟨h, rfl⟩)
  have he : (h ≫ j.hom.hom) * g = g * (h' ≫ j.hom.hom) := by
    rw [hh', inv_inv]
    group
  rw [restrict_act, a.comp_orbitMap, ← a.act_mul, he, a.act_mul]
  have hf : a.act (h' ≫ j.hom.hom) (toUnit T ≫ x) = toUnit T ≫ x := by
    simpa only [restrict_act] using hx T (toUnit T) h'
  rw [hf]

section Field

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

/-- Normal subgroup fixedness extends from a quasi-compact dominant orbit to a
reduced separated scheme locally of finite type. -/
theorem restrict_hom_eq_snd_of_dominant_orbit
    [Smooth H.X.hom] [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsSeparated X.hom]
    (j : H ⟶ G) (hn : (SubgroupFunctor.range j).IsNormal)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x)
    [IsDominant (a.orbitMap x).left] [QuasiCompact (a.orbitMap x).left] :
    (a.restrict j).hom = snd H.X X := by
  let q := a.orbitMap x
  let p : H.X ⊗ G.X ⟶ H.X ⊗ X := H.X ◁ q
  have hp : IsPullback (snd H.X G.X).left p.left q.left (snd H.X X).left := by
    apply IsPullback.of_bot (v₂₁ := (fst H.X X).left) (v₂₂ := X.hom)
      (h₃₁ := H.X.hom)
    · simpa only [p, Over.snd_left, Over.fst_left, Over.w q,
        Over.whiskerLeft_left_fst] using
        (IsPullback.of_hasPullback H.X.hom G.X.hom).flip
    · simp only [p, Over.snd_left, Over.whiskerLeft_left_snd]
    · exact (IsPullback.of_hasPullback H.X.hom X.hom).flip
  have : Flat (snd H.X X).left := by
    change Flat (pullback.snd H.X.hom X.hom)
    infer_instance
  have : IsSchemeTheoreticallyDominant q.left :=
    IsSchemeTheoreticallyDominant.of_isDominant q.left
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hp
  have : QuasiCompact p.left :=
    MorphismProperty.of_isPullback hp ‹QuasiCompact q.left›
  have : IsDominant p.left := inferInstance
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : GeometricallyReduced H.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth H.X.hom
  have : IsReduced (H.X ⊗ X).left :=
    inferInstanceAs (IsReduced (pullback H.X.hom X.hom))
  have he : p ≫ (a.restrict j).hom = p ≫ snd H.X X := by
    have h := a.restrict_act_orbitMap_eq j hn x hx
      (fst H.X G.X) (snd H.X G.X)
    have hp' : lift (fst H.X G.X) (snd H.X G.X ≫ q) = p := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [p]
    rw [← hp', lift_snd]
    exact h
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated X.hom
    ((Over.w _).trans (Over.w _).symm) p.left
    (congrArg (fun f => f.left) he)

/-- The normal subgroup fixing the base point of a quasi-compact dominant orbit
lies in the full action kernel. -/
theorem range_le_kernel_of_dominant_orbit
    [Smooth H.X.hom] [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsSeparated X.hom]
    (j : H ⟶ G) (hn : (SubgroupFunctor.range j).IsNormal)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x)
    [IsDominant (a.orbitMap x).left] [QuasiCompact (a.orbitMap x).left] :
    SubgroupFunctor.range j ≤ a.kernel :=
  (a.range_le_kernel_iff j).2 (a.restrict_hom_eq_snd_of_dominant_orbit j hn x hx)

end Field

end Langlands.GroupScheme.SchemeAction
