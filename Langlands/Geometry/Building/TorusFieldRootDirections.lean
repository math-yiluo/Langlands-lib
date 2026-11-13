import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Root directions under torus restriction and field descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
  (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "iT_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

private instance rootDirectionsAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance rootDirectionsFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- A nonzero restriction of an upper root direction is exactly the pullback
of an actual lower root form on the original real cocharacter space. -/
theorem exists_rootForm_comp_torusFieldTranslationMap
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K)
    (hne : (rootForm (k := K) (S := T_K) (G := G_K) iT_K β).comp
      (torusFieldTranslationMap k K f iT hS) ≠ 0) :
    ∃ α : relativeRoots (k := k) (T := S) (G := G) iS,
      (rootForm (k := k) (S := S) (G := G) iS α).comp (rootAnnihilator iS).mkQ =
        (rootForm (k := K) (S := T_K) (G := G_K) iT_K β).comp
          (torusFieldTranslationMap k K f iT hS) := by
  let χ : characterLattice S :=
    (characterLattice.baseChangeEquiv b S hS).symm (f_K ≫ β.val)
  have hχ : characterLattice.baseChange b S χ = f_K ≫ β.val :=
    (characterLattice.baseChangeEquiv b S hS).apply_symm_apply _
  have heval (v : V S) :
      (rootForm (k := K) (S := T_K) (G := G_K) iT_K β).comp
          (torusFieldTranslationMap k K f iT hS) v =
        eval S χ v := by
    change eval T_K β.val (descentCocharacterMap k K f hS v) = _
    rw [eval_descentCocharacterMap, ← hχ, eval_splitCocharacterBaseChange]
  have hχ0 : f_K ≫ β.val ≠ 0 := by
    intro hz
    apply hne
    apply LinearMap.ext
    intro v
    rw [heval]
    have hzero : χ = 0 :=
      (characterLattice.baseChangeEquiv b S hS).injective (by
        simpa only [characterLattice.baseChangeEquiv_apply, map_zero] using hχ.trans hz)
    rw [hzero, eval_eq_pair]
    simp
  have hroot : f_K ≫ β.val ∈ relativeRoots
      (CommGroupScheme.groupHom f_K ≫ iT_K) :=
    (rootRestriction f_K iT_K ⟨β.val, β.property, hχ0⟩).property
  have hfactor : CommGroupScheme.groupHom f_K ≫ iT_K =
      (GroupScheme.baseChange b).map iS := by
    rw [← hf, CategoryTheory.Functor.map_comp]
    rfl
  have hχroot : χ ∈ relativeRoots (k := k) (T := S) (G := G) iS := by
    apply (mem_roots_baseChange_iff (K := K) G S hS iS χ).mp
    rw [hχ, ← hfactor]
    exact hroot
  refine ⟨⟨χ, hχroot⟩, ?_⟩
  apply LinearMap.ext
  intro v
  exact (heval v).symm

/-- Choose the actual lower root with the specified nonzero upper pullback form. -/
def torusFieldRootOfNonzeroForm
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K)
    (hne : (rootForm (S := T_K) iT_K β).comp
      (torusFieldTranslationMap k K f iT hS) ≠ 0) : relativeRoots iS :=
  (exists_rootForm_comp_torusFieldTranslationMap hS f iS iT hf β hne).choose

/-- The chosen root has exactly the prescribed pulled-back form. -/
theorem torusFieldRootOfNonzeroForm_spec
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K)
    (hne : (rootForm (S := T_K) iT_K β).comp
      (torusFieldTranslationMap k K f iT hS) ≠ 0) :
    (rootForm iS (torusFieldRootOfNonzeroForm hS f iS iT hf β hne)).comp
        (rootAnnihilator iS).mkQ =
      (rootForm (S := T_K) iT_K β).comp (torusFieldTranslationMap k K f iT hS) :=
  (exists_rootForm_comp_torusFieldTranslationMap hS f iS iT hf β hne).choose_spec

/-- Every upper affine-root derivative with nonzero pullback has an actual
lower root with the identical pulled-back form, and hence the identical kernel. -/
theorem exists_rootForm_comp_of_affineRoot
    [Mono (CategoryTheory.Functor.map (GroupScheme.baseChange b) iT).hom.hom.left]
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    {ω : Kˣ → ℝ} (D : KPApartmentData (k := K) (S := T_K) (G := G_K) iT_K ω)
    (ψ : D.affineRoots)
    (hne : ψ.val.linear.comp (torusFieldTranslationMap k K f iT hS) ≠ 0) :
    ∃ α : relativeRoots (k := k) (T := S) (G := G) iS,
      (rootForm (k := k) (S := S) (G := G) iS α).comp (rootAnnihilator iS).mkQ =
        ψ.val.linear.comp (torusFieldTranslationMap k K f iT hS) := by
  obtain ⟨β, hβ, -⟩ := ψ.property
  rw [hβ] at hne ⊢
  exact exists_rootForm_comp_torusFieldTranslationMap hS f iS iT hf β hne

end Langlands.Geometry.Building
