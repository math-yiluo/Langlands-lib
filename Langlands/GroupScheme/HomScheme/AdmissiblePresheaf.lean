import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Descent.ClosedSubgroupIdeals
import Langlands.CategoryTheory.OverTotalPresheaf
import Mathlib.Logic.Small.Basic

/-! # The small presheaf of actual closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Admissible actual subgroup functors, with their all-test meaning. -/
abbrev AdmissibleSubgroup (G : GroupScheme S) :=
  {F : SubgroupFunctor G // IsAdmissible F}

/-- An actual representative of an admissible subgroup functor. -/
structure AdmissibleRepresentative (F : AdmissibleSubgroup G) where
  group : GroupScheme S
  hom : group ⟶ G
  closed : IsClosedSubgroup hom
  torus : RelativeTorus.IsTorus group
  represents : F.val.IsRepresentedBy hom

/-- Choose an actual closed torus representative. -/
def admissibleRepresentative (F : AdmissibleSubgroup G) : AdmissibleRepresentative F :=
  Classical.choice (by
    obtain ⟨K, j, hj, hK, hF⟩ := F.property
    exact ⟨⟨K, j, hj, hK, hF⟩⟩)

/-- The full kernel ideal of the chosen actual representative. -/
def admissibleIdeal (F : AdmissibleSubgroup G) : G.X.left.IdealSheafData :=
  (admissibleRepresentative F).hom.hom.hom.left.ker

/-- A closed subgroup functor is determined by its full defining ideal. -/
theorem admissibleIdeal_injective :
    Function.Injective (admissibleIdeal (G := G)) := by
  intro F F' h
  apply Subtype.ext
  rw [← (admissibleRepresentative F).represents.2,
    ← (admissibleRepresentative F').represents.2]
  ext T x
  rw [(admissibleRepresentative F).closed.mem_range_iff_ker_le,
    (admissibleRepresentative F').closed.mem_range_iff_ker_le]
  exact congrArg (fun I => I ≤ x.left.ker) h |>.to_iff

/-- Actual admissible subgroups have the universe of the base scheme. -/
instance admissibleSubgroupSmall : Small.{u} (AdmissibleSubgroup G) :=
  small_of_injective admissibleIdeal_injective

variable {M T U : Over S}
variable {K L : GroupScheme M.left}

/-- Evaluation depends only on the actual all-test range of the family. -/
theorem evaluate_eq_of_range_eq
    (i : K ⟶ (baseChange M.hom).obj G)
    (j : L ⟶ (baseChange M.hom).obj G)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j) (a : T ⟶ M) :
    evaluate i a = evaluate j a := by
  simp only [evaluate, familyHom, SubgroupFunctor.range_comp_iso,
    SubgroupFunctor.range_baseChangeHom, h]

/-- Identity evaluation is the original actual inclusion up to the canonical
source pullback comparison. -/
theorem familyHom_id (j : K ⟶ (baseChange M.hom).obj G) :
    familyHom j (𝟙 M) = (baseChangeIdIso K).hom ≫ j := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [familyHom_original, Grp.comp_hom_hom, Over.comp_left,
      baseChangeIdIso_hom_left, Over.id_left, Category.assoc]
  · exact (Over.w (familyHom j (𝟙 M)).hom.hom).trans
      (Over.w ((baseChangeIdIso K).hom ≫ j).hom.hom).symm

/-- Identity evaluation preserves the literal all-test subgroup functor. -/
@[simp]
theorem evaluate_id (j : K ⟶ (baseChange M.hom).obj G) :
    evaluate j (𝟙 M) = SubgroupFunctor.range j := by
  rw [evaluate, familyHom_id]
  exact SubgroupFunctor.range_iso_comp (baseChangeIdIso K) j

/-- Restriction of an admissible subgroup by actual family evaluation. -/
def restrict (a : T ⟶ M)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G)) :
    AdmissibleSubgroup ((baseChange T.hom).obj G) :=
  ⟨evaluate (admissibleRepresentative F).hom a,
    isAdmissible_evaluate _ (admissibleRepresentative F).closed
      (admissibleRepresentative F).torus a⟩

/-- Restriction is evaluation of every actual representative, independent of
the chosen representative. -/
theorem restrict_eq_evaluate
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G))
    (j : K ⟶ (baseChange M.hom).obj G)
    (h : SubgroupFunctor.range j = F.val) (a : T ⟶ M) :
    (restrict a F).val = evaluate j a :=
  evaluate_eq_of_range_eq _ _ ((admissibleRepresentative F).represents.2.trans h.symm) a

@[simp]
theorem restrict_id (F : AdmissibleSubgroup ((baseChange M.hom).obj G)) :
    restrict (𝟙 M) F = F := by
  apply Subtype.ext
  exact (evaluate_id _).trans (admissibleRepresentative F).represents.2

/-- Successive restriction is direct restriction on all actual test schemes. -/
theorem restrict_comp (a : T ⟶ M) (b : U ⟶ T)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G)) :
    restrict b (restrict a F) = restrict (b ≫ a) F := by
  apply Subtype.ext
  calc
    (restrict b (restrict a F)).val =
        evaluate (familyHom (admissibleRepresentative F).hom a) b :=
      restrict_eq_evaluate _ _ rfl b
    _ = (restrict (b ≫ a) F).val := evaluate_comp _ a b

/-- The presheaf of actual admissible subgroup functors, before shrinking. -/
def admissiblePresheaf (G : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := AdmissibleSubgroup ((baseChange T.unop.hom).obj G)
  map a := TypeCat.ofHom (restrict a.unop)
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext F
    exact restrict_id F
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext F
    exact (restrict_comp a.unop b.unop F).symm

/-- The same actual subgroup presheaf with values in `Type u`. -/
def smallAdmissiblePresheaf (G : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (AdmissibleSubgroup ((baseChange T.unop.hom).obj G))
  map {T T'} a := TypeCat.ofHom fun F =>
    equivShrink _ (restrict a.unop ((equivShrink _).symm F))
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext F
    simp only [unop_id, restrict_id, Equiv.apply_symm_apply]
    rfl
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext F
    simp only [TypeCat.homEquiv_apply, types_comp_apply, TypeCat.ofHom_apply,
      unop_comp, Equiv.symm_apply_apply, restrict_comp]

/-- Decode a small section as its actual admissible subgroup. -/
def smallAdmissibleEquiv (G : GroupScheme S) (T : Over S) :
    (smallAdmissiblePresheaf G).obj (op T) ≃
      AdmissibleSubgroup ((baseChange T.hom).obj G) :=
  (equivShrink _).symm

/-- Shrinking commutes with actual subgroup restriction. -/
@[simp]
theorem smallAdmissibleEquiv_map (a : T ⟶ M)
    (F : (smallAdmissiblePresheaf G).obj (op M)) :
    smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op F) =
      restrict a (smallAdmissibleEquiv G M F) :=
  (equivShrink _).symm_apply_apply _

/-- The absolute presheaf remembers the base map and the actual subgroup. -/
def totalAdmissiblePresheaf (G : GroupScheme S) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  (smallAdmissiblePresheaf G).overTotal

end Langlands.GroupScheme.TorusSubgroupModuli
