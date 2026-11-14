import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.RelativeLevi.ParabolicSchemeStatement
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf

/-! # The presheaf of actual relative parabolic subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- A subgroup functor is parabolic when an actual relative parabolic represents it. -/
def IsParabolic (F : SubgroupFunctor G) : Prop :=
  ∃ (P : GroupScheme S) (j : P ⟶ G),
    IsRelativeParabolicSubgroup j ∧ F.IsRepresentedBy j

/-- The actual range of a relative parabolic is parabolic. -/
theorem isParabolic_range {P : GroupScheme S} (j : P ⟶ G)
    (hj : IsRelativeParabolicSubgroup j) : IsParabolic (SubgroupFunctor.range j) :=
  ⟨P, j, hj, hj.mono, rfl⟩

/-- Parabolic subgroup functors remain parabolic after actual base change. -/
theorem IsParabolic.baseChange {F : SubgroupFunctor G} (hF : IsParabolic F)
    (hG : IsReductive G) (b : S' ⟶ S) : IsParabolic (F.baseChange b) := by
  obtain ⟨P, j, hj, hF⟩ := hF
  exact ⟨(GroupScheme.baseChange b).obj P, (GroupScheme.baseChange b).map j,
    hj.baseChange hG b,
    hF.baseChange b⟩

/-- Actual parabolic subgroup functors, without a choice of presentation. -/
abbrev ParabolicSubgroup (G : GroupScheme S) :=
  {F : SubgroupFunctor G // IsParabolic F}

/-- An actual relative-parabolic representative of a subgroup functor. -/
structure ParabolicRepresentative (F : ParabolicSubgroup G) where
  group : GroupScheme S
  hom : group ⟶ G
  parabolic : IsRelativeParabolicSubgroup hom
  represents : F.val.IsRepresentedBy hom

/-- Choose an actual relative-parabolic representative. -/
def parabolicRepresentative (F : ParabolicSubgroup G) : ParabolicRepresentative F :=
  Classical.choice (by
    obtain ⟨P, j, hj, hF⟩ := F.property
    exact ⟨⟨P, j, hj, hF⟩⟩)

variable {M T U : Over S} {P : GroupScheme M.left}

/-- Evaluation of a relative-parabolic family is relative parabolic. -/
theorem isRelativeParabolicSubgroup_familyHom (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    (a : T ⟶ M) : IsRelativeParabolicSubgroup (familyHom j a) :=
  (hj.baseChange (hG.baseChange M.hom) a.left).comp_iso
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G)

/-- Evaluation of a relative-parabolic family is a parabolic subgroup functor. -/
theorem isParabolic_evaluate (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    (a : T ⟶ M) : IsParabolic (evaluate j a) :=
  isParabolic_range _ (isRelativeParabolicSubgroup_familyHom hG j hj a)

/-- Restrict an actual parabolic subgroup using actual family evaluation. -/
def restrict (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    ParabolicSubgroup ((baseChange T.hom).obj G) :=
  ⟨evaluate (parabolicRepresentative F).hom a,
    isParabolic_evaluate hG _ (parabolicRepresentative F).parabolic a⟩

/-- Restriction evaluates every actual representative, independently of the chosen one. -/
theorem restrict_eq_evaluate (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (j : P ⟶ (baseChange M.hom).obj G)
    (h : SubgroupFunctor.range j = F.val) (a : T ⟶ M) :
    (restrict hG a F).val = evaluate j a :=
  evaluate_eq_of_range_eq _ _ ((parabolicRepresentative F).represents.2.trans h.symm) a

@[simp]
theorem restrict_id (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    restrict hG (𝟙 M) F = F := by
  apply Subtype.ext
  exact (evaluate_id _).trans (parabolicRepresentative F).represents.2

/-- Successive restriction is direct restriction on every test scheme. -/
theorem restrict_comp (hG : IsReductive G) (a : T ⟶ M) (b : U ⟶ T)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    restrict hG b (restrict hG a F) = restrict hG (b ≫ a) F := by
  apply Subtype.ext
  calc
    (restrict hG b (restrict hG a F)).val =
        evaluate (familyHom (parabolicRepresentative F).hom a) b :=
      restrict_eq_evaluate hG _ _ rfl b
    _ = (restrict hG (b ≫ a) F).val := evaluate_comp _ a b

/-- The presheaf of actual parabolic subgroup functors of a reductive group scheme.
It takes values in `Type (u + 1)` and needs no smallness or closedness premise. -/
def parabolicPresheaf (G : GroupScheme S) (hG : IsReductive G) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ParabolicSubgroup ((baseChange T.unop.hom).obj G)
  map a := TypeCat.ofHom (restrict hG a.unop)
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext F
    exact restrict_id hG F
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext F
    exact (restrict_comp hG a.unop b.unop F).symm

/-- A family is universal when it evaluates to each actual parabolic subgroup
functor at a unique parameter morphism. -/
def IsUniversal (j : P ⟶ (baseChange M.hom).obj G) : Prop :=
  ∀ (T : Over S) (F : SubgroupFunctor ((baseChange T.hom).obj G)),
    IsParabolic F → ∃! a : T ⟶ M, evaluate j a = F

/-- Universality on subgroup functors is exactly universality on actual
relative-parabolic inclusions, as used in the published target. -/
theorem isUniversal_iff (j : P ⟶ (baseChange M.hom).obj G) :
    IsUniversal j ↔
      ∀ (T : Over S) (Q : GroupScheme T.left)
        (i : Q ⟶ (baseChange T.hom).obj G),
        IsRelativeParabolicSubgroup i →
          ∃! a : T ⟶ M, evaluate j a = SubgroupFunctor.range i := by
  constructor
  · intro h T Q i hi
    exact h T _ (isParabolic_range i hi)
  · intro h T F hF
    obtain ⟨Q, i, hi, hFi⟩ := hF
    rw [← hFi.2]
    exact h T Q i hi

/-- A representing object carries an actual universal relative-parabolic family. -/
theorem exists_universal_of_representableBy (hG : IsReductive G) {M : Over S}
    (e : (parabolicPresheaf G hG).RepresentableBy M) :
    ∃ (P : GroupScheme M.left) (j : P ⟶ (baseChange M.hom).obj G),
      IsRelativeParabolicSubgroup j ∧ IsUniversal j := by
  let F : ParabolicSubgroup ((baseChange M.hom).obj G) := e.homEquiv (𝟙 M)
  let r := parabolicRepresentative F
  have he {T : Over S} (a : T ⟶ M) :
      evaluate r.hom a = (e.homEquiv a).val := by
    rw [e.homEquiv_eq]
    exact (restrict_eq_evaluate hG F r.hom r.represents.2 a).symm
  refine ⟨r.group, r.hom, r.parabolic, ?_⟩
  intro T F' hF'
  let x : (parabolicPresheaf G hG).obj (op T) := ⟨F', hF'⟩
  refine ⟨e.homEquiv.symm x, ?_, ?_⟩
  · change evaluate r.hom (e.homEquiv.symm x) = F'
    rw [he, Equiv.apply_symm_apply]
  · intro b hb
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext ((he b).symm.trans hb)

/-- Evaluation of a universal relative-parabolic family is a bijection on
every actual test scheme. -/
def parameterEquiv (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    (hu : IsUniversal j) (T : Over S) :
    (T ⟶ M) ≃ ParabolicSubgroup ((baseChange T.hom).obj G) where
  toFun a := ⟨evaluate j a, isParabolic_evaluate hG j hj a⟩
  invFun F := (hu T F.val F.property).choose
  left_inv a := by
    exact ((hu T (evaluate j a) (isParabolic_evaluate hG j hj a)).choose_spec.2 a
      rfl).symm
  right_inv F := by
    apply Subtype.ext
    exact (hu T F.val F.property).choose_spec.1

/-- An actual universal relative-parabolic family represents the presheaf. -/
def representableBy_of_isUniversal (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    (hu : IsUniversal j) : (parabolicPresheaf G hG).RepresentableBy M where
  homEquiv {T} := parameterEquiv hG j hj hu T
  homEquiv_comp {T U} a b := by
    apply Subtype.ext
    change evaluate j (a ≫ b) =
      (restrict hG a ⟨evaluate j b, isParabolic_evaluate hG j hj b⟩).val
    exact (restrict_eq_evaluate hG _ (familyHom j b) rfl a).trans
      (evaluate_comp j b a) |>.symm

/-- For a fixed parameter scheme, representability and an actual universal
relative-parabolic family are equivalent. -/
theorem representableBy_iff_exists_universal (hG : IsReductive G) (M : Over S) :
    Nonempty ((parabolicPresheaf G hG).RepresentableBy M) ↔
      ∃ (P : GroupScheme M.left) (j : P ⟶ (baseChange M.hom).obj G),
        IsRelativeParabolicSubgroup j ∧ IsUniversal j := by
  constructor
  · rintro ⟨e⟩
    exact exists_universal_of_representableBy hG e
  · rintro ⟨P, j, hj, hu⟩
    exact ⟨representableBy_of_isUniversal hG j hj hu⟩

/-- The unchanged published target is equivalent to smooth proper
representability of the actual parabolic presheaf. -/
theorem relativeParabolicSchemeStatement_iff :
    RelativeParabolicSchemeStatement.{u} ↔
      ∀ (S : Scheme.{u}) (G : GroupScheme S) (hG : IsReductive G),
        ∃ M : Over S, Nonempty ((parabolicPresheaf G hG).RepresentableBy M) ∧
          Smooth M.hom ∧ IsProper M.hom := by
  constructor
  · intro h S G hG
    obtain ⟨M, P, j, hj, hu, hs, hp⟩ := h S G hG
    exact ⟨M, ⟨representableBy_of_isUniversal hG j hj ((isUniversal_iff j).mpr hu)⟩,
      hs, hp⟩
  · intro h S G hG
    obtain ⟨M, ⟨e⟩, hs, hp⟩ := h S G hG
    obtain ⟨P, j, hj, hu⟩ := exists_universal_of_representableBy hG e
    exact ⟨M, P, j, hj, (isUniversal_iff j).mp hu, hs, hp⟩

end Langlands.GroupScheme.ParabolicSubgroupModuli
