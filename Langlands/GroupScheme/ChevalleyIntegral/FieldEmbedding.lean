import Langlands.GroupScheme.ChevalleyIntegral.FieldSubgroup
import Langlands.GroupScheme.ChevalleyIntegral.TorusClosure
import Langlands.GroupScheme.ChevalleyIntegral.RootClosure
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Closed Chevalley subgroups in every field fibre -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  (k : Type u) [Field k] (ρ : CommRingCat.of R ⟶ CommRingCat.of k)

/-- The fibre of the one fixed integral model at a specified field-valued point. -/
abbrev fieldModel : GroupScheme (Spec (CommRingCat.of k)) :=
  (baseChange (Spec.map ρ)).obj (genericModel D R K C).group

/-- The closed matrix representation of this field fibre. -/
def fieldInclusion : fieldModel D R K C k ρ ⟶ D.GLk k :=
  (baseChange (Spec.map ρ)).map (modelInclusion D R K C) ≫
    (GeneralLinear.baseChangeIso (Fin D.n) (Spec.map ρ)).hom

theorem fieldInclusion_closed : IsClosedSubgroup (fieldInclusion D R K C k ρ) :=
  ((modelInclusion_closed D R K C).baseChange (Spec.map ρ)).comp_iso
    (GeneralLinear.baseChangeIso (Fin D.n) (Spec.map ρ))

/-- The integral torus, expressed over the field by the canonical source comparison. -/
def fieldTorus :
    (Tk (X := X) k).toGrp ⟶ fieldModel D R K C k ρ :=
  (Diagonalizable.baseChangeIso (Spec.map ρ) X).inv ≫
    (baseChange (Spec.map ρ)).map (torus D R K C)

@[reassoc (attr := simp)]
theorem fieldTorus_comp :
    fieldTorus D R K C k ρ ≫ fieldInclusion D R K C k ρ = D.torusToGL k := by
  dsimp only [fieldTorus, fieldInclusion]
  rw [Category.assoc, ← Category.assoc ((baseChange _).map _), ← Functor.map_comp,
    torus_comp, D.baseChange_torusToGLOver, Iso.inv_hom_id_assoc,
    D.torusToGLOver_eq]

/-- The integral root maps, expressed over the field by the additive source comparison. -/
def fieldRoot (j : J) : Gak k ⟶ fieldModel D R K C k ρ :=
  (VectorGroup.baseChangeIso (n := 1) ρ).inv ≫
    (baseChange (Spec.map ρ)).map (root D R K C j)

@[reassoc (attr := simp)]
theorem fieldRoot_comp (j : J) :
    fieldRoot D R K C k ρ j ≫ fieldInclusion D R K C k ρ = D.rootToGL k j := by
  dsimp only [fieldRoot, fieldInclusion]
  rw [Category.assoc, ← Category.assoc ((baseChange _).map _), ← Functor.map_comp,
    root_comp, D.baseChange_rootToGLOver, Iso.inv_hom_id_assoc,
    D.rootToGLOver_eq]

theorem torus_range_le_fieldInclusion :
    SubgroupFunctor.range (D.torusToGL k) ≤
      SubgroupFunctor.range (fieldInclusion D R K C k ρ) := by
  rw [← fieldTorus_comp D R K C k ρ]
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨y ≫ (fieldTorus D R K C k ρ).hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩

theorem root_range_le_fieldInclusion (j : J) :
    SubgroupFunctor.range (D.rootToGL k j) ≤
      SubgroupFunctor.range (fieldInclusion D R K C k ρ) := by
  rw [← fieldRoot_comp D R K C k ρ j]
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨y ≫ (fieldRoot D R K C k ρ j).hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩

variable (H : D.ChevGroup k)

/-- Every actual field Chevalley group embeds in the corresponding fibre of
the single integral model. -/
def fieldEmbedding : H.H ⟶ fieldModel D R K C k ρ :=
  H.factorOfGenerators (fieldInclusion D R K C k ρ)
    (fieldInclusion_closed D R K C k ρ)
    (torus_range_le_fieldInclusion D R K C k ρ)
    (root_range_le_fieldInclusion D R K C k ρ)

@[reassoc (attr := simp)]
theorem fieldEmbedding_comp :
    fieldEmbedding D R K C k ρ H ≫ fieldInclusion D R K C k ρ = H.i :=
  H.factorOfGenerators_comp _ _ _ _

theorem fieldEmbedding_closed :
    IsClosedSubgroup (fieldEmbedding D R K C k ρ H) :=
  H.factorOfGenerators_closed _ _ _ _

local instance fieldInclusionMono :
    Mono (fieldInclusion D R K C k ρ).hom.hom := by
  have : IsClosedImmersion (fieldInclusion D R K C k ρ).hom.hom.left :=
    fieldInclusion_closed D R K C k ρ
  have : Mono (fieldInclusion D R K C k ρ).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective
      (IsClosedImmersion.isClosedEmbedding _).injective
  exact Over.mono_of_mono_left _

/-- The closed embedding identifies the supplied field torus with the integral one. -/
@[reassoc (attr := simp)]
theorem torus_fieldEmbedding :
    H.t ≫ fieldEmbedding D R K C k ρ H = fieldTorus D R K C k ρ := by
  apply Grp.hom_ext
  apply (cancel_mono (fieldInclusion D R K C k ρ).hom.hom).mp
  change ((H.t ≫ fieldEmbedding D R K C k ρ H) ≫
      fieldInclusion D R K C k ρ).hom.hom =
    (fieldTorus D R K C k ρ ≫ fieldInclusion D R K C k ρ).hom.hom
  rw [Category.assoc, fieldEmbedding_comp, H.t_comp, fieldTorus_comp]

/-- The closed embedding identifies every supplied field root map with the integral one. -/
@[reassoc (attr := simp)]
theorem root_fieldEmbedding (j : J) :
    H.u j ≫ fieldEmbedding D R K C k ρ H = fieldRoot D R K C k ρ j := by
  apply Grp.hom_ext
  apply (cancel_mono (fieldInclusion D R K C k ρ).hom.hom).mp
  change ((H.u j ≫ fieldEmbedding D R K C k ρ H) ≫
      fieldInclusion D R K C k ρ).hom.hom =
    (fieldRoot D R K C k ρ j ≫ fieldInclusion D R K C k ρ).hom.hom
  rw [Category.assoc, fieldEmbedding_comp, H.u_comp, fieldRoot_comp]

end Langlands.GroupScheme.ChevalleyIntegral
