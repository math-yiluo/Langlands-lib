import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Langlands.GroupScheme.FiniteTypeMonomorphismProof
import Langlands.GroupScheme.DvrGenericAffinenessStatement
import Langlands.GroupScheme.Reductive.MonomorphismValuativeReductionStatement

/-! # The conditional affine-target reduction over a DVR -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.DvrAffineClosureReduction

/-- An affine flat closed target through which the original map factors,
with its exact generic identification and schematic-closure ideal. -/
structure Data {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (M G : GroupScheme (Spec (CommRingCat.of R))) (f : M ⟶ G) where
  target : GroupScheme (Spec (CommRingCat.of R))
  flat : Flat target.X.hom
  isAffineHom : IsAffineHom target.X.hom
  locallyOfFiniteType : LocallyOfFiniteType target.X.hom
  quasiCompact : QuasiCompact target.X.hom
  inclusion : target ⟶ G
  inclusion_isClosedImmersion : IsClosedImmersion inclusion.hom.hom.left
  factor : M ⟶ target
  factor_mono : Mono factor.hom.hom.left
  factor_fac : factor ≫ inclusion = f
  genericIso :
    (baseChange (Spec.algebraMap R K)).obj M ≅
      (baseChange (Spec.algebraMap R K)).obj target
  baseChange_factor :
    (baseChange (Spec.algebraMap R K)).map factor = genericIso.hom
  inclusion_ker :
    inclusion.hom.hom.left.ker =
      (GenericSubgroupClosure.genericOver G
        ((baseChange (Spec.algebraMap R K)).map f)).left.ker

/-- Closedness can be checked after replacing the target by the affine closure. -/
theorem Data.isClosedImmersion_iff {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))} {f : M ⟶ G}
    (D : Data (K := K) M G f) :
    IsClosedImmersion f.hom.hom.left ↔ IsClosedImmersion D.factor.hom.hom.left := by
  have := D.inclusion_isClosedImmersion
  have hfac : D.factor.hom.hom.left ≫ D.inclusion.hom.hom.left = f.hom.hom.left :=
    congrArg (fun t => t.hom.hom.left) D.factor_fac
  constructor
  · intro hf
    have : IsClosedImmersion (D.factor.hom.hom.left ≫ D.inclusion.hom.hom.left) :=
      hfac.symm ▸ hf
    exact IsClosedImmersion.of_comp _ D.inclusion.hom.hom.left
  · intro ha
    rw [← hfac]
    exact IsClosedImmersion.comp _ _

/-- The generic base change of a monomorphism of the indicated finite-type
groups is closed, by the published arbitrary-field theorem. -/
theorem genericMap_isClosedImmersion
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left] :
    IsClosedImmersion ((baseChange (Spec.algebraMap R K)).map f).hom.hom.left := by
  let F := baseChange (Spec.algebraMap R K)
  have : LocallyOfFiniteType (F.obj M).X.hom := by
    change LocallyOfFiniteType (pullback.snd M.X.hom (Spec.algebraMap R K))
    infer_instance
  have : IsAffineHom (F.obj M).X.hom := by
    change IsAffineHom (pullback.snd M.X.hom (Spec.algebraMap R K))
    infer_instance
  have : LocallyOfFiniteType (F.obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (Spec.algebraMap R K))
    infer_instance
  have : QuasiCompact (F.obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom (Spec.algebraMap R K))
    infer_instance
  have : IsSeparated (F.obj G).X.hom := by
    change IsSeparated (pullback.snd G.X.hom (Spec.algebraMap R K))
    infer_instance
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : Mono (F.map f).hom.hom.left := by
    change Mono ((Over.pullback (Spec.algebraMap R K)).map f.hom.hom).left
    infer_instance
  exact finiteTypeMonomorphism K (F.obj M) (F.obj G) (F.map f)

/-- Raynaud's criterion, supplied as an explicit premise, makes the actual
schematic closure of the generic image an affine flat target. -/
def affineClosure (raynaud : DvrGenericAffinenessStatement.{u})
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Flat M.X.hom] [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left] : Data (K := K) M G f := by
  let F := baseChange (Spec.algebraMap R K)
  let j := F.map f
  have : IsClosedImmersion j.hom.hom.left := genericMap_isClosedImmersion f
  let C := GenericSubgroupClosure.closureGroup G j
  let a := GenericSubgroupClosure.factor G j f (𝟙 _) (by simp [j, F])
  let e := GenericSubgroupClosure.genericToClosureIso G j
  have : IsAffineHom (F.obj M).X.hom := by
    change IsAffineHom (pullback.snd M.X.hom (Spec.algebraMap R K))
    infer_instance
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  have hgeneric : IsAffineHom (F.obj C).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  have hC : IsAffineHom C.X.hom :=
    (raynaud R K C inferInstance inferInstance inferInstance hgeneric).mpr inferInstance
  exact
    { target := C
      flat := inferInstance
      isAffineHom := hC
      locallyOfFiniteType := inferInstance
      quasiCompact := inferInstance
      inclusion := GenericSubgroupClosure.closureInclusion G j
      inclusion_isClosedImmersion := inferInstance
      factor := a
      factor_mono := inferInstance
      factor_fac := GenericSubgroupClosure.factor_fac G j f (𝟙 _) (by simp [j, F])
      genericIso := e
      baseChange_factor := by
        change F.map (GenericSubgroupClosure.factor G j f (𝟙 _) _) = e.hom
        rw [GenericSubgroupClosure.baseChange_factor, Category.id_comp]
      inclusion_ker := GenericSubgroupClosure.inclusionOver_ker G j }

/-- The remaining DVR assertion when the target is flat affine of finite type. -/
def FlatAffineCase : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (M G : GroupScheme (Spec (CommRingCat.of R))), IsReductive M →
    Flat G.X.hom → IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    QuasiCompact G.X.hom →
    ∀ f : M ⟶ G, Mono f.hom.hom.left → IsClosedImmersion f.hom.hom.left

/-- Conditional on Raynaud, the flat affine target case implies the full DVR case. -/
theorem dvrCase_of_flatAffineCase (raynaud : DvrGenericAffinenessStatement.{u})
    (h : FlatAffineCase.{u}) : ReductiveMonomorphismValuativeReduction.DvrCase.{u} := by
  intro R _ _ _ M G hM hsep hfp hqc f hf
  have := hM.smooth
  have := hM.isAffineHom
  let D := affineClosure (K := FractionRing R) raynaud f
  exact D.isClosedImmersion_iff.mpr
    (h R M D.target hM D.flat D.isAffineHom D.locallyOfFiniteType D.quasiCompact
      D.factor D.factor_mono)

end Langlands.GroupScheme.DvrAffineClosureReduction
