import Langlands.GroupScheme.ChevalleyIntegral.GenericClosure
import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.VectorScalarKernel

/-! # Additive root maps into the generic Chevalley closure -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  {R R' : CommRingCat.{u}} (ρ : R ⟶ R') (j : J)

/-- The additive root representation respects every homomorphism of base rings. -/
theorem baseChange_rootToGLOver :
    (baseChange (Spec.map ρ)).map (D.rootToGLOver R j) ≫
        (GeneralLinear.baseChangeIso (Fin D.n) (Spec.map ρ)).hom =
      (VectorGroup.baseChangeIso (n := 1) ρ).hom ≫ D.rootToGLOver R' j := by
  refine hom_ext_points fun T t => (GeneralLinear.pointsEquiv (Fin D.n) R' T).injective ?_
  rw [Grp.comp_hom_hom, ← Category.assoc,
    GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp,
    D.pointsEquiv_rootToGLOver, Grp.comp_hom_hom, ← Category.assoc,
    D.pointsEquiv_rootToGLOver]
  congr 1
  change (VectorGroup.coordinates R 1 ((Over.map (Spec.map ρ)).obj T)
      (baseChangePointsEquiv (Spec.map ρ) (GaR R) T t)).toAdd 0 =
    (VectorGroup.coordinates R' 1 T (t ≫ (VectorGroup.baseChangeIso (n := 1) ρ).hom.hom.hom)).toAdd 0
  rw [VectorGroup.coordinates_baseChangeIso_hom]
  rfl

/-- The additive group is flat over every base ring. -/
instance flat_GaR (R : CommRingCat.{u}) : Flat (GaR R).X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 1) R))))
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence.ChevalleyData
open IntegralModel.SchematicClosureConstruction

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K) (j : J)

local instance rootGenericClosed : IsClosedImmersion C.i.hom.hom.left := C.closed

/-- The generic root homomorphism into the specified generic Chevalley group. -/
def genericRoot :
    (baseChange (Spec.algebraMap R K)).obj (GaR (CommRingCat.of R)) ⟶ C.H :=
  (VectorGroup.baseChangeIso (n := 1) (CommRingCat.ofHom (algebraMap R K))).hom ≫ C.u j

theorem genericRoot_comp :
    genericRoot D R K C j ≫ C.i =
      (baseChange (Spec.algebraMap R K)).map (D.rootToGLOver (CommRingCat.of R) j) ≫
        (ambientModel D R K).genericIso.hom := by
  rw [genericRoot, Category.assoc, C.u_comp, ← D.rootToGLOver_eq K]
  exact (D.baseChange_rootToGLOver (CommRingCat.ofHom (algebraMap R K)) j).symm

/-- Each additive root homomorphism factors through the flat schematic closure. -/
theorem exists_rootOver :
    ∃ t : (GaR (CommRingCat.of R)).X ⟶
        (genericModel D R K C).group.X,
      t ≫ (modelInclusion D R K C).hom.hom =
        (D.rootToGLOver (CommRingCat.of R) j).hom.hom := by
  let T := (GaR (CommRingCat.of R))
  have : Flat T.X.hom := flat_GaR (CommRingCat.of R)
  let h := genericRoot D R K C j ≫ (genericModel D R K C).genericIso.inv
  have hh : h ≫ (baseChange (Spec.algebraMap R K)).map (modelInclusion D R K C) =
      (baseChange (Spec.algebraMap R K)).map (D.rootToGLOver (CommRingCat.of R) j) := by
    apply (cancel_mono (ambientModel D R K).genericIso.hom).mp
    dsimp only [h]
    simp only [Category.assoc]
    rw [modelInclusion_generic]
    simp only [Iso.inv_hom_id_assoc]
    exact genericRoot_comp D R K C j
  have : IsClosedImmersion (modelInclusion D R K C).hom.hom.left :=
    modelInclusion_closed D R K C
  refine exists_over_factor_of_schematic_precomp (modelInclusion D R K C).hom.hom
    (GenericSubgroupClosure.genericProjection (K := K) T) _ 
    (baseChangePointsEquiv (Spec.algebraMap R K) (genericModel D R K C).group _ h.hom.hom) ?_
  rw [← baseChangePointsEquiv_comp]
  have hh' := congrArg (fun f => f.hom.hom) hh
  rw [← Grp.comp_hom_hom, hh']
  simpa only [GenericSubgroupClosure.genericProjection, Category.id_comp] using
    (baseChangePointsEquiv_comp (Spec.algebraMap R K)
      (D.rootToGLOver (CommRingCat.of R) j)
      ((baseChange (Spec.algebraMap R K)).obj T).X (𝟙 _)).symm

/-- The chosen factorization of a root homomorphism over the base. -/
def rootOver :
    (GaR (CommRingCat.of R)).X ⟶ (genericModel D R K C).group.X :=
  Classical.choose (exists_rootOver D R K C j)

@[reassoc (attr := simp)]
theorem rootOver_comp :
    rootOver D R K C j ≫ (modelInclusion D R K C).hom.hom =
      (D.rootToGLOver (CommRingCat.of R) j).hom.hom :=
  Classical.choose_spec (exists_rootOver D R K C j)

local instance rootModelClosed :
    IsClosedImmersion (modelInclusion D R K C).hom.hom.left :=
  modelInclusion_closed D R K C

local instance rootModelMono : Mono (modelInclusion D R K C).hom.hom := by
  have : Mono (modelInclusion D R K C).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective
      (IsClosedImmersion.isClosedEmbedding (modelInclusion D R K C).hom.hom.left).injective
  exact Over.mono_of_mono_left _

instance isMonHom_rootOver : IsMonHom (rootOver D R K C j) := by
  have : IsMonHom (rootOver D R K C j ≫ (modelInclusion D R K C).hom.hom) := by
    rw [rootOver_comp]
    infer_instance
  exact isMonHom_of_comp_mono _ (modelInclusion D R K C).hom.hom

/-- The actual additive root homomorphism into the integral model. -/
def root :
    (GaR (CommRingCat.of R)) ⟶ (genericModel D R K C).group :=
  Grp.homMk (rootOver D R K C j)

@[reassoc (attr := simp)]
theorem root_comp :
    root D R K C j ≫ modelInclusion D R K C =
      D.rootToGLOver (CommRingCat.of R) j := by
  apply Grp.hom_ext
  exact rootOver_comp D R K C j

/-- The root factorization is characterized by its matrix representation. -/
theorem root_unique
    (t : (GaR (CommRingCat.of R)) ⟶ (genericModel D R K C).group)
    (ht : t ≫ modelInclusion D R K C = D.rootToGLOver (CommRingCat.of R) j) :
    t = root D R K C j := by
  apply Grp.hom_ext
  apply (cancel_mono (modelInclusion D R K C).hom.hom).mp
  exact (congrArg (fun f => f.hom.hom) ht).trans (rootOver_comp D R K C j).symm

/-- The generic root map is exactly the supplied root map of the chosen Chevalley group. -/
theorem baseChange_root :
    (baseChange (Spec.algebraMap R K)).map (root D R K C j) ≫
        (genericModel D R K C).genericIso.hom = genericRoot D R K C j := by
  have : Mono C.i.hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective (IsClosedImmersion.isClosedEmbedding _).injective
  have : Mono C.i.hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono C.i.hom.hom).mp
  change (((baseChange (Spec.algebraMap R K)).map (root D R K C j) ≫
      (genericModel D R K C).genericIso.hom) ≫ C.i).hom.hom =
    (genericRoot D R K C j ≫ C.i).hom.hom
  rw [Category.assoc, ← modelInclusion_generic, ← Category.assoc, ← Functor.map_comp,
    root_comp, genericRoot_comp]

end Langlands.GroupScheme.ChevalleyIntegral
