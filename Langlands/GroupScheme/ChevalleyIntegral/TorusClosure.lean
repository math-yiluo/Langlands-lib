import Langlands.GroupScheme.ChevalleyIntegral.GenericClosure
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange

/-! # The full-lattice torus in the generic Chevalley closure -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  {R R' : CommRingCat.{u}} (a : Spec R' ⟶ Spec R)

/-- The diagonal matrix representation respects arbitrary base change. -/
theorem baseChange_torusToGLOver :
    (baseChange a).map (D.torusToGLOver R) ≫
        (GeneralLinear.baseChangeIso (Fin D.n) a).hom =
      (Diagonalizable.baseChangeIso a X).hom ≫ D.torusToGLOver R' := by
  refine hom_ext_points fun T t => (GeneralLinear.pointsEquiv (Fin D.n) R' T).injective ?_
  rw [Grp.comp_hom_hom, ← Category.assoc,
    GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp,
    D.pointsEquiv_torusToGLOver, Grp.comp_hom_hom, ← Category.assoc,
    D.pointsEquiv_torusToGLOver]
  congr 1
  exact (Diagonalizable.characterPointsEquiv_baseChangeIso_hom a X T t).symm

/-- A diagonalizable group has a flat structure morphism over every ring. -/
instance flat_TR (R : CommRingCat.{u}) :
    Flat (TR (X := X) R).toGrp.X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
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
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)

local instance torusGenericClosed : IsClosedImmersion C.i.hom.hom.left := C.closed

/-- The generic torus mapped into the specified generic Chevalley group. -/
def genericTorus :
    (baseChange (Spec.algebraMap R K)).obj (TR (X := X) (CommRingCat.of R)).toGrp ⟶ C.H :=
  (Diagonalizable.baseChangeIso (Spec.algebraMap R K) X).hom ≫ C.t

theorem genericTorus_comp :
    genericTorus D R K C ≫ C.i =
      (baseChange (Spec.algebraMap R K)).map (D.torusToGLOver (CommRingCat.of R)) ≫
        (ambientModel D R K).genericIso.hom := by
  rw [genericTorus, Category.assoc, C.t_comp, ← D.torusToGLOver_eq K]
  exact (D.baseChange_torusToGLOver (Spec.algebraMap R K)).symm

/-- The full-lattice torus factors through the flat schematic closure. -/
theorem exists_torusOver :
    ∃ t : (TR (X := X) (CommRingCat.of R)).toGrp.X ⟶
        (genericModel D R K C).group.X,
      t ≫ (modelInclusion D R K C).hom.hom =
        (D.torusToGLOver (CommRingCat.of R)).hom.hom := by
  let T := (TR (X := X) (CommRingCat.of R)).toGrp
  let h := genericTorus D R K C ≫ (genericModel D R K C).genericIso.inv
  have hh : h ≫ (baseChange (Spec.algebraMap R K)).map (modelInclusion D R K C) =
      (baseChange (Spec.algebraMap R K)).map (D.torusToGLOver (CommRingCat.of R)) := by
    apply (cancel_mono (ambientModel D R K).genericIso.hom).mp
    dsimp only [h]
    simp only [Category.assoc]
    rw [modelInclusion_generic]
    simp only [Iso.inv_hom_id_assoc]
    exact genericTorus_comp D R K C
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
      (D.torusToGLOver (CommRingCat.of R))
      ((baseChange (Spec.algebraMap R K)).obj T).X (𝟙 _)).symm

/-- The chosen factorization of the integral torus over the base. -/
def torusOver :
    (TR (X := X) (CommRingCat.of R)).toGrp.X ⟶ (genericModel D R K C).group.X :=
  Classical.choose (exists_torusOver D R K C)

@[reassoc (attr := simp)]
theorem torusOver_comp :
    torusOver D R K C ≫ (modelInclusion D R K C).hom.hom =
      (D.torusToGLOver (CommRingCat.of R)).hom.hom :=
  Classical.choose_spec (exists_torusOver D R K C)

local instance torusModelClosed :
    IsClosedImmersion (modelInclusion D R K C).hom.hom.left :=
  modelInclusion_closed D R K C

local instance torusModelMono : Mono (modelInclusion D R K C).hom.hom := by
  have : Mono (modelInclusion D R K C).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective
      (IsClosedImmersion.isClosedEmbedding (modelInclusion D R K C).hom.hom.left).injective
  exact Over.mono_of_mono_left _

instance isMonHom_torusOver : IsMonHom (torusOver D R K C) := by
  have : IsMonHom (torusOver D R K C ≫ (modelInclusion D R K C).hom.hom) := by
    rw [torusOver_comp]
    infer_instance
  exact isMonHom_of_comp_mono _ (modelInclusion D R K C).hom.hom

/-- The actual full-lattice torus homomorphism into the integral model. -/
def torus :
    (TR (X := X) (CommRingCat.of R)).toGrp ⟶ (genericModel D R K C).group :=
  Grp.homMk (torusOver D R K C)

@[reassoc (attr := simp)]
theorem torus_comp :
    torus D R K C ≫ modelInclusion D R K C =
      D.torusToGLOver (CommRingCat.of R) := by
  apply Grp.hom_ext
  exact torusOver_comp D R K C

/-- The full-lattice torus remains a closed subgroup in the closure. -/
theorem torus_closed : IsClosedSubgroup (torus D R K C) := by
  have hfac : (torus D R K C).hom.hom.left ≫
      (modelInclusion D R K C).hom.hom.left =
      (D.torusToGLOver (CommRingCat.of R)).hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (torus_comp D R K C)
  have : IsClosedImmersion ((torus D R K C).hom.hom.left ≫
      (modelInclusion D R K C).hom.hom.left) :=
    hfac.symm ▸ D.isClosedSubgroup_torusToGLOver (CommRingCat.of R)
  exact IsClosedImmersion.of_comp _ (modelInclusion D R K C).hom.hom.left

/-- The torus factorization is characterized by its matrix representation. -/
theorem torus_unique
    (t : (TR (X := X) (CommRingCat.of R)).toGrp ⟶ (genericModel D R K C).group)
    (ht : t ≫ modelInclusion D R K C = D.torusToGLOver (CommRingCat.of R)) :
    t = torus D R K C := by
  apply Grp.hom_ext
  apply (cancel_mono (modelInclusion D R K C).hom.hom).mp
  exact (congrArg (fun f => f.hom.hom) ht).trans (torusOver_comp D R K C).symm

/-- The generic torus is exactly the supplied torus of the chosen Chevalley group. -/
theorem baseChange_torus :
    (baseChange (Spec.algebraMap R K)).map (torus D R K C) ≫
        (genericModel D R K C).genericIso.hom = genericTorus D R K C := by
  have : Mono C.i.hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective (IsClosedImmersion.isClosedEmbedding _).injective
  have : Mono C.i.hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono C.i.hom.hom).mp
  change (((baseChange (Spec.algebraMap R K)).map (torus D R K C) ≫
      (genericModel D R K C).genericIso.hom) ≫ C.i).hom.hom =
    (genericTorus D R K C ≫ C.i).hom.hom
  rw [Category.assoc, ← modelInclusion_generic, ← Category.assoc, ← Functor.map_comp,
    torus_comp, genericTorus_comp]

end Langlands.GroupScheme.ChevalleyIntegral
