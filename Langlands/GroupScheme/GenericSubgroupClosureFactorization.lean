import Langlands.GroupScheme.GenericSubgroupClosure

/-! # Factorization through a generic subgroup closure -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GenericSubgroupClosure

open IntegralModel.SchematicClosureConstruction

section GenericProjection

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (M : GroupScheme (Spec (CommRingCat.of R)))

/-- The generic-fibre projection, regarded as a morphism over `Spec R`. -/
def genericProjection :
    (Over.map (Spec.algebraMap R K)).obj
      ((baseChange (Spec.algebraMap R K)).obj M).X ⟶ M.X :=
  baseChangePointsEquiv (Spec.algebraMap R K) M _ (𝟙 _)

omit [IsDomain R] [IsFractionRing R K] in
theorem genericProjection_left :
    (genericProjection (K := K) M).left =
      pullback.fst M.X.hom (Spec.algebraMap R K) := by
  simp [genericProjection]

instance quasiCompact_genericProjection :
    QuasiCompact (genericProjection (K := K) M).left := by
  rw [genericProjection_left]
  infer_instance

instance isSchemeTheoreticallyDominant_genericProjection [Flat M.X.hom] :
    IsSchemeTheoreticallyDominant (genericProjection (K := K) M).left := by
  rw [genericProjection_left]
  infer_instance

end GenericProjection

section Factorization

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  {H : GroupScheme (Spec (CommRingCat.of K))}
  (j : H ⟶ (baseChange (Spec.algebraMap R K)).obj G)
  [IsClosedImmersion j.hom.hom.left]
  {M : GroupScheme (Spec (CommRingCat.of R))} [Flat M.X.hom]
  (f : M ⟶ G)
  (h : (baseChange (Spec.algebraMap R K)).obj M ⟶ H)
  (hh : h ≫ j = (baseChange (Spec.algebraMap R K)).map f)

instance isClosedImmersion_closureInclusion :
    IsClosedImmersion (closureInclusion G j).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver G j).left)

include h hh in
omit [IsDedekindDomain R] [IsClosedImmersion j.hom.hom.left] in
/-- A flat source whose generic map lands in the subgroup factors through its closure. -/
theorem exists_factorOver :
    ∃ a : M.X ⟶ closureOver G j, a ≫ inclusionOver G j = f.hom.hom := by
  refine exists_over_factor_of_schematic_precomp (inclusionOver G j)
    (genericProjection (K := K) M) f.hom.hom
    ((Over.map (Spec.algebraMap R K)).map h.hom.hom ≫ projectionOver G j) ?_
  rw [Category.assoc, projectionOver_fac, map_comp_genericOver]
  have hh' : h.hom.hom ≫ j.hom.hom =
      ((baseChange (Spec.algebraMap R K)).map f).hom.hom :=
    congrArg (fun t => t.hom.hom) hh
  rw [hh']
  simpa only [Category.id_comp, genericProjection, baseChange] using
    (baseChangePointsEquiv_comp (Spec.algebraMap R K) f
      ((baseChange (Spec.algebraMap R K)).obj M).X (𝟙 _)).symm

/-- The induced morphism to the closure on schemes over the base. -/
def factorOver : M.X ⟶ closureOver G j :=
  Classical.choose (exists_factorOver G j f h hh)

omit [IsDedekindDomain R] [IsClosedImmersion j.hom.hom.left] in
@[reassoc (attr := simp)]
theorem factorOver_fac :
    factorOver G j f h hh ≫ inclusionOver G j = f.hom.hom :=
  Classical.choose_spec (exists_factorOver G j f h hh)

instance isMonHom_factorOver : IsMonHom (factorOver G j f h hh) := by
  have : IsMonHom (factorOver G j f h hh ≫ inclusionOver G j) := by
    rw [factorOver_fac]
    infer_instance
  exact isMonHom_of_comp_mono _ (inclusionOver G j)

/-- The induced group-scheme homomorphism to the generic subgroup closure. -/
def factor : M ⟶ closureGroup G j := Grp.homMk (factorOver G j f h hh)

@[reassoc (attr := simp)]
theorem factor_fac : factor G j f h hh ≫ closureInclusion G j = f := by
  apply Grp.hom_ext
  exact factorOver_fac G j f h hh

instance mono_factor_left [Mono f.hom.hom.left] :
    Mono (factor G j f h hh).hom.hom.left :=
  mono_of_mono_fac (congrArg (fun t => t.hom.hom.left) (factor_fac G j f h hh))

/-- Closedness of the original homomorphism is equivalent to closedness of its
factor through the generic subgroup closure. -/
theorem isClosedImmersion_iff_factor :
    IsClosedImmersion f.hom.hom.left ↔
      IsClosedImmersion (factor G j f h hh).hom.hom.left := by
  have hfac :
      (factor G j f h hh).hom.hom.left ≫ (closureInclusion G j).hom.hom.left =
        f.hom.hom.left :=
    congrArg (fun t => t.hom.hom.left) (factor_fac G j f h hh)
  constructor
  · intro hf
    have : IsClosedImmersion ((factor G j f h hh).hom.hom.left ≫
        (closureInclusion G j).hom.hom.left) := hfac.symm ▸ hf
    exact IsClosedImmersion.of_comp _ (closureInclusion G j).hom.hom.left
  · intro ha
    rw [← hfac]
    exact IsClosedImmersion.comp _ _

/-- The factorization is unique among group-scheme homomorphisms. -/
theorem factor_unique (a : M ⟶ closureGroup G j)
    (ha : a ≫ closureInclusion G j = f) : a = factor G j f h hh := by
  apply Grp.hom_ext
  apply (cancel_mono (inclusionOver G j)).mp
  exact (congrArg (fun t => t.hom.hom) ha).trans (factorOver_fac G j f h hh).symm

/-- The generic fibre of the factorization is the supplied generic map followed by
the canonical identification with the generic fibre of the closure. -/
theorem baseChange_factor :
    (baseChange (Spec.algebraMap R K)).map (factor G j f h hh) =
      h ≫ (genericToClosureIso G j).hom := by
  apply Grp.hom_ext
  apply (cancel_mono
    ((baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom).mp
  change ((baseChange (Spec.algebraMap R K)).map (factor G j f h hh) ≫
      (baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom =
    ((h ≫ (genericToClosureIso G j).hom) ≫
      (baseChange (Spec.algebraMap R K)).map (closureInclusion G j)).hom.hom
  rw [← Functor.map_comp, factor_fac, Category.assoc, genericToClosureIso_hom_comp, hh]

end Factorization

end Langlands.GroupScheme.GenericSubgroupClosure
