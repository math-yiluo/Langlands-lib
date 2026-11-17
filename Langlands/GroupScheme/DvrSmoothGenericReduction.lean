import Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement
import Langlands.GroupScheme.DvrSmoothGenericReductionStatement
import Langlands.GroupScheme.DvrGenericReduction
import Langlands.GroupScheme.DvrCoverAssembly

/-! # Smooth-generic reduction from potential geometric reducedness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.DvrSmoothGenericReduction

/-- Actual witnesses for the preliminary reduction to smooth generic fibre. -/
structure Reduction {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) where
  ring : Type u
  [comm : CommRing ring]
  [domain : IsDomain ring]
  [dvr : IsDiscreteValuationRing ring]
  base : Spec (CommRingCat.of ring) ⟶ Spec (CommRingCat.of R)
  flat : Flat base
  surjective : Surjective base
  group : GroupScheme (Spec (CommRingCat.of ring))
  map : group ⟶ (baseChange base).obj G
  group_flat : Flat group.X.hom
  locallyOfFiniteType : LocallyOfFiniteType group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  separated : IsSeparated group.X.hom
  smoothGeneric : Smooth
    ((baseChange (Spec.algebraMap ring (FractionRing ring))).obj group).X.hom
  affineGeneric : IsAffineHom
    ((baseChange (Spec.algebraMap ring (FractionRing ring))).obj group).X.hom
  finite : IsFinite map.hom.hom.left
  map_surjective : Surjective map.hom.hom.left

attribute [instance] Reduction.comm Reduction.domain Reduction.dvr

section Construction

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Flat G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  [IsSeparated G.X.hom]
  [IsAffineHom ((baseChange (Spec.algebraMap R K)).obj G).X.hom]

include K in
/-- Potential geometric reducedness supplies a DVR extension and the
flat closure of the actual smooth reduced generic subgroup. -/
theorem nonempty_reduction
    (hPotential : Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement.{u}) :
    Nonempty (Reduction G) := by
  obtain ⟨R', cR', dR', hDvr, b, hbflat, hbsurj, hred⟩ :=
    hPotential R G.X inferInstance inferInstance inferInstance
  let := cR'
  let := dR'
  let := hDvr
  let := hbflat
  let := hbsurj
  let G' := (baseChange b).obj G
  have : Flat G'.X.hom := by change Flat (pullback.snd G.X.hom b); infer_instance
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b); infer_instance
  have : QuasiCompact G'.X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b); infer_instance
  have : IsSeparated G'.X.hom := by
    change IsSeparated (pullback.snd G.X.hom b); infer_instance
  have : GeometricallyReduced
      (ReducedSubgroup.redOver
        (DvrGenericReduction.genericGroup (K := FractionRing R') G')).hom := hred
  have : IsAffineHom ((Over.pullback (Spec.algebraMap R K)).obj G.X).hom :=
    inferInstanceAs (IsAffineHom ((baseChange (Spec.algebraMap R K)).obj G).X.hom)
  have : IsAffineHom
      (DvrGenericReduction.genericGroup (K := FractionRing R') G').X.hom :=
    DvrCoverAssembly.affine_generic (K := K) b G.X
  exact ⟨{
    ring := R'
    base := b
    flat := hbflat
    surjective := hbsurj
    group := DvrGenericReduction.group (K := FractionRing R') G'
    map := DvrGenericReduction.map (K := FractionRing R') G'
    group_flat := inferInstance
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    separated := inferInstance
    smoothGeneric := inferInstance
    affineGeneric := DvrGenericReduction.affine_generic (K := FractionRing R') G'
    finite := inferInstance
    map_surjective := inferInstance }⟩

/-- Select the actual finite surjective preliminary group cover. -/
def reduction
    (hPotential : Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement.{u}) :
    Reduction G := Classical.choice (nonempty_reduction R K G hPotential)

end Construction

/-- The group-specific reduction follows from the general scheme prerequisite. -/
theorem dvrSmoothGenericReduction_of_potential
    (hPotential : Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement.{u}) :
    DvrSmoothGenericReductionStatement.{u} := by
  intro R _ _ _ K _ _ _ G hflat hlft hqc hsep hgen
  have := hflat
  have := hlft
  have := hqc
  have := hsep
  have := hgen
  let D := reduction R K G hPotential
  exact ⟨D.ring, D.comm, D.domain, D.dvr, D.base, D.flat, D.surjective,
    D.group, D.map, D.group_flat, D.locallyOfFiniteType, D.quasiCompact, D.separated,
    D.smoothGeneric, D.affineGeneric, D.finite, D.map_surjective⟩

end Langlands.GroupScheme.DvrSmoothGenericReduction
