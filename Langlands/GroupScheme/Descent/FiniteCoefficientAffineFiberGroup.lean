import Langlands.AlgebraicGeometry.AffineFiberLocus
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.GroupScheme.Descent.FiniteCoefficientSeparatedGroup

/-! # Finite coefficient models of smooth groups with affine residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A finite coefficient model with the smooth, separated and affine-residue-fibre
properties and an actual group-scheme isomorphism after base change. -/
structure SmoothAffineFiberGroupModel (G : GroupScheme (Spec (CommRingCat.of A))) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  group : GroupScheme (Spec (CommRingCat.of coefficients))
  smooth : Smooth group.X.hom
  separated : IsSeparated group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  affineFibres : affineFiberLocus group.X.hom = Set.univ
  iso : G ≅ (baseChange (Spec.algebraMap coefficients A)).obj group

private theorem groupIsoPullback {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H) :
    IsPullback e.inv.hom.hom.left H.X.hom G.X.hom (𝟙 S) :=
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.inv.hom.hom.w⟩

private def baseChangeSubalgebraIso (B : Subalgebra R A)
    (G : GroupScheme (Spec (CommRingCat.of R))) :
    (baseChange (Spec.algebraMap R A)).obj G ≅
      (baseChange (Spec.algebraMap B A)).obj ((baseChange (Spec.algebraMap R B)).obj G) :=
  (pullbackComparison (Spec.algebraMap R B) (Spec.algebraMap B A)
    (Spec.algebraMap R A) (by
      simp only [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]) G).symm

/-- Over a noetherian coefficient ring, a smooth separated quasi-compact group
with affine residue fibres admits a finite coefficient model with those properties. -/
theorem exists_smoothAffineFiberGroupModel [IsNoetherianRing R]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : affineFiberLocus G.X.hom = Set.univ) :
    Nonempty (SmoothAffineFiberGroupModel R A G) := by
  let D := separatedGroupModel R A G
  let : QuasiCompact D.group.X.hom := D.quasiCompact
  let : LocallyOfFinitePresentation D.group.X.hom := D.finitePresentation
  let : Smooth (pullback.snd D.group.X.hom (Spec.algebraMap D.coefficients A)) :=
    MorphismProperty.of_isPullback (P := @Smooth) (groupIsoPullback D.iso) inferInstance
  obtain ⟨B, hB, -, hBsmooth⟩ := smoothSubalgebraDescent D.group.X.hom (∅ : Finset A)
  let H := (baseChange (Spec.algebraMap D.coefficients B)).obj D.group
  let e : G ≅ (baseChange (Spec.algebraMap B A)).obj H :=
    D.iso ≪≫ baseChangeSubalgebraIso D.coefficients A B D.group
  let : QuasiCompact H.X.hom :=
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ D.quasiCompact
  let : IsSeparated H.X.hom :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ D.separated
  let : Smooth H.X.hom := hBsmooth
  have hDfin : Algebra.FiniteType R D.coefficients :=
    (Subalgebra.fg_iff_finiteType D.coefficients).mp D.finite
  have hBfin : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans hDfin ((Subalgebra.fg_iff_finiteType B).mp hB)
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hH : affineFiberLocus (pullback.snd H.X.hom (Spec.algebraMap B A)) = Set.univ := by
    change affineFiberLocus ((baseChange (Spec.algebraMap B A)).obj H).X.hom = Set.univ
    rw [affineFiberLocus_baseChange (groupIsoPullback e), hG, Set.preimage_univ]
  obtain ⟨C, hC, -, hCfibres⟩ := exists_fg_subalgebra_affineFiberLocus_eq_univ H.X.hom hH ∅
  have hCfin : Algebra.FiniteType R C :=
    Algebra.FiniteType.trans hBfin ((Subalgebra.fg_iff_finiteType C).mp hC)
  exact ⟨{
    coefficients := (C.restrictScalars D.coefficients).restrictScalars R
    finite := (Subalgebra.fg_iff_finiteType _).mpr hCfin
    group := (baseChange (Spec.algebraMap B C)).obj H
    smooth := MorphismProperty.pullback_snd (P := @Smooth) _ _ hBsmooth
    separated := MorphismProperty.pullback_snd (P := @IsSeparated) _ _
      (inferInstance : IsSeparated H.X.hom)
    quasiCompact := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _
      (inferInstance : QuasiCompact H.X.hom)
    affineFibres := hCfibres
    iso := e ≪≫ baseChangeSubalgebraIso B A C H }⟩

/-- The finite coefficient ring is noetherian over a noetherian starting ring. -/
theorem SmoothAffineFiberGroupModel.isNoetherianRing [IsNoetherianRing R]
    {G : GroupScheme (Spec (CommRingCat.of A))} (D : SmoothAffineFiberGroupModel R A G) :
    IsNoetherianRing D.coefficients := by
  let : Algebra.FiniteType R D.coefficients :=
    (Subalgebra.fg_iff_finiteType D.coefficients).mp D.finite
  exact Algebra.FiniteType.isNoetherianRing R D.coefficients

end Langlands.GroupScheme.Descent.FiniteCoefficient
