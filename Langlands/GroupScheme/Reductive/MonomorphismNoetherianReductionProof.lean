import Langlands.GroupScheme.Reductive.MonomorphismNoetherianReductionStatement
import Langlands.GroupScheme.Descent.FiniteCoefficientReductiveModel
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Mathlib.RingTheory.FiniteType

/-! # Reduction of reductive monomorphisms to noetherian bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace ReductiveMonomorphismNoetherianReduction

open Descent.FiniteCoefficient

/-- A recovered closed coefficient model makes the original homomorphism closed. -/
theorem SimultaneousHomModel.isClosedImmersion_of_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}
    (D : Descent.FiniteCoefficient.SimultaneousHomModel R A f)
    (hc : IsClosedImmersion D.hom.hom.hom.left) :
    IsClosedImmersion f.hom.hom.left := by
  let b := Spec.algebraMap D.coefficients A
  have : IsClosedImmersion ((baseChange b).map D.hom).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (baseChange_map_isPullback b D.hom).flip hc
  have he : f = D.sourceIso.hom ≫ (baseChange b).map D.hom ≫ D.targetIso.inv := by
    rw [← Category.assoc, D.comm]
    simp
  rw [he]
  change IsClosedImmersion (D.sourceIso.hom.hom.hom.left ≫
    ((baseChange b).map D.hom).hom.hom.left ≫ D.targetIso.inv.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- The locally noetherian case implies the theorem over every affine base. -/
theorem affineCase_of_locallyNoetherianCase
    (hHom : HomGeneralStatement.{u})
    (hMono : Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u})
    (hLimit : DirectLimitReductiveStatement.{u})
    (hN : ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u})
    (A : Type u) [CommRing A] (G H : GroupScheme (Spec (CommRingCat.of A)))
    (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom.left] : IsClosedImmersion f.hom.hom.left := by
  have : IsNoetherianRing (⊥ : Subalgebra ℤ A) := by
    have := (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ A)).mp Subalgebra.fg_bot
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨D, -, hred, hm⟩ :=
    exists_reductiveMonoModel (R := ↥(⊥ : Subalgebra ℤ A)) hHom hMono hLimit f hG ∅
  have := (Subalgebra.fg_iff_finiteType D.coefficients).mp D.finite
  have : IsNoetherianRing D.coefficients :=
    Algebra.FiniteType.isNoetherianRing (⊥ : Subalgebra ℤ A) D.coefficients
  apply SimultaneousHomModel.isClosedImmersion_of_model D
  exact hN _ D.source D.target hred D.targetSeparated D.targetFinitePresentation
    D.targetQuasiCompact D.hom hm

/-- Closedness of an actual group homomorphism is local on an open cover of the base. -/
theorem isClosedImmersion_of_openCover {S : Scheme.{u}} {G H : GroupScheme S}
    (f : G ⟶ H) (𝒰 : Scheme.OpenCover.{u} S)
    (hc : ∀ i, IsClosedImmersion ((baseChange (𝒰.f i)).map f).hom.hom.left) :
    IsClosedImmersion f.hom.hom.left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (𝒰.pullback₁ H.X.hom)
  intro i
  let := hc i
  let hp := (baseChange_map_isPullback (𝒰.f i) f).flip
  change IsClosedImmersion
    (pullback.snd f.hom.hom.left (pullback.fst H.X.hom (𝒰.f i)))
  rw [← hp.isoPullback_inv_snd]
  infer_instance

/-- Finite coefficient descent and the locally noetherian case give the theorem
over an arbitrary base. -/
theorem generalCase_of_locallyNoetherianCase
    (hHom : HomGeneralStatement.{u})
    (hMono : Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u})
    (hLimit : DirectLimitReductiveStatement.{u})
    (hN : ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u}) :
    ReductiveMonomorphismClosedImmersionStatement.{u} := by
  intro S G H hG hs hp hq f hm
  let := hs
  let := hp
  let := hq
  let := hm
  apply isClosedImmersion_of_openCover f S.affineOpenCover.openCover
  intro i
  let b := S.affineOpenCover.f i
  have : IsSeparated ((baseChange b).obj H).X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation ((baseChange b).obj H).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom b)
    infer_instance
  have : QuasiCompact ((baseChange b).obj H).X.hom := by
    change QuasiCompact (pullback.snd H.X.hom b)
    infer_instance
  have : Mono ((baseChange b).map f).hom.hom.left :=
    (baseChange_map_isPullback b f).flip.mono_snd_of_mono
  exact affineCase_of_locallyNoetherianCase hHom hMono hLimit hN
    (S.affineOpenCover.X i) _ _ (hG.baseChange b) ((baseChange b).map f)

end ReductiveMonomorphismNoetherianReduction

/-- The conditional reduction from arbitrary bases to locally noetherian bases. -/
theorem reductiveMonomorphismNoetherianReduction :
    ReductiveMonomorphismNoetherianReductionStatement.{u} := by
  intro hHom hMono hLimit
  constructor
  · exact ReductiveMonomorphismNoetherianReduction.generalCase_of_locallyNoetherianCase
      hHom hMono hLimit
  · intro h S _ G H hG hs hp hq f hm
    exact h S G H hG hs hp hq f hm

end Langlands.GroupScheme
