import Langlands.AlgebraicGeometry.SchemeFilteredModelExistenceStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

/-! # Existence of initial scheme models along filtered ring colimits -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- Noetherian approximation over lifted integers, followed by factorization
through the actual spectrum diagram, constructs an initial model. -/
theorem schemeFilteredModelExistence : SchemeFilteredModelExistence.{u} := by
  intro J _ _ F c hc X g _ _ _
  let : Algebra (ULift.{u} ℤ) c.pt := ULift.algebra' ℤ c.pt
  obtain ⟨T, hT, _, X₀, f₀, π₀, hf₀, hqc₀, hqs₀, hpb₀⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent
      (A₀ := ULift.{u} ℤ) g ∅
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let : Algebra.FiniteType (ULift.{u} ℤ) T := T.fg_iff_finiteType.mp hT
  let : Algebra.FinitePresentation (ULift.{u} ℤ) T :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let z : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) T))
  let : LocallyOfFinitePresentation z := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let D : Jᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  let hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  let t : D ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    { app := fun i => Spec.map (CommRingCat.isInitial.to (F.obj i.unop))
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let (i : Jᵒᵖ) : IsAffine (D.obj i) := by
    dsimp [D]
    infer_instance
  let a : d.pt ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T c.pt))
  have ha : d.π ≫ t = (Functor.const Jᵒᵖ).map (a ≫ z) := by
    ext i
    exact specULiftZIsTerminal.hom_ext _ _
  obtain ⟨i, q, hq, _⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t z d hd a ha
  let : LocallyOfFinitePresentation f₀ := hf₀
  let : QuasiCompact f₀ := hqc₀
  let : QuasiSeparated f₀ := hqs₀
  let Xj := pullback f₀ q
  let gj : Xj ⟶ Spec (F.obj i.unop) := pullback.snd f₀ q
  have houter : IsPullback π₀ g f₀ (Spec.map (c.ι.app i.unop) ≫ q) := by
    simpa only [D, d, a] using hq ▸ hpb₀
  have hright : IsPullback (pullback.fst f₀ q) gj f₀ q :=
    IsPullback.of_hasPullback f₀ q
  exact ⟨i.unop, Xj, gj, _, inferInstance, inferInstance, inferInstance,
    houter.of_right' hright⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
