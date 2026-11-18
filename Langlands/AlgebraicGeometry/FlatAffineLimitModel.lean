import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Flat affine models along affine limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.AlgebraicGeometry.FlatAffineLimit

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X]
  (f : X ⟶ Spec (CommRingCat.of A)) [Flat f] [LocallyOfFinitePresentation f]

/-- A flat affine finite-presentation model over a noetherian finite
coefficient ring, with its actual recovery square. -/
theorem exists_coefficientModel :
    ∃ (T : CommRingCat.{u}) (_ : IsNoetherianRing T)
      (Y : Scheme.{u}) (_ : IsAffine Y) (g : Y ⟶ Spec T)
      (_ : Flat g) (_ : LocallyOfFinitePresentation g)
      (b : Spec (CommRingCat.of A) ⟶ Spec T) (a : X ⟶ Y),
      IsPullback a f g b ∧ LocallyOfFinitePresentation (Langlands.GroupScheme.Gm.toSpecZ (Spec T)) := by
  let R := ULift.{u} ℤ
  let : Algebra R A := ULift.algebra' ℤ A
  have : IsScalarTower R R A := ⟨fun r s a => by
    change (r.down * s.down) • a = r.down • s.down • a
    exact mul_smul r.down s.down a⟩
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, -, -, Y, g, a, hY, hfp, hqc, hqs, hpb⟩ :=
    exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
      (A₀ := R) (R := R) f (∅ : Finset A)
  let := hY
  let := hfp
  let := hqc
  let := hqs
  have : Flat (pullback.snd g (Spec.algebraMap T A)) := by
    rw [← hpb.isoPullback_inv_snd]
    infer_instance
  obtain ⟨U, hU, -, hflat⟩ := Flat.exists_fg_subalgebra_of_flat_pullback_snd g (∅ : Finset A)
  let b := Spec.algebraMap U A
  let d := Spec.algebraMap T U
  have hbd : b ≫ d = Spec.algebraMap T A := by
    dsimp [b, d, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let Z := pullback g d
  let g' : Z ⟶ Spec (CommRingCat.of U) := pullback.snd g d
  let a' : X ⟶ Z := pullback.lift a (f ≫ b) (by rw [Category.assoc, hbd]; exact hpb.w)
  have hpb' : IsPullback a' f g' b :=
    IsPullback.of_right
      (by simpa only [a', pullback.lift_fst, hbd] using hpb)
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g d)
  have hft : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have hfu : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have hRT : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
  have hRU : IsNoetherianRing U := Algebra.FiniteType.isNoetherianRing T U
  have hRUft : Algebra.FiniteType R U := Algebra.FiniteType.trans hft hfu
  have : Algebra.FinitePresentation R U := (Algebra.FinitePresentation.of_finiteType (R := R) (A := U)).mp hRUft
  have hfpU : LocallyOfFinitePresentation (Spec.algebraMap R U) := by
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have heq : Langlands.GroupScheme.Gm.toSpecZ (Spec (CommRingCat.of U)) =
      Spec.algebraMap R U := specULiftZIsTerminal.hom_ext _ _
  refine ⟨CommRingCat.of U, hRU, Z, inferInstance, g', hflat, inferInstance, b, a', hpb', ?_⟩
  rw [heq]
  exact hfpU

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
  (c : Cone D) (hc : IsLimit c) (e : c.pt ≅ Spec (CommRingCat.of A))

/-- A supplied affine flat finitely presented scheme over the affine limit
is recovered by base change from one actual affine flat finitely presented
level model. -/
structure Model where
  level : I
  source : Scheme.{u}
  [affine : IsAffine source]
  map : source ⟶ D.obj level
  [flat : Flat map]
  [finitePresentation : LocallyOfFinitePresentation map]
  projection : X ⟶ source
  isPullback : IsPullback projection f map (e.inv ≫ c.π.app level)

attribute [instance] Model.affine Model.flat Model.finitePresentation

include hc

/-- Construct an actual flat affine model on one affine diagram level. -/
theorem nonempty_model : Nonempty (Model f D c e) := by
  obtain ⟨T, hT, Y, hY, g, hflat, hfp, b, a, hpb, hTZ⟩ := exists_coefficientModel f
  let := hT
  let := hY
  let := hflat
  let := hfp
  let := hTZ
  let t : D ⟶ (Functor.const I).obj (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    { app i := Langlands.GroupScheme.Gm.toSpecZ (D.obj i)
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  obtain ⟨i, v, hv, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t (Langlands.GroupScheme.Gm.toSpecZ (Spec T)) c hc (e.hom ≫ b)
    (by ext; exact specULiftZIsTerminal.hom_ext _ _)
  have hv' : (e.inv ≫ c.π.app i) ≫ v = b := by
    rw [Category.assoc, hv, Iso.inv_hom_id_assoc]
  let Z := pullback g v
  let g' : Z ⟶ D.obj i := pullback.snd g v
  let a' : X ⟶ Z := pullback.lift a (f ≫ e.inv ≫ c.π.app i)
    (by rw [Category.assoc, Category.assoc, ← Category.assoc e.inv, hv']; exact hpb.w)
  have hp : IsPullback a' f g' (e.inv ≫ c.π.app i) :=
    IsPullback.of_right
      (by simpa only [a', pullback.lift_fst, hv'] using hpb)
      (by simp only [a', g', pullback.lift_snd])
      (IsPullback.of_hasPullback g v)
  exact ⟨⟨i, Z, g', a', hp⟩⟩

/-- Choose the actual model at an affine level. -/
def model : Model f D c e := Classical.choice (nonempty_model f D c hc e)

end Langlands.AlgebraicGeometry.FlatAffineLimit
