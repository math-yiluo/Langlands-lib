import Langlands.GroupScheme.PointCentralizer
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The conjugacy transporter from a section to a point of a group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Base change of the pullback of `w` and `o` along `q` is the pullback of `q ≫ w` and `o`. -/
theorem isPullback_pullback_comp {C : Type*} [Category C] [HasPullbacks C] {W W' X Y : C}
    (q : W' ⟶ W) (w : W ⟶ Y) (o : X ⟶ Y) :
    IsPullback (pullback.fst (q ≫ w) o)
      (pullback.lift (pullback.fst (q ≫ w) o ≫ q) (pullback.snd (q ≫ w) o)
        (by rw [Category.assoc, pullback.condition]))
      q (pullback.fst w o) := by
  have s : IsPullback (pullback.lift (pullback.fst (q ≫ w) o ≫ q) (pullback.snd (q ≫ w) o)
      (by rw [Category.assoc, pullback.condition]) ≫ pullback.snd w o)
      (pullback.fst (q ≫ w) o) o (q ≫ w) := by
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (q ≫ w) o).flip
  exact (IsPullback.of_right s (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback w o).flip).flip

variable {S : Scheme.{u}} (G : GroupScheme S) (x : 𝟙_ (Over S) ⟶ G.X)

/-- The conjugation orbit map `h ↦ h x h⁻¹` of a section `x`. -/
def conjugationOrbitMap : G.X ⟶ G.X :=
  𝟙 G.X * (toUnit G.X ≫ x) * (𝟙 G.X)⁻¹

/-- Restricting a conjugate of the pullback of a section along a test morphism. -/
theorem comp_conj {Y Y' : Over S} (f : Y' ⟶ Y) (a : Y ⟶ G.X) :
    f ≫ (a * (toUnit Y ≫ x) * a⁻¹) = (f ≫ a) * (toUnit Y' ≫ x) * (f ≫ a)⁻¹ := by
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    toUnit_unique (f ≫ toUnit Y) (toUnit Y')]

theorem comp_conjugationOrbitMap {Y : Over S} (h : Y ⟶ G.X) :
    h ≫ G.conjugationOrbitMap x = h * (toUnit Y ≫ x) * h⁻¹ := by
  rw [conjugationOrbitMap, comp_conj, Category.comp_id]

variable {G x} {T : GroupScheme S} {i : T ⟶ G} (hi : (G.pointCentralizer x).IsRepresentedBy i)
  {W : Over S} {w : W ⟶ G.X} (g : W ⟶ G.X) (hg : g * (toUnit W ≫ x) * g⁻¹ = w)

include hg in
/-- On the transporter, the quotient of the two conjugators centralizes the section. -/
theorem transporter_mem :
    (pullback.fst w (G.conjugationOrbitMap x) ≫ g)⁻¹ * pullback.snd w (G.conjugationOrbitMap x) ∈
      (G.pointCentralizer x).carrier (pullback w (G.conjugationOrbitMap x)) := by
  set a := pullback.fst w (G.conjugationOrbitMap x) ≫ g
  set h := pullback.snd w (G.conjugationOrbitMap x)
  set X := toUnit (pullback w (G.conjugationOrbitMap x)) ≫ x
  have e : h * X * h⁻¹ = a * X * a⁻¹ := by
    rw [← comp_conjugationOrbitMap G x h, ← pullback.condition, ← comp_conj, hg]
  rw [mem_pointCentralizer]
  calc a⁻¹ * h * X = a⁻¹ * (h * X * h⁻¹) * h := by group
    _ = a⁻¹ * (a * X * a⁻¹) * h := by rw [e]
    _ = X * (a⁻¹ * h) := by group

/-- The point of the centralizer comparing a transporter point with `g`. -/
def transporterToCentralizer : pullback w (G.conjugationOrbitMap x) ⟶ T.X :=
  (hi.pointsEquiv _).symm ⟨_, transporter_mem g hg⟩

theorem transporterToCentralizer_comp :
    transporterToCentralizer hi g hg ≫ i.hom.hom =
      (pullback.fst w (G.conjugationOrbitMap x) ≫ g)⁻¹ *
        pullback.snd w (G.conjugationOrbitMap x) :=
  hi.pointsEquiv_symm_comp _

/-- The translate of the centralizer by `g`, mapped into the transporter. -/
def transporterOfCentralizer : W ⊗ T.X ⟶ pullback w (G.conjugationOrbitMap x) :=
  pullback.lift (fst W T.X) ((fst W T.X ≫ g) * (snd W T.X ≫ i.hom.hom)) (by
    have hc : snd W T.X ≫ i.hom.hom ∈ (G.pointCentralizer x).carrier (W ⊗ T.X) := by
      rw [← hi.2]
      exact ⟨_, rfl⟩
    rw [mem_pointCentralizer] at hc
    rw [comp_conjugationOrbitMap]
    calc fst W T.X ≫ w = fst W T.X ≫ (g * (toUnit W ≫ x) * g⁻¹) := by rw [hg]
      _ = (fst W T.X ≫ g) * (toUnit _ ≫ x) * (fst W T.X ≫ g)⁻¹ := comp_conj G x _ _
      _ = (fst W T.X ≫ g) * ((snd W T.X ≫ i.hom.hom) * (toUnit _ ≫ x) *
            (snd W T.X ≫ i.hom.hom)⁻¹) * (fst W T.X ≫ g)⁻¹ := by
          rw [hc, mul_inv_cancel_right]
      _ = _ := by group)

/-- **The transporter is a translate of the centralizer.** If `g` conjugates the section `x`
to `w`, the transporter from `x` to `w` is isomorphic over `W` to `W × T`, where `T`
represents the centralizer of `x`. -/
def transporterIso : pullback w (G.conjugationOrbitMap x) ≅ W ⊗ T.X where
  hom := lift (pullback.fst _ _) (transporterToCentralizer hi g hg)
  inv := transporterOfCentralizer hi g hg
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, transporterOfCentralizer, pullback.lift_fst, lift_fst, Category.id_comp]
    · rw [Category.assoc, transporterOfCentralizer, pullback.lift_snd, MonObj.comp_mul,
        lift_fst_assoc, ← Category.assoc, lift_snd, transporterToCentralizer_comp,
        mul_inv_cancel_left, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp, transporterOfCentralizer, pullback.lift_fst]
    · have : Mono i.hom.hom := hi.1
      rw [Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i.hom.hom, Category.assoc,
        transporterToCentralizer_comp, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        transporterOfCentralizer, pullback.lift_fst, pullback.lift_snd, inv_mul_cancel_left]

theorem transporterIso_hom_fst :
    (transporterIso hi g hg).hom ≫ fst W T.X = pullback.fst w (G.conjugationOrbitMap x) :=
  lift_fst _ _

include hi hg in
/-- The transporter to a conjugate of the section is smooth over `W` when the centralizer is
smooth. -/
theorem smooth_transporter_fst_left [Smooth T.X.hom] :
    Smooth (pullback.fst w (G.conjugationOrbitMap x)).left := by
  rw [← transporterIso_hom_fst hi g hg, Over.comp_left]
  have : Smooth (fst W T.X).left := show Smooth (pullback.fst W.hom T.X.hom) by infer_instance
  have : IsIso (transporterIso hi g hg).hom.left :=
    show IsIso ((Over.forget S).map (transporterIso hi g hg).hom) by infer_instance
  infer_instance

end Langlands.GroupScheme
