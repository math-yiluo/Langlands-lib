import Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement
import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Geometry
import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Frame

/-!
# Fibre frame lifting from restriction-compatible models and the algebraic spreading

`FibreFrameLiftingStatement` follows from `RestrictionPerfectModelsStatement` and
`FibreH0RestrictionSpreadStatement`: work over an affine open neighbourhood of the point, spread
the degree-zero restriction isomorphism to a basic open neighbourhood, lift the frame of the
first closed piece to a section, and test it on the fibre.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules Langlands.Cohomology Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

/-- The fibre frame lifting statement, assuming restriction-compatible perfect models and the
algebraic spreading of a degree-zero restriction isomorphism. -/
theorem fibreFrameLifting_of_models (h1 : RestrictionPerfectModelsStatement.{u})
    (h2 : ModuleComplex.FibreH0RestrictionSpreadStatement.{u}) :
    FibreFrameLiftingStatement.{u} := by
  intro S X X₁ X₂ hXsm hXpr hXgc hX₁sm hX₁pr hX₁gc hX₂sm hX₂pr hX₂gc i₁ i₂ hi₁ hi₂ L s
    hL₁ hL₂ hLs j₁ j₂ O H hH1
  -- an affine open neighbourhood `V` of `s` and the point `Spec κ(s) ⟶ Spec Γ(S, V)`
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  let e := hV.fromSpec
  let k := IsLocalRing.ResidueField (S.presheaf.stalk s)
  let φ₀ : Γ(S, V) ⟶ CommRingCat.of k := S.presheaf.germ V s hsV ≫ S.residue s
  have he : S.fromSpecResidueField s = Spec.map φ₀ ≫ e := fromSpecResidueField_eq_comp_fromSpec hV hsV
  -- base change of the three families to `Spec Γ(S, V)`
  let f := pullback.snd X.hom e
  obtain ⟨_, _, _⟩ := smoothProperConnected_of_isPullback (IsPullback.of_hasPullback X.hom e)
  let L' : LineBundle (pullback X.hom e) := (LineBundle.pullback (pullback.fst X.hom e)).obj L
  have hw₁ : i₁.left ≫ X.hom = X₁.hom := Over.w i₁
  have hw₂ : i₂.left ≫ X.hom = X₂.hom := Over.w i₂
  let g₁ := mapOver X.hom X₁.hom i₁.left hw₁ e
  let g₂ := mapOver X.hom X₂.hom i₂.left hw₂ e
  have : IsClosedImmersion g₁ := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_mapOver X.hom X₁.hom i₁.left hw₁ e) hi₁
  have : IsClosedImmersion g₂ := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_mapOver X.hom X₂.hom i₂.left hw₂ e) hi₂
  obtain ⟨_, _, _⟩ : Smooth (g₁ ≫ f) ∧ IsProper (g₁ ≫ f) ∧ GeometricallyConnected (g₁ ≫ f) := by
    rw [show g₁ ≫ f = pullback.snd X₁.hom e from mapOver_snd _ _ _ _ _]
    exact smoothProperConnected_of_isPullback (IsPullback.of_hasPullback X₁.hom e)
  obtain ⟨_, _, _⟩ : Smooth (g₂ ≫ f) ∧ IsProper (g₂ ≫ f) ∧ GeometricallyConnected (g₂ ≫ f) := by
    rw [show g₂ ≫ f = pullback.snd X₂.hom e from mapOver_snd _ _ _ _ _]
    exact smoothProperConnected_of_isPullback (IsPullback.of_hasPullback X₂.hom e)
  have hL₁' := nonempty_pullback_pullback_iso_unit g₁ (pullback.fst X.hom e)
    (pullback.fst X₁.hom e) i₁.left (mapOver_fst _ _ _ _ _) L.obj hL₁
  have hL₂' := nonempty_pullback_pullback_iso_unit g₂ (pullback.fst X.hom e)
    (pullback.fst X₂.hom e) i₂.left (mapOver_fst _ _ _ _ _) L.obj hL₂
  -- the fibre over `s`
  let t := S.fromSpecResidueField s
  have hLs' := nonempty_pullback_pullback_iso_unit (liftPoint X.hom e φ₀ t he)
    (pullback.fst X.hom e) (𝟙 _) (pullback.fst X.hom t)
    ((liftPoint_fst X.hom e φ₀ t he).trans (Category.id_comp _).symm) L.obj hLs
  obtain ⟨r, hr, hspread⟩ := exists_spread_of_models h1 h2 f L' g₁ g₂ hL₁' hL₂' k φ₀
    (liftPoint X.hom e φ₀ t he) (pullback.snd X.hom t) (isPullback_liftPoint X.hom e φ₀ t he)
    (liftPoint X₁.hom e φ₀ t he) j₁
    (isPullback_liftPoint_mapOver X.hom X₁.hom i₁.left hw₁ e φ₀ t he)
    (liftPoint X₂.hom e φ₀ t he) j₂
    (isPullback_liftPoint_mapOver X.hom X₂.hom i₂.left hw₂ e φ₀ t he) hLs' hH1
  -- the basic open neighbourhood `U` where `r` is invertible
  have hsU : s ∈ S.basicOpen r := by
    rw [S.mem_basicOpen r s hsV]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hr
  have hU : IsAffineOpen (S.basicOpen r) := hV.basicOpen r
  have hUV : S.basicOpen r ≤ V := S.basicOpen_le r
  have hφU : IsUnit ((S.presheaf.map (homOfLE hUV).op) r) :=
    RingedSpace.isUnit_res_basicOpen _ r
  let p := liftAffineOpen X.hom hV hU hUV
  have hX' := isPullback_liftAffineOpen X.hom hV hU hUV
  have hY' := IsPullback.of_hasPullback g₁ p
  have hiso := hspread _ _ hφU _ p _ hX' _ _ _ hY'
  -- base change of the closed piece to `U`
  let g' := pullback.snd g₁ p
  let b := pullback.snd X.hom (S.basicOpen r).ι
  obtain ⟨_, _, _⟩ :=
    smoothProperConnected_of_isPullback (IsPullback.of_hasPullback X.hom (S.basicOpen r).ι)
  obtain ⟨_, _, hgc⟩ := smoothProperConnected_of_isPullback (hY'.paste_vert hX')
  have : GeometricallyConnected (g' ≫ b) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := 𝟙 _) (snd := g' ≫ b)
        (f := g' ≫ b ≫ hU.isoSpec.hom) (g := hU.isoSpec.hom)
        (CommSq.mk (by rw [Category.id_comp, Category.assoc]))) hgc
  -- the module and its trivialization on the closed piece
  let M := (Scheme.Modules.pullback p).obj L'.obj
  let ζ := (nonempty_pullback_pullback_iso_unit g' p (pullback.fst g₁ p) g₁ hY'.w.symm
    L'.obj hL₁').some
  have hsurj := ((ConcreteCategory.isIso_iff_bijective _).mp hiso).2
  -- the trivialization on the fibre over `s`
  let x : (S.basicOpen r).toScheme := ⟨s, hsU⟩
  let m : b.fiber x ⟶ X.hom.fiber s :=
    pullback.lift _ _ (fiberι_fst_comp_eq X.hom x)
  have heF := nonempty_pullback_pullback_iso_unit (b.fiberι x ≫ p) (pullback.fst X.hom e) m
    (X.hom.fiberι s) (by rw [Category.assoc, liftAffineOpen_fst]; exact (pullback.lift_fst _ _ _).symm)
    L.obj hLs
  obtain ⟨σ, hσ⟩ := exists_isIso_fiber_pullback b g' x M ζ hsurj
    ((Scheme.Modules.pullbackComp (b.fiberι x) p).app _ ≪≫ heF.some)
  -- transport to the pullback of `L` along `X ×_S U ⟶ X`
  let κ : M ≅ (Scheme.Modules.pullback (pullback.fst X.hom (S.basicOpen r).ι)).obj L.obj :=
    (Scheme.Modules.pullbackComp p (pullback.fst X.hom e)).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr (liftAffineOpen_fst X.hom hV hU hUV)).app L.obj
  have hfin : IsIso ((Scheme.Modules.pullback (b.fiberι x)).map (σ ≫ κ.hom)) := by
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' hσ (Iso.isIso_hom ((Scheme.Modules.pullback (b.fiberι x)).mapIso κ))
  exact ⟨S.basicOpen r, hsU, σ ≫ κ.hom, hfin⟩

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
