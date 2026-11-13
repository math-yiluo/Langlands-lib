import Langlands.AbelianScheme.RelativeGlobalUnits
import Langlands.AlgebraicGeometry.Units.RelativeGlobalUnitsGluing
import Langlands.AlgebraicGeometry.Picard.SmoothUnitBaseChange
import Langlands.TauCeti.Algebra.Polynomial.Laurent.Smooth

/-! # The multiplicative group represents global units of abelian schemes over an affine base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite LaurentPolynomial

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

variable (R : Type u) [CommRing R]

/-- The multiplicative group `Spec R[T;T⁻¹]` over `Spec R`. -/
abbrev multiplicativeGroupOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))

/-- The multiplicative group over `Spec R` is smooth. -/
lemma multiplicativeGroupOver_smooth : Smooth (multiplicativeGroupOver R).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
    RingHom.smooth_algebraMap]
  infer_instance

/-- The coordinate `T`, as a global unit on the multiplicative group. -/
def coordinateUnit : Γ((multiplicativeGroupOver R).left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).inv.hom.toMonoidHom
    (isUnit_T (R := R) 1).unit

lemma coordinateUnit_val :
    (coordinateUnit R : Γ((multiplicativeGroupOver R).left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).inv (T 1) := rfl

/-- Two ring maps out of `R[T;T⁻¹]` agreeing on constants and on `T` are equal. -/
lemma laurent_ringHom_ext {S : Type*} [CommRing S] {g h : R[T;T⁻¹] →+* S}
    (hC : ∀ r, g (C r) = h (C r)) (hT : g (T 1) = h (T 1)) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.coe_comp, Function.comp_apply, algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C] using hC r
  · simpa only [RingHom.coe_comp, Function.comp_apply, algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using hT

variable {R}

/-- The ring map out of the base induced by a scheme over `Spec R`. -/
abbrev baseRingMap (V : Over (Spec (CommRingCat.of R))) :
    CommRingCat.of R ⟶ Γ(V.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop

/-- A morphism into the multiplicative group restricts on constants to the
structure map. -/
lemma algebraMap_comp_appTop (V : Over (Spec (CommRingCat.of R)))
    (j : V ⟶ multiplicativeGroupOver R) :
    CommRingCat.ofHom (algebraMap R R[T;T⁻¹]) ≫
        (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).inv ≫ j.left.appTop =
      baseRingMap V := by
  have hw := congrArg Scheme.Hom.appTop (Over.w j)
  rw [Scheme.Hom.comp_appTop] at hw
  change _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop
  rw [← hw]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))).appTop ≫ j.left.appTop
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Morphisms over `Spec R` into the multiplicative group correspond bijectively
to global units, by pulling back the coordinate unit. -/
lemma coordinateUnit_pullback_bijective (V : Over (Spec (CommRingCat.of R))) :
    Function.Bijective (fun j : V ⟶ multiplicativeGroupOver R =>
      Units.map j.left.appTop.hom.toMonoidHom (coordinateUnit R)) := by
  constructor
  · intro j l hjl
    have hv := congrArg Units.val hjl
    simp only [Units.coe_map, coordinateUnit_val] at hv
    apply Over.OverMorphism.ext
    apply ext_to_Spec
    apply CommRingCat.hom_ext
    apply laurent_ringHom_ext
    · intro r
      have hj := congrArg (fun q => q.hom r) (algebraMap_comp_appTop V j)
      have hl := congrArg (fun q => q.hom r) (algebraMap_comp_appTop V l)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        CommRingCat.hom_ofHom] at hj hl
      rw [← C_eq_algebraMap] at hj hl
      exact hj.trans hl.symm
    · exact hv
  · intro v
    let ψ : CommRingCat.of R[T;T⁻¹] ⟶ Γ(V.left, ⊤) :=
      CommRingCat.ofHom (eval₂ (baseRingMap V).hom v)
    let g : V.left ⟶ multiplicativeGroupOver R |>.left :=
      ΓSpec.adjunction.homEquiv V.left (op (CommRingCat.of R[T;T⁻¹])) ψ.op
    have hg : g.appTop = (Scheme.ΓSpecIso (CommRingCat.of R[T;T⁻¹])).hom ≫ ψ :=
      ΓSpec_adjunction_homEquiv_eq ψ
    have hw : g ≫ (multiplicativeGroupOver R).hom = V.hom := by
      apply ext_to_Spec
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (g ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop
      rw [Scheme.Hom.comp_appTop, hg, Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
      apply CommRingCat.hom_ext
      ext r
      simp [ψ]
    refine ⟨Over.homMk g hw, ?_⟩
    apply Units.ext
    simp only [Units.coe_map, coordinateUnit_val, Over.homMk_left]
    rw [hg]
    simp [ψ, CommRingCat.hom_comp, Iso.inv_hom_id_apply, eval₂_T]

variable (A : AbelianScheme (Spec (CommRingCat.of R)))

/-- The coordinate unit pulled back to `G_m ×_{Spec R} A`. -/
def universalUnit : RelativeGlobalUnits.sections A.X.hom (multiplicativeGroupOver R) :=
  relativeUnitsPullback A _ (coordinateUnit R)

/-- Pulling back the universal unit along a test point is the pullback of
the corresponding base unit. -/
lemma restriction_universalUnit (V : Over (Spec (CommRingCat.of R)))
    (j : V ⟶ multiplicativeGroupOver R) :
    RelativeGlobalUnits.restriction A.X.hom j (universalUnit A) =
      relativeUnitsPullback A V
        (Units.map j.left.appTop.hom.toMonoidHom (coordinateUnit R)) :=
  relativeUnitsPullback_map A j _ ((relativeProjection A.X.hom).naturality j) _

/-- Test points of the multiplicative group correspond bijectively to global
units of the relative abelian scheme. -/
lemma restriction_universalUnit_bijective (V : Over (Spec (CommRingCat.of R))) :
    Function.Bijective (fun j : V ⟶ multiplicativeGroupOver R =>
      RelativeGlobalUnits.restriction A.X.hom j (universalUnit A)) := by
  have he : (fun j : V ⟶ multiplicativeGroupOver R =>
      RelativeGlobalUnits.restriction A.X.hom j (universalUnit A)) =
      (relativeGlobalUnitsEquiv A (universalGlobalFunctions A) V) ∘
        (fun j => Units.map j.left.appTop.hom.toMonoidHom (coordinateUnit R)) := by
    funext j
    exact restriction_universalUnit A V j
  rw [he]
  exact (relativeGlobalUnitsEquiv A _ V).bijective.comp (coordinateUnit_pullback_bijective V)

/-- The multiplicative group represents the actual relative global-unit presheaf. -/
def unitSchemeIso :
    (AlgebraicSpace.schemeYoneda _).obj (multiplicativeGroupOver R) ≅
      RelativeGlobalUnits.presheaf A.X.hom :=
  RelativeGlobalUnits.fromUniversalUnitIsoOfAffine A.X.hom _ (universalUnit A) fun V _ => by
    have hb := restriction_universalUnit_bijective A V
    constructor
    · intro x y hxy
      exact ULift.ext _ _ (hb.1 (congrArg ULift.down hxy))
    · intro t
      obtain ⟨j, hj⟩ := hb.2 t.down
      exact ⟨⟨j⟩, ULift.ext _ _ hj⟩

/-- Every abelian scheme over an affine base has smooth relative automorphism
schemes for all its line bundles on all test schemes. -/
theorem hasSmoothRelativeAutomorphismSchemes :
    PicardGroupoid.HasSmoothRelativeAutomorphismSchemes A.X.hom :=
  PicardGroupoid.hasSmoothRelativeAutomorphismSchemes_of_unitScheme A.X.hom _
    (unitSchemeIso A) (multiplicativeGroupOver_smooth R)

end Langlands.AbelianScheme
