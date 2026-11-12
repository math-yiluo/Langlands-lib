import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Closedness of the relation under a finite cover with separated quotient

A finite surjective cartesian cover whose relation is the kernel pair of a map to a
separated scheme makes the relation map of the covered relation a closed immersion.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open EtaleEquivalenceRelation

/-- The kernel pair of a map to a separated scheme is closed in the product. -/
theorem isClosedImmersion_lift_of_isPullback {R U M : Scheme.{u}}
    {t s : R ⟶ U} (q : U ⟶ M) [M.IsSeparated] (hq : IsPullback t s q q) :
    IsClosedImmersion (prod.lift t s) := by
  have hdiag : IsPullback (t ≫ q) (prod.lift t s)
      (prod.lift (𝟙 M) (𝟙 M)) (prod.map q q) := by
    refine IsPullback.mk' ?_ ?_ ?_
    · ext <;> simp [hq.w]
    · intro T a b _ hab
      apply hq.hom_ext
      · simpa using congrArg (fun k => k ≫ prod.fst) hab
      · simpa using congrArg (fun k => k ≫ prod.snd) hab
    · intro T a b hab
      have ht : (b ≫ prod.fst) ≫ q = a := by
        simpa using (congrArg (fun k => k ≫ prod.fst) hab).symm
      have hs : (b ≫ prod.snd) ≫ q = a := by
        simpa using (congrArg (fun k => k ≫ prod.snd) hab).symm
      refine ⟨hq.lift (b ≫ prod.fst) (b ≫ prod.snd) (ht.trans hs.symm), ?_, ?_⟩
      · simpa using ht
      · ext <;> simp
  exact MorphismProperty.of_isPullback hdiag inferInstance

private theorem isFinite_prod_map_self {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    IsFinite (prod.map f f) := by
  have hleft (Z : Scheme.{u}) : IsFinite (prod.map f (𝟙 Z)) :=
    MorphismProperty.of_isPullback (IsPullback.of_prod_fst_with_id f Z) inferInstance
  have : IsFinite (prod.map (𝟙 Y) f) := by
    convert (inferInstance : IsFinite ((prod.braiding Y X).hom ≫
      prod.map f (𝟙 Y) ≫ (prod.braiding Y Y).hom)) using 1
    ext <;> simp
  have hfactor : prod.map f f = prod.map f (𝟙 X) ≫ prod.map (𝟙 Y) f := by simp
  rw [hfactor]
  infer_instance

/-- If an étale equivalence relation `E` has a finite surjective cartesian cover `E'` whose
relation is the kernel pair of a map `q : E'.U ⟶ M` to a separated scheme, then
`(t, s) : E.R ⟶ E.U ⨯ E.U` is a closed immersion. -/
theorem isClosedImmersion_lift_of_separated_quotient {E E' : EtaleEquivalenceRelation.{u}}
    {φ : E'.U ⟶ E.U} {g : E'.R ⟶ E.R} (hcart : IsCartesianHom E' E φ g) [IsFinite φ]
    [Surjective φ] {M : Scheme.{u}} [M.IsSeparated] (q : E'.U ⟶ M)
    (hq : IsPullback E'.t E'.s q q) :
    IsClosedImmersion (prod.lift E.t E.s) := by
  obtain ⟨ht, hpb⟩ := hcart
  have : IsClosedImmersion (prod.lift E'.t E'.s) :=
    isClosedImmersion_lift_of_isPullback q hq
  have : IsFinite (prod.map φ φ) := isFinite_prod_map_self φ
  have hcomp : g ≫ prod.lift E.t E.s = prod.lift E'.t E'.s ≫ prod.map φ φ := by
    ext
    · simpa using ht
    · simpa using hpb.w
  have : UniversallyClosed (g ≫ prod.lift E.t E.s) := by
    rw [hcomp]
    infer_instance
  have : Surjective g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : UniversallyClosed (prod.lift E.t E.s) :=
    UniversallyClosed.of_comp_surjective g _
  have := E.mono_lift
  have := E.etale_t
  have : LocallyOfFiniteType (prod.lift E.t E.s ≫ prod.fst) := by
    simpa using (inferInstance : LocallyOfFiniteType E.t)
  have : LocallyOfFiniteType (prod.lift E.t E.s) :=
    locallyOfFiniteType_of_comp _ prod.fst
  have : IsProper (prod.lift E.t E.s) := {}
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- Under the hypotheses of `isClosedImmersion_lift_of_separated_quotient`, an affine
`E.U` has an affine relation scheme `E.R`. -/
theorem isAffine_R_of_separated_quotient {E E' : EtaleEquivalenceRelation.{u}}
    [IsAffine E.U] {φ : E'.U ⟶ E.U} {g : E'.R ⟶ E.R} (hcart : IsCartesianHom E' E φ g)
    [IsFinite φ] [Surjective φ] {M : Scheme.{u}} [M.IsSeparated] (q : E'.U ⟶ M)
    (hq : IsPullback E'.t E'.s q q) :
    IsAffine E.R := by
  have := isClosedImmersion_lift_of_separated_quotient hcart q hq
  have : IsAffine (E.U ⨯ E.U) := IsAffine.of_isIso (prodIsoPullback E.U E.U).hom
  exact isAffine_of_isAffineHom (prod.lift E.t E.s)

end Langlands.AlgebraicGeometry.QuasiAffineApproximation
