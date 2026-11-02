import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineRelationStatement
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Affineness and closedness of the relation scheme

A finite surjective cartesian cover with an affine quotient makes the relation map
universally closed. Its monomorphism and local finite type then make it a closed immersion.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

private theorem closedImmersion_pair_of_pullback {R U M : Scheme.{u}}
    {t s : R ⟶ U} (q : U ⟶ M) [IsAffine M] (hq : IsPullback t s q q) :
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

/-- The relation scheme is affine and its map into the product is a closed immersion. -/
theorem etaleEquivalenceRelationAffineRelation :
    EtaleEquivalenceRelationAffineRelationStatement.{u} := by
  intro E hU hcover
  have := hU
  obtain ⟨E', f, g, ⟨ht, hcart⟩, hf, hsurj, M, q, hM, hq, _, _, _⟩ := hcover
  have := hf
  have := hsurj
  have := hM
  have : IsClosedImmersion (prod.lift E'.t E'.s) :=
    closedImmersion_pair_of_pullback q hq
  have : IsFinite (prod.map f f) := isFinite_prod_map_self f
  have hcomp : g ≫ prod.lift E.t E.s = prod.lift E'.t E'.s ≫ prod.map f f := by
    ext
    · simpa using ht
    · simpa using hcart.w
  have : UniversallyClosed (g ≫ prod.lift E.t E.s) := by
    rw [hcomp]
    infer_instance
  have : Surjective g := MorphismProperty.of_isPullback hcart.flip inferInstance
  have : UniversallyClosed (prod.lift E.t E.s) :=
    UniversallyClosed.of_comp_surjective g _
  have := E.mono_lift
  have := E.etale_t
  have : LocallyOfFiniteType (prod.lift E.t E.s ≫ prod.fst) := by
    simpa using (inferInstance : LocallyOfFiniteType E.t)
  have : LocallyOfFiniteType (prod.lift E.t E.s) :=
    locallyOfFiniteType_of_comp _ prod.fst
  have : IsProper (prod.lift E.t E.s) := {}
  have : IsClosedImmersion (prod.lift E.t E.s) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  have : IsAffine (E.U ⨯ E.U) := IsAffine.of_isIso (prodIsoPullback E.U E.U).hom
  exact ⟨isAffine_of_isAffineHom (prod.lift E.t E.s), inferInstance⟩

end Langlands.AlgebraicGeometry
