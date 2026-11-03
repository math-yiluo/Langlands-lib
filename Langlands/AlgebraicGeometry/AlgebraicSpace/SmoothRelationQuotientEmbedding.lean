import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Scheme quotients from maps with exact relation fibers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

variable {S : Scheme.{u}} {U : Over S} (R : AlgebraicSpace S)
  (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
  (h : IsEquivalenceRelation R s t)
  {F : Presheaf S} (a : (schemeYoneda S).obj U ⟶ F) (ha : s ≫ a = t ≫ a)

/-- A map with exactly the relation as its kernel embeds the pointwise quotient. -/
theorem mono_quotientPresheafDesc
    (hker : ∀ (T : Over S) (x y : ((schemeYoneda S).obj U).obj (op T)),
      a.app (op T) x = a.app (op T) y ↔ relation R s t T x y) :
    Mono (quotientPresheafDesc R s t h a ha) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro x y hxy
  exact Quotient.sound ((hker T.unop x y).mp hxy)

/-- Sheafification preserves the embedding into any etale sheaf. -/
theorem mono_quotientSheafDesc
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hker : ∀ (T : Over S) (x y : ((schemeYoneda S).obj U).obj (op T)),
      a.app (op T) x = a.app (op T) y ↔ relation R s t T x y) :
    Mono (quotientSheafDesc R s t h a ha hF) := by
  let : Mono (quotientPresheafDesc R s t h a ha) :=
    mono_quotientPresheafDesc R s t h a ha hker
  let J := Scheme.etaleTopology.over S
  change Mono (sheafifyLift J (quotientPresheafDesc R s t h a ha) hF)
  let : Mono (sheafifyMap J (quotientPresheafDesc R s t h a ha)) := by
    change Mono ((presheafToSheaf J (Type (u + 1))).map
      (quotientPresheafDesc R s t h a ha)).hom
    infer_instance
  have heq : sheafifyMap J (quotientPresheafDesc R s t h a ha) ≫
      (isoSheafify J hF).inv = sheafifyLift J (quotientPresheafDesc R s t h a ha) hF := by
    apply sheafifyLift_unique
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    change quotientPresheafDesc R s t h a ha ≫
      ((isoSheafify J hF).hom ≫ (isoSheafify J hF).inv) = _
    simp
  rw [← heq]
  infer_instance

variable {R s t}

/-- A smooth relation with a locally finite type scheme of objects has a scheme
quotient whenever an actual scheme map has exactly its full relation fibers. -/
theorem exists_scheme_quotient_of_map_kernel
    (h : IsEquivalenceRelation R s t)
    (hsm : HasSmoothProjections R s t) (hU : LocallyOfFiniteType U.hom)
    (Y : Over S) (r : U ⟶ Y)
    (hker : ∀ (T : Over S) (x y : T ⟶ U),
      x ≫ r = y ≫ r ↔ relation R s t T ⟨x⟩ ⟨y⟩) :
    ∃ (Q : Over S) (q : U ⟶ Q) (j : Q ⟶ Y),
      q ≫ j = r ∧ Mono j.left ∧ Smooth q.left ∧ Surjective q.left ∧
        ∀ (T : Over S) (x y : T ⟶ U),
          x ≫ q = y ≫ q ↔ relation R s t T ⟨x⟩ ⟨y⟩ := by
  obtain ⟨hF, hd, _, hqsm, hqsurj, W, b, hbe, hbs, hW⟩ :=
    smoothRelationQuotient S U R s t h hsm hU
  let X : AlgebraicSpace S :=
    ⟨⟨(quotientSheaf R s t h).obj, hF⟩, hd, W, b, hbe, hbs⟩
  let a := (schemeYoneda S).map r
  have ha : s ≫ a = t ≫ a := by
    ext T z
    apply ULift.ext
    exact (hker T.unop (s.app T z).down (t.app T z).down).mpr ⟨z, rfl, rfl⟩
  have hY : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      ((schemeYoneda S).obj Y) :=
    (((schemeSheaf S).obj Y).property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))
  have hker' : ∀ (T : Over S) (x y : ((schemeYoneda S).obj U).obj (op T)),
      a.app (op T) x = a.app (op T) y ↔ relation R s t T x y := by
    intro T x y
    exact (ULift.ext_iff.trans (hker T x.down y.down))
  let f : X.presheaf ⟶ (schemeYoneda S).obj Y :=
    quotientSheafDesc R s t h a ha hY
  have : Mono f := mono_quotientSheafDesc R s t h a ha hY hker'
  obtain ⟨w, hw⟩ := (schemeYoneda S).map_surjective (b ≫ f)
  have hwft : LocallyOfFiniteType w.left := by
    have : LocallyOfFiniteType (w.left ≫ Y.hom) := by
      rw [Over.w w]
      exact hW
    exact locallyOfFiniteType_of_comp w.left Y.hom
  obtain ⟨Q, ⟨e⟩⟩ := monomorphismLocallyFiniteTypeScheme S X Y f inferInstance
    ⟨W, b, w, hbe, hbs, hw.symm, hwft⟩
  let q : U ⟶ Q := (schemeYoneda S).preimage (quotientMap R s t h ≫ e.inv)
  have hq : (schemeYoneda S).map q ≫ e.hom = quotientMap R s t h := by
    dsimp [q]
    rw [Functor.map_preimage]
    simp
  have hsq : IsPullback (𝟙 ((schemeYoneda S).obj U))
      ((schemeYoneda S).map q) (quotientMap R s t h) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hq.symm⟩
  let j : Q ⟶ Y := (schemeYoneda S).preimage (e.hom ≫ f)
  have hj : (schemeYoneda S).map j = e.hom ≫ f :=
    (schemeYoneda S).map_preimage _
  have : Mono j := (schemeYoneda S).mono_of_mono_map (by rw [hj]; infer_instance)
  have hqr : q ≫ j = r := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, hj, ← Category.assoc, hq]
    exact quotientMap_desc R s t h a ha hY
  refine ⟨Q, q, j, hqr, inferInstance, hqsm.projection e.hom (𝟙 _) q hsq,
    hqsurj.projection e.hom (𝟙 _) q hsq, ?_⟩
  intro T x y
  rw [← hker T x y, ← hqr, ← Category.assoc, ← Category.assoc]
  exact (cancel_mono j).symm

/-- Actual quotient data, retaining its map into the ambient scheme and all fibers. -/
structure SchemeQuotientEmbedding (R : AlgebraicSpace S)
    (s t : R.presheaf ⟶ (schemeYoneda S).obj U) (Y : Over S) (r : U ⟶ Y) where
  scheme : Over S
  projection : U ⟶ scheme
  embedding : scheme ⟶ Y
  fac : projection ≫ embedding = r
  mono_embedding : Mono embedding.left
  smooth_projection : Smooth projection.left
  surjective_projection : Surjective projection.left
  fibers : ∀ (T : Over S) (x y : T ⟶ U),
    x ≫ projection = y ≫ projection ↔ relation R s t T ⟨x⟩ ⟨y⟩

/-- Choose an actual scheme quotient with its smooth surjective projection. -/
def schemeQuotientOfMapKernel
    (h : IsEquivalenceRelation R s t)
    (hsm : HasSmoothProjections R s t) (hU : LocallyOfFiniteType U.hom)
    (Y : Over S) (r : U ⟶ Y)
    (hker : ∀ (T : Over S) (x y : T ⟶ U),
      x ≫ r = y ≫ r ↔ relation R s t T ⟨x⟩ ⟨y⟩) :
    SchemeQuotientEmbedding R s t Y r :=
  Classical.choice (by
    obtain ⟨Q, q, j, hqr, hm, hqsm, hqsurj, hfib⟩ :=
      exists_scheme_quotient_of_map_kernel h hsm hU Y r hker
    exact ⟨⟨Q, q, j, hqr, hm, hqsm, hqsurj, hfib⟩⟩)

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
