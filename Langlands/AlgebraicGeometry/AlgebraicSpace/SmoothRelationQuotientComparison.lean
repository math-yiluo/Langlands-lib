import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison

/-! # Kernel pair and recognition of the canonical etale quotient -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

variable {S : Scheme.{u}} {U : Over S} (R : AlgebraicSpace S)
  (s t : R.presheaf ⟶ (schemeYoneda S).obj U) (h : IsEquivalenceRelation R s t)

/-- The arrow sheaf of an algebraic space is a sheaf for the big etale topology. -/
lemma isSheaf_etale_presheaf :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) R.presheaf :=
  (_root_.CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
    (R.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))

/-- The functor of points of a scheme is a sheaf for the big etale topology. -/
lemma isSheaf_etale_schemeYoneda (V : Over S) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) ((schemeYoneda S).obj V) :=
  (_root_.CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
    (((schemeSheaf S).obj V).property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))

/-- Two scheme points with the same class in the etale quotient are related by an
actual arrow section. -/
lemma relation_of_quotientMap_eq {T : Over S} (x y : ((schemeYoneda S).obj U).obj (op T))
    (hxy : (quotientMap R s t h).app (op T) x = (quotientMap R s t h).app (op T) y) :
    relation R s t T x y := by
  let J := Scheme.etaleTopology.over S
  let qx := (toQuotientPresheaf R s t h).app (op T) x
  let qy := (toQuotientPresheaf R s t h).app (op T) y
  have hmem : Presheaf.equalizerSieve (F := quotientPresheaf R s t h) qx qy ∈ J T :=
    Presheaf.equalizerSieve_mem J (toSheafify J (quotientPresheaf R s t h)) qx qy hxy
  let Sv := Presheaf.equalizerSieve (F := quotientPresheaf R s t h) qx qy
  have hrel : ∀ ⦃V : Over S⦄ (f : V ⟶ T), Sv.arrows f →
      relation R s t V (((schemeYoneda S).obj U).map f.op x)
        (((schemeYoneda S).obj U).map f.op y) :=
    fun _ _ hf ↦ Quotient.exact hf
  let fam : Presieve.FamilyOfElements R.presheaf Sv.arrows :=
    fun _ f hf ↦ (hrel f hf).choose
  have fam_s : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : Sv.arrows f),
      s.app (op V) (fam f hf) = ((schemeYoneda S).obj U).map f.op x :=
    fun _ f hf ↦ (hrel f hf).choose_spec.1
  have fam_t : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : Sv.arrows f),
      t.app (op V) (fam f hf) = ((schemeYoneda S).obj U).map f.op y :=
    fun _ f hf ↦ (hrel f hf).choose_spec.2
  have hcompat : fam.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    apply (h Z).1
    refine Prod.ext ?_ ?_
    · change s.app (op Z) (R.presheaf.map g₁.op (fam f₁ hf₁)) =
        s.app (op Z) (R.presheaf.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply s, NatTrans.naturality_apply s, fam_s f₁ hf₁, fam_s f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        ← op_comp, hcomm]
    · change t.app (op Z) (R.presheaf.map g₁.op (fam f₁ hf₁)) =
        t.app (op Z) (R.presheaf.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply t, NatTrans.naturality_apply t, fam_t f₁ hf₁, fam_t f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        ← op_comp, hcomm]
  obtain ⟨r, hr, -⟩ := isSheaf_etale_presheaf R Sv hmem fam hcompat
  refine ⟨r, ?_, ?_⟩
  · refine (isSheaf_etale_schemeYoneda U Sv hmem).isSeparatedFor.ext fun V f hf ↦ ?_
    rw [← NatTrans.naturality_apply s, hr f hf, fam_s f hf]
  · refine (isSheaf_etale_schemeYoneda U Sv hmem).isSeparatedFor.ext fun V f hf ↦ ?_
    rw [← NatTrans.naturality_apply t, hr f hf, fam_t f hf]

/-- Equality in the canonical etale quotient is exactly the actual-arrow relation. -/
theorem quotientMap_eq_iff {T : Over S} (x y : ((schemeYoneda S).obj U).obj (op T)) :
    (quotientMap R s t h).app (op T) x = (quotientMap R s t h).app (op T) y ↔
      relation R s t T x y := by
  refine ⟨relation_of_quotientMap_eq R s t h x y, ?_⟩
  rintro ⟨r, rfl, rfl⟩
  have hq : (toQuotientPresheaf R s t h).app (op T) (s.app (op T) r) =
      (toQuotientPresheaf R s t h).app (op T) (t.app (op T) r) :=
    Quotient.sound ⟨r, rfl, rfl⟩
  exact congrArg ((toSheafify (Scheme.etaleTopology.over S)
    (quotientPresheaf R s t h)).app (op T)) hq

/-- The arrow space is the kernel pair of the canonical etale quotient map. -/
theorem isPullback_quotientMap :
    IsPullback s t (quotientMap R s t h) (quotientMap R s t h) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext r
    exact (quotientMap_eq_iff R s t h _ _).2 ⟨r, rfl, rfl⟩
  · rintro r₁ r₂ ⟨h₁, h₂⟩
    exact (h T.unop).1 (Prod.ext h₁ h₂)
  · intro x y hxy
    exact (quotientMap_eq_iff R s t h (T := T.unop) x y).1 hxy

/-- The canonical quotient map is locally surjective for the big etale topology. -/
theorem isLocallySurjective_quotientMap :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (quotientMap R s t h) := by
  have : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (toQuotientPresheaf R s t h) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun _ ↦ Quotient.mk_surjective
  have : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (toSheafify (Scheme.etaleTopology.over S) (quotientPresheaf R s t h)) :=
    Presheaf.isLocallySurjective_toSheafify' _ _
  change Presheaf.IsLocallySurjective _ (toQuotientPresheaf R s t h ≫
    toSheafify (Scheme.etaleTopology.over S) (quotientPresheaf R s t h))
  infer_instance

variable {W : Over S} {F : Presheaf S}

/-- The canonical etale quotient agrees with any etale sheaf presented by a scheme
over `U` that sees the same identifications.

Here `g` maps the presenting scheme `W` to `U` so that every class of the quotient
is etale locally the class of a point of `W`, and `b` presents `F` etale locally
with the identifications of the relation pulled back along `g`. -/
def quotientSheafIsoOfPresentation
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (g : (schemeYoneda S).obj W ⟶ (schemeYoneda S).obj U)
    (b : (schemeYoneda S).obj W ⟶ F)
    (hg : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (g ≫ quotientMap R s t h))
    (hb : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩ ↔
        relation R s t T (g.app (op T) ⟨x⟩) (g.app (op T) ⟨y⟩)) :
    (quotientSheaf R s t h).obj ≅ F :=
  commonEtalePresentationIso (quotientSheaf R s t h).property hF
    (g ≫ quotientMap R s t h) b hg hb fun T x y ↦
      (quotientMap_eq_iff R s t h (g.app (op T) ⟨x⟩) (g.app (op T) ⟨y⟩)).trans (hker T x y).symm

/-- The recognition isomorphism carries the composite presentation to `b`. -/
theorem quotientSheafIsoOfPresentation_hom_fac
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (g : (schemeYoneda S).obj W ⟶ (schemeYoneda S).obj U)
    (b : (schemeYoneda S).obj W ⟶ F)
    (hg : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (g ≫ quotientMap R s t h))
    (hb : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩ ↔
        relation R s t T (g.app (op T) ⟨x⟩) (g.app (op T) ⟨y⟩)) :
    g ≫ quotientMap R s t h ≫ (quotientSheafIsoOfPresentation R s t h hF g b hg hb hker).hom =
      b := by
  rw [← Category.assoc]
  exact commonEtalePresentationIso_hom_fac _ _ _ _ _ _ _

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
