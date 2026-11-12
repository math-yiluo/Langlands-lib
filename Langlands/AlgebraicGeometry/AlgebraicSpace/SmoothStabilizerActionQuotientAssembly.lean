import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison

/-!
# Action quotients from a smooth relation space

Let a group scheme `G` act on a scheme `V` over `S`. Suppose given an algebraic space `B`
with two maps `s', t' : B ⟶ V` that jointly embed `B` into `V × V`, have smooth
projections on an etale atlas, and receive an etale-locally surjective map
`q : G × V ⟶ B` with `q ≫ s' = a` and `q ≫ t' = pr₂`. Then `(s', t')` is an equivalence
relation, the canonical etale quotient of `V` by it is an algebraic space and an fppf
quotient of `V` by the action, and every fppf quotient of `V` by the action has a smooth
surjective quotient map and is locally of finite type over `S` when `V` is.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section Transport

variable {S : Scheme.{u}} {F₁ F₂ F₃ : Presheaf S}

/-- Composing a smooth transformation with a presheaf isomorphism preserves smoothness. -/
theorem IsSmooth.comp_iso {f : F₁ ⟶ F₂} (hf : IsSmooth f) (e : F₂ ≅ F₃) :
    IsSmooth (f ≫ e.hom) := by
  have : MorphismProperty.RespectsIso @Smooth.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr hf

end Transport

namespace SmoothStabilizerActionQuotient

open SmoothRelationQuotient

variable {S : Scheme.{u}}

/-- The underlying presheaf of an algebraic space is a sheaf for the big etale topology. -/
lemma isSheaf_etale (B : AlgebraicSpace S) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) B.presheaf :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (B.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))

/-- The functor of points of a scheme is a sheaf for the big etale topology. -/
lemma isSheaf_etale_scheme (V : Over S) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) ((schemeYoneda S).obj V) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    ((((schemeSheaf S).obj V).property).of_le
      (Sites.etaleTopologyOver_le_fppfTopologyOver S))

/-- An fppf sheaf is separated for the big etale topology. -/
lemma isSheaf_etale_fppfSheaf (F : FppfSheaf S) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) F.obj :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (F.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))

section Relation

variable {V : Over S} (B : AlgebraicSpace S) {s' t' : B.presheaf ⟶ (schemeYoneda S).obj V}

/-- For a jointly injective pair of maps out of an algebraic space, the relation it
defines is etale local: if two points become related on an etale covering sieve, they
are related. The local witnesses agree on overlaps by joint injectivity and glue. -/
theorem relation_of_sieve
    (hinj : ∀ T : Over S, Function.Injective
      (fun r : B.sections T ↦ (s'.app (op T) r, t'.app (op T) r)))
    {T : Over S} (x y : ((schemeYoneda S).obj V).obj (op T)) (R : Sieve T)
    (hR : R ∈ Scheme.etaleTopology.over S T)
    (hloc : ∀ ⦃W : Over S⦄ (g : W ⟶ T), R.arrows g →
      relation B s' t' W (((schemeYoneda S).obj V).map g.op x)
        (((schemeYoneda S).obj V).map g.op y)) :
    relation B s' t' T x y := by
  let P := (schemeYoneda S).obj V
  let fam : Presieve.FamilyOfElements B.presheaf R.arrows :=
    fun _ g hg ↦ (hloc g hg).choose
  have fam_s : ∀ ⦃W : Over S⦄ (g : W ⟶ T) (hg : R.arrows g),
      s'.app (op W) (fam g hg) = P.map g.op x :=
    fun _ g hg ↦ (hloc g hg).choose_spec.1
  have fam_t : ∀ ⦃W : Over S⦄ (g : W ⟶ T) (hg : R.arrows g),
      t'.app (op W) (fam g hg) = P.map g.op y :=
    fun _ g hg ↦ (hloc g hg).choose_spec.2
  have hcompat : fam.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    apply hinj Z
    refine Prod.ext ?_ ?_
    · change s'.app (op Z) (B.presheaf.map g₁.op (fam f₁ hf₁)) =
        s'.app (op Z) (B.presheaf.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply s', NatTrans.naturality_apply s',
        fam_s f₁ hf₁, fam_s f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
    · change t'.app (op Z) (B.presheaf.map g₁.op (fam f₁ hf₁)) =
        t'.app (op Z) (B.presheaf.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply t', NatTrans.naturality_apply t',
        fam_t f₁ hf₁, fam_t f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  obtain ⟨r, hr, -⟩ := isSheaf_etale B R hR fam hcompat
  refine ⟨r, ?_, ?_⟩
  · refine ((isSheaf_etale_scheme V) R hR).isSeparatedFor.ext fun W g hg ↦ ?_
    rw [← NatTrans.naturality_apply s', hr g hg, fam_s g hg]
  · refine ((isSheaf_etale_scheme V) R hR).isSeparatedFor.ext fun W g hg ↦ ?_
    rw [← NatTrans.naturality_apply t', hr g hg, fam_t g hg]

end Relation

section Action

variable {G : GroupScheme S} {V : Over S} (a : SchemeAction G V)
  (B : AlgebraicSpace S) {s' t' : B.presheaf ⟶ (schemeYoneda S).obj V}
  {q : (schemeYoneda S).obj (G.X ⊗ V) ⟶ B.presheaf}

/-- The orbit relation on points of `V` over a single test scheme: `x = g.y`. -/
def ActRel {T : Over S} (x y : T ⟶ V) : Prop :=
  ∃ g : T ⟶ G.X, x = a.act g y

/-- The pointwise orbit relation is an equivalence relation. -/
lemma actRel_equivalence (T : Over S) : Equivalence (ActRel a (T := T)) where
  refl x := ⟨1, (a.act_one x).symm⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← a.act_mul, inv_mul_cancel, a.act_one]
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', (a.act_mul g g' z).symm⟩

/-- The orbit relation is stable under pullback along test morphisms. -/
lemma ActRel.comp {T W : Over S} {x y : T ⟶ V} (h : ActRel a x y) (f : W ⟶ T) :
    ActRel a (f ≫ x) (f ≫ y) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ≫ g, a.naturality f g y⟩

variable {a B}

/-- Every pair of points of `V` in the same orbit is related by `(s', t')`, with witness
the image under `q` of the corresponding point of `G × V`. -/
lemma relation_of_actRel (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V)) {T : Over S} {x y : T ⟶ V}
    (h : ActRel a x y) : relation B s' t' T ⟨x⟩ ⟨y⟩ := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨q.app (op T) ⟨lift g y⟩, ?_, ?_⟩
  · have := congrArg (fun k ↦ k.app (op T) (⟨lift g y⟩ : ULift (T ⟶ G.X ⊗ V))) hqs
    simpa [SchemeAction.act] using this
  · have := congrArg (fun k ↦ k.app (op T) (⟨lift g y⟩ : ULift (T ⟶ G.X ⊗ V))) hqt
    simpa using this

/-- A related pair of points of `V` is in the same orbit on an etale covering sieve:
locally the witness lifts through the locally surjective map `q`. -/
lemma exists_sieve_actRel (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V))
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    {T : Over S} {x y : T ⟶ V} (h : relation B s' t' T ⟨x⟩ ⟨y⟩) :
    ∃ R : Sieve T, R ∈ Scheme.etaleTopology.over S T ∧
      ∀ ⦃W : Over S⦄ (f : W ⟶ T), R.arrows f → ActRel a (f ≫ x) (f ≫ y) := by
  obtain ⟨r, hrs, hrt⟩ := h
  refine ⟨CategoryTheory.Presheaf.imageSieve q r,
    CategoryTheory.Presheaf.imageSieve_mem (Scheme.etaleTopology.over S) q r, ?_⟩
  rintro W f ⟨⟨α⟩, hα⟩
  have hs := congrArg (fun k ↦ k.app (op W) (⟨α⟩ : ULift (W ⟶ G.X ⊗ V))) hqs
  have ht := congrArg (fun k ↦ k.app (op W) (⟨α⟩ : ULift (W ⟶ G.X ⊗ V))) hqt
  simp only [NatTrans.comp_app, types_comp_apply] at hs ht
  rw [hα, NatTrans.naturality_apply, hrs] at hs
  rw [hα, NatTrans.naturality_apply, hrt] at ht
  have hs' : f ≫ x = α ≫ a.hom := congrArg ULift.down hs
  have ht' : f ≫ y = α ≫ snd G.X V := congrArg ULift.down ht
  refine ⟨α ≫ fst G.X V, ?_⟩
  rw [hs', ht', SchemeAction.act, ← comp_lift, lift_fst_snd, Category.comp_id]

/-- The relation defined by `(s', t')` is exactly the etale sheafified orbit relation. -/
lemma relation_iff (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V))
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    (hinj : ∀ T : Over S, Function.Injective
      (fun r : B.sections T ↦ (s'.app (op T) r, t'.app (op T) r)))
    {T : Over S} (x y : T ⟶ V) :
    relation B s' t' T ⟨x⟩ ⟨y⟩ ↔ ∃ R : Sieve T, R ∈ Scheme.etaleTopology.over S T ∧
      ∀ ⦃W : Over S⦄ (f : W ⟶ T), R.arrows f → ActRel a (f ≫ x) (f ≫ y) := by
  refine ⟨exists_sieve_actRel hqs hqt hq, ?_⟩
  rintro ⟨R, hR, hloc⟩
  exact relation_of_sieve B hinj ⟨x⟩ ⟨y⟩ R hR fun W f hf ↦
    relation_of_actRel hqs hqt (hloc f hf)

/-- The pair `(s', t')` is a monomorphic equivalence relation on `V`. -/
theorem isEquivalenceRelation (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V))
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    (hinj : ∀ T : Over S, Function.Injective
      (fun r : B.sections T ↦ (s'.app (op T) r, t'.app (op T) r))) :
    IsEquivalenceRelation B s' t' := by
  intro T
  refine ⟨hinj T, ?_⟩
  have hiff := relation_iff hqs hqt hq hinj (T := T)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x⟩
    exact relation_of_actRel hqs hqt ((actRel_equivalence a T).refl x)
  · rintro ⟨x⟩ ⟨y⟩ h
    obtain ⟨R, hR, hloc⟩ := (hiff x y).mp h
    exact (hiff y x).mpr ⟨R, hR, fun W f hf ↦ (actRel_equivalence a W).symm (hloc f hf)⟩
  · rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h h'
    obtain ⟨R, hR, hloc⟩ := (hiff x y).mp h
    obtain ⟨R', hR', hloc'⟩ := (hiff y z).mp h'
    refine (hiff x z).mpr ⟨R ⊓ R', (Scheme.etaleTopology.over S).intersection_covering hR hR',
      fun W f hf ↦ (actRel_equivalence a W).trans (hloc f hf.1) (hloc' f hf.2)⟩

end Action

section Quotient

variable {G : GroupScheme S} {V : Over S} {a : SchemeAction G V}
  {B : AlgebraicSpace S} {s' t' : B.presheaf ⟶ (schemeYoneda S).obj V}
  {q : (schemeYoneda S).obj (G.X ⊗ V) ⟶ B.presheaf}

/-- Two maps into an etale sheaf agree once they agree after an etale locally surjective
map. -/
lemma hom_ext_of_isLocallySurjective {A P F : Presheaf S} (p : A ⟶ P)
    (hp : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    (hF : Presieve.IsSheaf (Scheme.etaleTopology.over S) F) {u v : P ⟶ F}
    (huv : p ≫ u = p ≫ v) : u = v := by
  ext T r
  change u.app T r = v.app T r
  refine (hF _ (CategoryTheory.Presheaf.imageSieve_mem _ p r)).isSeparatedFor.ext ?_
  rintro W f ⟨α, hα⟩
  rw [← NatTrans.naturality_apply u, ← NatTrans.naturality_apply v, ← hα]
  exact congrArg (fun k ↦ k.app (op W) α) huv

/-- A map out of `V` into an etale sheaf that is invariant under the action identifies the
two endpoints `s'` and `t'` of the relation space. -/
lemma coequalizes_of_invariant (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V))
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    {F : Presheaf S} (hF : Presieve.IsSheaf (Scheme.etaleTopology.over S) F)
    {k : (schemeYoneda S).obj V ⟶ F}
    (hk : (schemeYoneda S).map a.hom ≫ k = (schemeYoneda S).map (snd G.X V) ≫ k) :
    s' ≫ k = t' ≫ k :=
  hom_ext_of_isLocallySurjective q hq hF (by
    rw [← Category.assoc, hqs, ← Category.assoc, hqt]
    exact hk)

/-- **Action quotients from a relation space.** Let `B` be an algebraic space with maps
`s', t' : B ⟶ V` that are jointly injective on points and have smooth projections on an
etale atlas, and let `q : G × V ⟶ B` be etale locally surjective with `q ≫ s' = a` and
`q ≫ t' = pr₂`. If `V` is locally of finite type over `S`, then the canonical etale quotient
of `V` by `(s', t')` is an algebraic space and an fppf quotient of `V` by the action, and
for every fppf quotient `π : V ⟶ X` of the action by an algebraic space, `π` is smooth and
surjective and `X` is locally of finite type over `S`. -/
theorem actionQuotient_of_relationSpace (hV : LocallyOfFiniteType V.hom)
    (hqs : q ≫ s' = (schemeYoneda S).map a.hom)
    (hqt : q ≫ t' = (schemeYoneda S).map (snd G.X V))
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    (hinj : ∀ T : Over S, Function.Injective
      (fun r : B.sections T ↦ (s'.app (op T) r, t'.app (op T) r)))
    (hsm : HasSmoothProjections B s' t') :
    (∃ (X : AlgebraicSpace S) (π : (schemeSheaf S).obj V ⟶ X.toSheaf),
        IsFppfActionQuotient a π) ∧
      ∀ (X : AlgebraicSpace S) (π : (schemeSheaf S).obj V ⟶ X.toSheaf),
        IsFppfActionQuotient a π →
          IsSmooth π.hom ∧ IsSurjective π.hom ∧ LocallyOfFiniteTypeOverBase X := by
  have h := isEquivalenceRelation hqs hqt hq hinj
  obtain ⟨hF₂, hD₂, -, hsmooth, hsurj, W, c, hc, hcs, hW⟩ :=
    smoothRelationQuotient S V B s' t' h hsm hV
  let X : AlgebraicSpace S := ⟨⟨(quotientSheaf B s' t' h).obj, hF₂⟩, hD₂, W, c, hc, hcs⟩
  let π : (schemeSheaf S).obj V ⟶ X.toSheaf := ObjectProperty.homMk (quotientMap B s' t' h)
  have w : (schemeSheaf S).map a.hom ≫ π = (schemeSheaf S).map (snd G.X V) ≫ π := by
    apply Sheaf.hom_ext
    change (schemeYoneda S).map a.hom ≫ quotientMap B s' t' h =
      (schemeYoneda S).map (snd G.X V) ≫ quotientMap B s' t' h
    rw [← hqs, ← hqt, Category.assoc, Category.assoc, quotientMap_coequalizes]
  have hsheaf : ∀ F : FppfSheaf S,
      CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F.obj :=
    fun F ↦ F.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S)
  have hcoeq : ∀ s : Cofork ((schemeSheaf S).map a.hom) ((schemeSheaf S).map (snd G.X V)),
      s' ≫ s.π.hom = t' ≫ s.π.hom := fun s ↦
    coequalizes_of_invariant hqs hqt hq (isSheaf_etale_fppfSheaf s.pt)
      (congrArg (fun k ↦ k.hom) s.condition)
  have hcol : IsColimit (Cofork.ofπ π w) := by
    refine Cofork.IsColimit.mk _
      (fun s ↦ ObjectProperty.homMk
        (quotientSheafDesc B s' t' h s.π.hom (hcoeq s) (hsheaf s.pt)))
      (fun s ↦ Sheaf.hom_ext (quotientMap_desc B s' t' h _ (hcoeq s) (hsheaf s.pt)))
      (fun s m hm ↦ Sheaf.hom_ext ?_)
    refine quotientSheaf_hom_ext B s' t' h (hsheaf s.pt) ?_
    exact (congrArg (fun k ↦ k.hom) hm).trans
      (quotientMap_desc B s' t' h _ (hcoeq s) (hsheaf s.pt)).symm
  refine ⟨⟨X, π, w, ⟨hcol⟩⟩, ?_⟩
  rintro X' π' ⟨w', ⟨hcol'⟩⟩
  let e : X.toSheaf ≅ X'.toSheaf := hcol.coconePointUniqueUpToIso hcol'
  have he : π ≫ e.hom = π' :=
    hcol.comp_coconePointUniqueUpToIso_hom hcol' WalkingParallelPair.one
  let e' : X.presheaf ≅ X'.presheaf := (sheafToPresheaf _ _).mapIso e
  have hπ' : π'.hom = quotientMap B s' t' h ≫ e'.hom := by
    rw [← he]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hπ']
    exact hsmooth.comp_iso e'
  · rw [hπ']
    exact hsurj.comp_iso e'
  · exact HasAtlasProperty.of_iso (X := X) ⟨W, c, hc, hcs, hW⟩ e'

end Quotient

end SmoothStabilizerActionQuotient

end Langlands.AlgebraicGeometry.AlgebraicSpace
