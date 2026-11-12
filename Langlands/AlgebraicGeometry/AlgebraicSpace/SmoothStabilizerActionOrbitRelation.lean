import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionArrows
import Langlands.AlgebraicGeometry.Picard.SmoothArrowRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothProjectionAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientProof
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # The orbit relation of a group action as a quotient of its arrow relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotient

open SmoothRelationQuotient

variable {S : Scheme.{u}}

/-- The functor of points of a scheme is a sheaf for the big étale topology. -/
lemma isSheaf_etale_representable (U : Over S) :
    CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((schemeYoneda S).obj U) :=
  ((schemeSheaf S).obj U).property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S)

variable {G : GroupScheme S} {V : Over S} (a : SchemeAction G V)

/-- The projection `G × V → V` is smooth when `G` is smooth over `S`. -/
lemma smooth_snd (hG : Smooth G.X.hom) : Smooth (snd G.X V).left := by
  change Smooth (Limits.pullback.snd G.X.hom V.hom)
  infer_instance

/-- The product `G × V` is locally of finite type over `S` when `G` is smooth and `V` is
locally of finite type. -/
lemma locallyOfFiniteType_prod (hG : Smooth G.X.hom) (hV : LocallyOfFiniteType V.hom) :
    LocallyOfFiniteType (G.X ⊗ V).hom := by
  rw [← Over.w (snd G.X V)]
  have := smooth_snd (V := V) hG
  infer_instance

/-- The shear automorphism `(g, v) ↦ (g, g.v)` of `G × V`. -/
def shear : G.X ⊗ V ≅ G.X ⊗ V where
  hom := lift (fst G.X V) a.hom
  inv := lift (fst G.X V) (a.act (fst G.X V)⁻¹ (snd G.X V))
  hom_inv_id := by
    have e : a.act (fst G.X V) (snd G.X V) = a.hom := by simpa using act_fst_snd a (𝟙 _)
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, a.naturality, GrpObj.comp_inv, lift_fst,
        lift_snd, ← e, ← a.act_mul, inv_mul_cancel, a.act_one]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, ← act_fst_snd a, lift_fst, lift_snd,
        ← a.act_mul, mul_inv_cancel, a.act_one]

/-- The action map is smooth when `G` is smooth over `S`: it is the shear automorphism
followed by the smooth projection to `V`. -/
lemma smooth_act (hG : Smooth G.X.hom) : Smooth a.hom.left := by
  have h : a.hom = (shear a).hom ≫ snd G.X V := (lift_snd _ _).symm
  have : Smooth (snd G.X V).left := smooth_snd hG
  have : IsIso (shear a).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (shear a).hom))
  rw [h, Over.comp_left]
  infer_instance

/-- The arrow scheme of `a`: pairs of points of `G × V` with the same graph image. -/
abbrev arrows : Over S := Limits.pullback (graph a) (graph a)

/-- The first projection of the arrow scheme. -/
abbrev arrowsFst : arrows a ⟶ G.X ⊗ V := pullback.fst _ _

/-- The second projection of the arrow scheme. -/
abbrev arrowsSnd : arrows a ⟶ G.X ⊗ V := pullback.snd _ _

/-- The functor of points of the arrow scheme is the kernel pair of the graph. -/
lemma isPullback_arrows :
    IsPullback ((schemeYoneda S).map (arrowsFst a)) ((schemeYoneda S).map (arrowsSnd a))
      ((schemeYoneda S).map (graph a)) ((schemeYoneda S).map (graph a)) :=
  (IsPullback.of_hasPullback _ _).map (schemeYoneda S)

/-- The arrow scheme is a monomorphic equivalence relation on `G × V`. -/
lemma arrows_isEquivalenceRelation :
    IsEquivalenceRelation ((schemeToSpace S).obj (arrows a))
      ((schemeYoneda S).map (arrowsFst a)) ((schemeYoneda S).map (arrowsSnd a)) :=
  Picard.PicardGroupoid.representedKernel_isEquivalenceRelation _ _ _ (isPullback_arrows a)

/-- Both projections of the arrow scheme are smooth when the stabilizer is. -/
lemma arrows_hasSmoothProjections (hσ : Smooth (stabilizerProj a).left) :
    HasSmoothProjections ((schemeToSpace S).obj (arrows a))
      ((schemeYoneda S).map (arrowsFst a)) ((schemeYoneda S).map (arrowsSnd a)) :=
  Picard.PicardGroupoid.schemeRelation_hasSmoothProjections _ _
    (smooth_arrow_fst (IsPullback.of_hasPullback (graph a) (graph a)) hσ)
    (smooth_arrow_snd (IsPullback.of_hasPullback (graph a) (graph a)) hσ)

/-- The canonical étale quotient of `G × V` by its arrow relation. -/
abbrev arrowQuotient : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  quotientSheaf ((schemeToSpace S).obj (arrows a)) _ _ (arrows_isEquivalenceRelation a)

/-- The quotient map from `G × V` to the arrow quotient. -/
abbrev arrowQuotientMap : (schemeYoneda S).obj (G.X ⊗ V) ⟶ (arrowQuotient a).obj :=
  quotientMap ((schemeToSpace S).obj (arrows a)) _ _ (arrows_isEquivalenceRelation a)

/-- The graph descends to the arrow quotient. -/
def endpoint : (arrowQuotient a).obj ⟶ (schemeYoneda S).obj (V ⊗ V) :=
  quotientSheafDesc ((schemeToSpace S).obj (arrows a)) _ _ (arrows_isEquivalenceRelation a)
    ((schemeYoneda S).map (graph a)) (isPullback_arrows a).w
    (isSheaf_etale_representable (V ⊗ V))

/-- The descended graph recovers the graph on points of `G × V`. -/
@[simp]
lemma arrowQuotientMap_endpoint :
    arrowQuotientMap a ≫ endpoint a = (schemeYoneda S).map (graph a) :=
  quotientMap_desc _ _ _ _ _ _ _

/-- The descended graph is a monomorphism: the arrow relation is the full kernel pair of
the graph, and étale sheafification preserves monomorphisms. -/
lemma endpoint_mono : Mono (endpoint a) := by
  let c := quotientPresheafDesc ((schemeToSpace S).obj (arrows a)) _ _
    (arrows_isEquivalenceRelation a) ((schemeYoneda S).map (graph a)) (isPullback_arrows a).w
  have : Mono c := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro T
    apply (mono_iff_injective _).mpr
    intro x y hxy
    induction x using Quotient.ind with
    | _ x =>
      induction y using Quotient.ind with
      | _ y => exact Quotient.sound (Types.exists_of_isPullback ((isPullback_arrows a).app T) x y hxy)
  have : Mono (sheafifyMap (Scheme.etaleTopology.over S) c) :=
    inferInstanceAs (Mono ((sheafification (Scheme.etaleTopology.over S)
      (Type (u + 1))).map c))
  have heq : endpoint a = sheafifyMap (Scheme.etaleTopology.over S) c ≫
      (isoSheafify (Scheme.etaleTopology.over S) (isSheaf_etale_representable (V ⊗ V))).inv := by
    rw [isoSheafify_inv, sheafifyMap_sheafifyLift, Category.comp_id]
    rfl
  rw [heq]
  exact mono_comp' (inferInstanceAs (Mono (sheafifyMap (Scheme.etaleTopology.over S) c)))
    (inferInstanceAs (Mono (isoSheafify (Scheme.etaleTopology.over S)
      (isSheaf_etale_representable (V ⊗ V))).inv))

/-- The first endpoint of an arrow class: the image of `(g, v)` under the action. -/
def orbitFst : (arrowQuotient a).obj ⟶ (schemeYoneda S).obj V :=
  endpoint a ≫ (schemeYoneda S).map (fst V V)

/-- The second endpoint of an arrow class: the point `v` of `(g, v)`. -/
def orbitSnd : (arrowQuotient a).obj ⟶ (schemeYoneda S).obj V :=
  endpoint a ≫ (schemeYoneda S).map (snd V V)

/-- The first endpoint recovers the action map. -/
@[simp]
lemma arrowQuotientMap_orbitFst :
    arrowQuotientMap a ≫ orbitFst a = (schemeYoneda S).map a.hom := by
  rw [orbitFst, ← Category.assoc, arrowQuotientMap_endpoint, ← Functor.map_comp, lift_fst]

/-- The second endpoint recovers the projection to `V`. -/
@[simp]
lemma arrowQuotientMap_orbitSnd :
    arrowQuotientMap a ≫ orbitSnd a = (schemeYoneda S).map (snd G.X V) := by
  rw [orbitSnd, ← Category.assoc, arrowQuotientMap_endpoint, ← Functor.map_comp, lift_snd]

/-- The two endpoints determine every section of the arrow quotient. -/
lemma orbit_jointlyInjective (T : Over S) :
    Function.Injective (fun q : (arrowQuotient a).obj.obj (op T) ↦
      ((orbitFst a).app (op T) q, (orbitSnd a).app (op T) q)) := by
  have : Mono (endpoint a) := endpoint_mono a
  have hinj := (mono_iff_injective ((endpoint a).app (op T))).mp inferInstance
  intro q q' hqq'
  apply hinj
  apply ULift.ext
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg ULift.down (congrArg Prod.fst hqq')
  · exact congrArg ULift.down (congrArg Prod.snd hqq')

variable (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) (arrowQuotient a).obj)
  (hD : HasRepresentableDiagonal (arrowQuotient a).obj)
  (hAtlas : ∃ (W : Over S) (b : (schemeYoneda S).obj W ⟶ (arrowQuotient a).obj),
    IsEtale b ∧ IsSurjective b)

/-- The arrow quotient as an algebraic space, under its geometric hypotheses. -/
def arrowQuotientSpace : AlgebraicSpace S :=
  ⟨⟨(arrowQuotient a).obj, hF⟩, hD, hAtlas⟩

/-- Both endpoints of the arrow quotient are smooth, witnessed on an étale atlas: the
quotient map from `G × V` is a smooth surjective cover along which the endpoints become the
smooth action map and the smooth projection. -/
lemma orbit_hasSmoothProjections (hG : Smooth G.X.hom) (hq : IsSmooth (arrowQuotientMap a))
    (hqSurj : IsSurjective (arrowQuotientMap a)) :
    HasSmoothProjections (arrowQuotientSpace a hF hD hAtlas) (orbitFst a) (orbitSnd a) :=
  (smoothProjectionAtlasOfSmoothCover
    (fun P W Z p g hp hs hpg ↦ @smooth_of_smooth_of_surjective_of_smooth_comp P W Z p g hp hs hpg)
    (arrowQuotientSpace a hF hD hAtlas) (orbitFst a) (orbitSnd a) (arrowQuotientMap a) hq hqSurj
    a.hom (snd G.X V) (arrowQuotientMap_orbitFst a) (arrowQuotientMap_orbitSnd a)
    (smooth_act a hG) (smooth_snd hG)).hasSmoothProjections

/-- The first quotient: when `G` is smooth, `V` is locally of finite type and the stabilizer
is smooth, the arrow quotient of `G × V` is an algebraic space with jointly injective
endpoints to `V` having smooth projections, and the quotient map from `G × V` is étale
locally surjective with endpoints the action map and the projection. -/
theorem exists_orbitRelationSpace (hG : Smooth G.X.hom) (hV : LocallyOfFiniteType V.hom)
    (hσ : Smooth (stabilizerProj a).left) :
    ∃ (B : AlgebraicSpace S) (s' t' : B.presheaf ⟶ (schemeYoneda S).obj V)
      (q : (schemeYoneda S).obj (G.X ⊗ V) ⟶ B.presheaf),
      q ≫ s' = (schemeYoneda S).map a.hom ∧ q ≫ t' = (schemeYoneda S).map (snd G.X V) ∧
      CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q ∧
      (∀ T : Over S, Function.Injective
        (fun r : B.sections T ↦ (s'.app (op T) r, t'.app (op T) r))) ∧
      HasSmoothProjections B s' t' := by
  obtain ⟨hF, hD, -, hq, hqSurj, W, c, hc, hcSurj, -⟩ :=
    smoothRelationQuotient S (G.X ⊗ V) ((schemeToSpace S).obj (arrows a)) _ _
      (arrows_isEquivalenceRelation a) (arrows_hasSmoothProjections a hσ)
      (locallyOfFiniteType_prod hG hV)
  have hAtlas : ∃ (W : Over S) (b : (schemeYoneda S).obj W ⟶ (arrowQuotient a).obj),
      IsEtale b ∧ IsSurjective b := ⟨W, c, hc, hcSurj⟩
  exact ⟨arrowQuotientSpace a hF hD hAtlas, orbitFst a, orbitSnd a, arrowQuotientMap a,
    arrowQuotientMap_orbitFst a, arrowQuotientMap_orbitSnd a,
    isLocallySurjective_quotientMap _ _ _ _, orbit_jointlyInjective a,
    orbit_hasSmoothProjections a hF hD hAtlas hG hq hqSurj⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotient
