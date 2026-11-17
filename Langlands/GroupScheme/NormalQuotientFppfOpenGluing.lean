import Langlands.GroupScheme.NormalQuotientOpenGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleRelationQuotient

/-! # Open gluing of fppf quotients with arbitrary represented kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace HomogeneousCosetRelation

variable {S : Scheme.{u}} {G N : GroupScheme S} (i : N ⟶ G)

/-- The fppf sheafification of the represented right-coset relation. -/
def fppfQuotientSheaf : FppfSheaf S :=
  RelationQuotient.quotientSheaf (source i) (target i)

/-- The represented coset relation is an equivalence relation without a
smoothness assumption on the subgroup. -/
theorem isOverEquivRel [Mono i.hom.hom] :
    RelationQuotient.IsOverEquivRel (source i) (target i) where
  ext := by
    intro T a b hs ht
    exact arrow_unique i hs ht
  refl := by
    intro T x
    exact (exists_arrow_iff i x x).mpr (by simp)
  symm := by
    intro T a
    apply (exists_arrow_iff i _ _).mpr
    have ha := (exists_arrow_iff i _ _).mp ⟨a, rfl, rfl⟩
    simpa using ((SubgroupFunctor.range i).carrier _).inv_mem ha
  trans := by
    intro T a b hab
    apply (exists_arrow_iff i _ _).mpr
    have ha := (exists_arrow_iff i _ _).mp ⟨a, rfl, rfl⟩
    have hb := (exists_arrow_iff i _ _).mp ⟨b, rfl, rfl⟩
    rw [← hab] at hb
    simpa [mul_assoc] using ((SubgroupFunctor.range i).carrier _).mul_mem ha hb

end HomogeneousCosetRelation

namespace NormalQuotient

variable {S S' : Scheme.{u}}

/-- Pullback of an arrow in a slice is the pullback of its underlying arrow
along the projection of its target. -/
theorem overPullback_map_isPullback (b : S' ⟶ S) {W V : Over S} (r : W ⟶ V) :
    IsPullback ((Over.pullback b).map r).left (pullback.fst W.hom b)
      (pullback.fst V.hom b) r.left := by
  have houter : IsPullback
      (((Over.pullback b).map r).left ≫ pullback.snd V.hom b)
      (pullback.fst W.hom b) b (r.left ≫ V.hom) := by
    simpa only [Over.w r, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback W.hom b).flip
  exact houter.of_right
    (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback V.hom b).flip

/-- A target-local property of a relative morphism can be checked over an
open cover of the base. -/
theorem property_of_base_openCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {W V : Over S} (r : W ⟶ V) (𝒰 : Scheme.OpenCover.{u} S)
    (hr : ∀ j, P ((Over.pullback (𝒰.f j)).map r).left) : P r.left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (𝒰.pullback₁ V.hom)
  change ∀ j : 𝒰.I₀, P (pullback.snd r.left (pullback.fst V.hom (𝒰.f j)))
  intro j
  let h := overPullback_map_isPullback (𝒰.f j) r
  rw [← h.flip.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P _ _ (hr j)

/-- Restricting a presentation commutes with precomposition by a morphism of
representing schemes. -/
theorem restrictedPresentation_naturality (b : S' ⟶ S)
    {W V : Over S} {F : Presheaf S} (r : W ⟶ V)
    (a : (schemeYoneda S).obj V ⟶ F) :
    (schemeYoneda S').map ((Over.pullback b).map r) ≫
        restrictedPresentation b a =
      restrictedPresentation b ((schemeYoneda S).map r ≫ a) := by
  ext T x
  exact congrArg (fun z => a.app _ (ULift.up z))
    ((Over.mapPullbackAdj b).homEquiv_naturality_right_symm x.down r)

/-- The canonical local representative comparison respects its representing
isomorphism. -/
theorem localRepresentativeIso_fac (b : S' ⟶ S)
    {F : Presheaf S} (V : Over S) (eV : (schemeYoneda S).obj V ≅ F)
    (H : Over S') (eH : (schemeYoneda S').obj H ≅ (Over.map b).op ⋙ F) :
    (schemeYoneda S').map
        (LocalRepresentation.localRepresentativeIso b V eV H eH).hom ≫ eH.hom =
      restrictedPresentation b eV.hom := by
  change (schemeYoneda S').map
    ((ULiftYoneda.fullyFaithful (Over S')).preimageIso
      (representedBaseChangeIso b V eV ≪≫ eH.symm)).hom ≫ eH.hom = _
  rw [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, eH.inv_hom_id,
    Category.comp_id]
  rfl

/-- Affine fppf quotients over an open cover glue with their complete kernel;
the represented normal subgroup need not be smooth or reduced. -/
theorem exists_affine_fppfQuotient_of_openCover_arbitrary_kernel
    {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.OpenCover.{u} S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M),
      IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  let s := HomogeneousCosetRelation.source i
  let t := HomogeneousCosetRelation.target i
  let F : FppfSheaf S := HomogeneousCosetRelation.fppfQuotientSheaf i
  let a : (schemeYoneda S).obj G.X ⟶ F.obj := RelationQuotient.quotientMap s t
  have ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a :=
    inferInstanceAs (CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (RelationQuotient.quotientMap s t))
  have hfib : ∀ (T : Over S) (x y : T ⟶ G.X),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T := by
    intro T x y
    rw [← HomogeneousCosetRelation.exists_arrow_iff]
    constructor
    · exact RelationQuotient.exists_of_quotientMap_eq
        (HomogeneousCosetRelation.isOverEquivRel i) x y
    · rintro ⟨b, rfl, rfl⟩
      exact congrArg (fun f => f.app (op T) ⟨b⟩)
        (RelationQuotient.quotientMap_w s t)
  have hlocal : ∀ j,
      ∃ e : (schemeYoneda (𝒰.X j)).obj (Q j).X ≅ (Over.map (𝒰.f j)).op ⋙ F.obj,
        (schemeYoneda (𝒰.X j)).map (q j).hom.hom ≫ e.hom =
          restrictedPresentation (𝒰.f j) a := by
    intro j
    let := (hq j).1
    let := (hq j).2.1
    let := (hq j).2.2.1
    apply exists_restriction_iso (𝒰.f j) a ha (q j).hom.hom
    intro T x y
    change a.app (op ((Over.map (𝒰.f j)).obj T))
        ⟨baseChangePointsEquiv (𝒰.f j) G T x⟩ =
      a.app (op ((Over.map (𝒰.f j)).obj T))
        ⟨baseChangePointsEquiv (𝒰.f j) G T y⟩ ↔ _
    rw [hfib, (hq j).fibers T x y, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.mem_baseChange, map_mul, map_inv]
  choose e he using hlocal
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation F.property
    𝒰 (fun j => (Q j).X) e
  have hAffine : IsAffineHom V.hom :=
    LocalRepresentation.property_of_local_representations (@IsAffineHom)
      V eV 𝒰 (fun j => (Q j).X) e hQ
  let := hAffine
  let r : G.X ⟶ V := (schemeYoneda S).preimage (a ≫ eV.inv)
  have hr : (schemeYoneda S).map r ≫ eV.hom = a := by
    dsimp [r]
    rw [Functor.map_preimage, Category.assoc, eV.inv_hom_id, Category.comp_id]
  let d := fun j => LocalRepresentation.localRepresentativeIso
    (𝒰.f j) V eV (Q j).X (e j)
  have hd : ∀ j, (Over.pullback (𝒰.f j)).map r ≫ (d j).hom = (q j).hom.hom := by
    intro j
    apply (schemeYoneda (𝒰.X j)).map_injective
    apply (cancel_mono (e j).hom).mp
    rw [Functor.map_comp, Category.assoc, localRepresentativeIso_fac,
      restrictedPresentation_naturality, hr, he]
  have hp : ∀ (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P],
      (∀ j, P (q j).hom.hom.left) → P r.left := by
    intro P _ hP
    apply property_of_base_openCover P r 𝒰
    intro j
    have he' := congrArg (fun f => f.left) (hd j)
    change ((Over.pullback (𝒰.f j)).map r).left ≫ (d j).hom.left =
      (q j).hom.hom.left at he'
    have : IsIso (d j).hom.left := (Over.forget _).map_isIso (d j).hom
    apply (MorphismProperty.cancel_right_of_respectsIso P _ (d j).hom.left).mp
    rw [he']
    exact hP j
  let : Flat r.left := hp (@Flat) (fun j => (hq j).1)
  let : Surjective r.left := hp (@Surjective) (fun j => (hq j).2.1)
  let : LocallyOfFinitePresentation r.left :=
    hp (@LocallyOfFinitePresentation) (fun j => (hq j).2.2.1)
  have hqc : QuasiCompact r.left := by
    have : QuasiCompact (r.left ≫ V.hom) := by
      rw [Over.w r]
      infer_instance
    exact QuasiCompact.of_comp r.left V.hom
  let := hqc
  have hrfib : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ r = y ≫ r ↔ x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T := by
    intro T x y
    rw [← hfib]
    have hrx := congrArg (fun f => f.app (op T) ⟨x⟩) hr
    have hry := congrArg (fun f => f.app (op T) ⟨y⟩) hr
    rw [← hrx, ← hry]
    change x ≫ r = y ≫ r ↔
      eV.hom.app (op T) ⟨x ≫ r⟩ = eV.hom.app (op T) ⟨y ≫ r⟩
    constructor
    · intro hxy
      rw [hxy]
    · intro hxy
      exact congrArg ULift.down ((eV.app (op T)).toEquiv.injective hxy)
  exact ⟨groupScheme G (SubgroupFunctor.range i) hn r hrfib,
    hom G (SubgroupFunctor.range i) hn r hrfib,
    hAffine, isFppfQuotient G (SubgroupFunctor.range i) hn r hrfib⟩

end NormalQuotient
end Langlands.GroupScheme
