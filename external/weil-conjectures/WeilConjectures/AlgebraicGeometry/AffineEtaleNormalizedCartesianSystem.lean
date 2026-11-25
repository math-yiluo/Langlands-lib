/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.AffineEtaleNormalizedCartesianComparisons

/-!
# Normalized cartesian affine étale pullback systems

Source: Stacks Project, Étale Cohomology 0EYL, including its coherence discussion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def normalizedPullback {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f] :
    S.FullAffineEtale ⥤ T.FullAffineEtale :=
  ObjectProperty.lift (fun A : T.Etale ↦ IsAffine A.left)
    (fullAffineEtaleInclusion S ⋙ MorphismProperty.Over.pullback @Etale ⊤ f)
    (fun A ↦ by
      have : IsAffine ((𝟭 Scheme).obj A.obj.left) := A.property
      change IsAffine (pullback A.obj.hom f)
      exact AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1 _ _)

private noncomputable def normalizedFirst {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f] :
    normalizedPullback f ⋙ fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S where
  app A := pullback.fst A.obj.hom f
  naturality A B a := by
    change pullback.lift (pullback.fst A.obj.hom f ≫ a.hom.left)
      (pullback.snd A.obj.hom f) _ ≫ pullback.fst B.obj.hom f = _
    exact pullback.lift_fst _ _ _

private theorem normalizedSquare {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f]
    (A : S.FullAffineEtale) :
    IsPullback ((normalizedFirst f).app A) ((normalizedPullback f).obj A).obj.hom A.obj.hom f :=
  IsPullback.of_hasPullback _ _

private theorem normalizedPair {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i j : I) (h : i ≤ j) :
    ∃ (U : (D.obj (op i)).FullAffineEtale ⥤ (D.obj (op j)).FullAffineEtale)
      (p : U ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙ Etale.forget (D.obj (op j)) ⋙
          Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙ Etale.forget (D.obj (op i)) ⋙
          Over.forget (D.obj (op i))),
      (∀ _ : i = j, HEq U (𝟭 (D.obj (op i)).FullAffineEtale)) ∧
      (∀ (_ : i = j) (A : (D.obj (op i)).FullAffineEtale),
        HEq (p.app A) (𝟙 A.obj.left)) ∧
      ∀ A : (D.obj (op i)).FullAffineEtale,
        IsPullback (p.app A) (U.obj A).obj.hom A.obj.hom (D.map (homOfLE h).op) := by
  classical
  by_cases e : i = j
  · subst j
    let G := fullAffineEtaleInclusion (D.obj (op i)) ⋙ Etale.forget (D.obj (op i)) ⋙
      Over.forget (D.obj (op i))
    refine ⟨𝟭 _, G.leftUnitor.hom, fun _ ↦ HEq.rfl, fun _ _ ↦ HEq.rfl, ?_⟩
    intro A
    have he : (homOfLE h).op = 𝟙 (op i) := Subsingleton.elim _ _
    change IsPullback (𝟙 A.obj.left) A.obj.hom A.obj.hom (D.map (homOfLE h).op)
    rw [he, D.map_id]
    exact IsPullback.id_horiz A.obj.hom
  · refine ⟨normalizedPullback (D.map (homOfLE h).op), normalizedFirst (D.map (homOfLE h).op),
      fun h ↦ (e h).elim, fun h _ ↦ (e h).elim, ?_⟩
    exact normalizedSquare (D.map (homOfLE h).op)

/-- Source: Stacks Project, Étale Cohomology 0EYL, base-change functors and their
canonical comparison isomorphisms (including the discussion following its proof).

Proof: For i ≠ j, restrict pullback along D.map (homOfLE h).op to affine étale objects.
The first projection is affine, since it is a base change of an affine morphism; its
source is affine because its target is affine. Its other projection is étale by base
change. For i = j choose the identity functor and identity first projection instead;
D maps the unique endomorphism to the identity, so that square is cartesian. The
projection is the underlying functor left unitor, whose components are identities. Pullback
along each c.π.app (op i), restricted in the same way, gives v and q. The ordinary
pullback map supplies the functor laws and naturality of the first projections.

For a chain i ≤ j ≤ k, paste the two cartesian squares. Functoriality of D identifies
its composite base arrow with D.map (homOfLE (h.trans h')).op. The pasted pullback
and the single pullback have a unique isomorphism preserving the first and structure
projections. These component isomorphisms form gamma: naturality follows because both
sides have equal projections. The same construction using cone naturality gives delta.
If either adjacent pair of indices is equal, take the identity comparison; its source
and target identify through the diagonal identity choice. This gives the three HEq
normalization clauses. The first-projection equations are the defining equations of
the comparisons. No associativity or cone cocycle, covering, or continuity property is
concluded; these follow from the displayed first-projection equations by pullback
uniqueness and base change of coverings, respectively.
(blueprint: lem-weil-pbc-affine-etale-normalized-cartesian-system). -/
theorem exists_affineEtale_normalized_cartesian_system
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) [∀ i : Iᵒᵖ, IsAffineHom (c.π.app i)] :
    ∃ (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i),
      (∀ i : I, U i i le_rfl = 𝟭 _)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
      ∧ (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((gamma i j k h h').hom.app A).hom.left ≫ (p i k (h.trans h')).app A =
          (p j k h').app ((U i j h).obj A) ≫ (p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A) := by
  classical
  choose U p hUid hpid hp using normalizedPair D
  let v (i : I) := normalizedPullback (c.π.app (op i))
  let q (i : I) := normalizedFirst (c.π.app (op i))
  have hid (i : I) : U i i le_rfl = 𝟭 _ := eq_of_heq (hUid i i le_rfl rfl)
  have hpd (i : I) (A : (D.obj (op i)).FullAffineEtale) :
      HEq ((p i i le_rfl).app A) (𝟙 A.obj.left) := hpid i i le_rfl rfl A
  have hq (i : I) (A : (D.obj (op i)).FullAffineEtale) :
      IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i)) :=
    normalizedSquare (c.π.app (op i)) A
  obtain ⟨gamma, delta, hγl, hγr, hδ, hγp, hδp⟩ :=
    exists_affineEtale_normalized_cartesian_comparisons D c U v p q hid hpd hp hq
  exact ⟨U, v, p, q, gamma, delta, hid, hp, hq, hγl, hγr, hδ, hγp, hδp⟩

end AlgebraicGeometry.Scheme
