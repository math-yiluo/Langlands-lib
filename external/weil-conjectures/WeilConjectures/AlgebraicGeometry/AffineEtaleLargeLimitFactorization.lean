/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality

/-! # Factorization of maps from larger affine étale limits

Source: Stacks Project, Tags 01ZC and 099S.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Every map from the affine étale inverse limit to an affine étale object
factors through one stage, even for the larger index universe.

Source: Stacks Project, limits.tex, Proposition 32.6.1 (Tag 01ZC), surjectivity
in (1) implies (3), and proetale.tex, lemma-limit-pullback (Tag 099S).
(auxiliary; not a blueprint node).

Proof: Work over X and cover the source by finitely many affine opens mapping into
an affine chart of X and an affine chart of V. The affine finite-presentation
calculation lifts the finitely many generators of the target algebra to a common
stage and kills its finitely many defining relations after refinement. The
quasi-compact affine source permits finitely many such charts. Refine once more
so that they cover a stage, then descend the finitely many overlap equations by
the locally finite-type equality argument of Tag 01ZC. Glue the resulting local
maps to a stage map over X. All choices of generators, relations, covering charts
and overlap equations are finite, so the same construction works for I in u+1.
The resulting scheme map is a morphism of the full pro-étale subcategory of
schemes over X. For an empty limit, the same quasi-compact covering argument
produces an empty stage and hence its unique map to V. -/
theorem affineEtale_largeLimit_factorization {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ X.ProEt) (haff : ∀ i, IsAffine (D.obj i).left)
    (het : ∀ i, Etale (D.obj i).hom) (c : Cone D)
    (hc : IsLimit ((Scheme.ProEt.forget X).mapCone c))
    (V : X.ProEt) [IsAffine V.left] [Etale V.hom]
    (a : c.pt ⟶ V) :
    ∃ (i : I) (b : D.obj i ⟶ V), c.π.app i ≫ b = a := by
  classical
  let F := Scheme.AffineEtale.Spec X ⋙ Scheme.toProEt X
  have hD (i : I) : F.essImage (D.obj i) := by
    have : IsAffine (D.obj i).left := haff i
    have : Etale (D.obj i).hom := het i
    let T : X.AffineEtale := .mk ((D.obj i).left.isoSpec.inv ≫ (D.obj i).hom)
    refine ⟨T, ⟨?_⟩⟩
    exact MorphismProperty.Over.isoMk (D.obj i).left.isoSpec.symm (by rfl)
  -- Affine étale objects admit a model in the scheme universe.
  let A := F.EssImageSubcategory
  have : EssentiallySmall.{u} A :=
    (essentiallySmall_congr F.toEssImage.asEquivalence).mp inferInstance
  let L : I ⥤ A := F.essImage.lift D hD
  let G := L.toStructuredArrow c.pt F.essImage.ι (fun i ↦ c.π.app i)
    (fun f ↦ c.w f)
  -- Retain the actual projected stages, with all maps commuting with the projection.
  let P : ObjectProperty (StructuredArrow c.pt F.essImage.ι) :=
    fun T ↦ ∃ i, G.obj i = T
  let E := P.FullSubcategory
  let H : I ⥤ E := P.lift G (fun i ↦ ⟨i, rfl⟩)
  let K : E ⥤ X.ProEt := P.ι ⋙ StructuredArrow.proj _ _ ⋙ F.essImage.ι
  have : EssentiallySmall.{u} E := essentiallySmall_of_fully_faithful P.ι
  have : IsCofiltered E :=
    { nonempty := ⟨H.obj (Classical.choice (IsCofiltered.nonempty : Nonempty I))⟩
      cone_objs := by
        rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
        exact ⟨H.obj (IsCofiltered.min i j), H.map (IsCofiltered.minToLeft i j),
          H.map (IsCofiltered.minToRight i j), trivial⟩
      -- The extra parallel arrows can be equalized using eventual equality.
      cone_maps := by
        rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ f g
        have hab : c.π.app i ≫ K.map f = c.π.app i ≫ K.map g := by
          exact f.hom.w.trans g.hom.w.symm
        have : IsAffine (D.obj j).left := haff j
        have : Etale (D.obj j).hom := het j
        obtain ⟨k, h, heq⟩ := affineEtale_largeLimit_eventualEquality
          D haff het c hc (D.obj j) i (K.map f) (K.map g) hab
        refine ⟨H.obj k, H.map h, ?_⟩
        apply K.map_injective
        change D.map h ≫ K.map f = D.map h ≫ K.map g
        exact heq }
  -- The larger full diagram has the same limit: restriction recovers the given cone.
  let d : Cone K :=
    { pt := c.pt
      π :=
        { app T := T.obj.hom
          naturality _ _ f := by
            simpa [K] using f.hom.w.symm } }
  let U := Scheme.ProEt.forget X
  have hd : IsLimit (U.mapCone d) :=
    { lift s := hc.lift (s.whisker H)
      fac s T := by
        obtain ⟨i, hi⟩ := T.property
        obtain rfl : H.obj i = T := ObjectProperty.FullSubcategory.ext hi
        exact hc.fac (s.whisker H) i
      uniq s m hm := by
        apply hc.uniq (s.whisker H) m
        intro i
        exact hm (H.obj i) }
  -- Shrink the new index and apply the existing finite-presentation theorem.
  let e := equivSmallModel.{u} E
  have : IsCofiltered (SmallModel.{u} E) := IsCofiltered.of_equivalence e
  let D' := e.inverse ⋙ K
  let d' : Cone D' := d.whisker e.inverse
  have hd' : IsLimit (U.mapCone d') :=
    (Functor.Initial.isLimitWhiskerEquiv e.inverse (U.mapCone d)).symm hd
  let Q := U ⋙ Over.forget X
  have hd'' : IsLimit (Q.mapCone d') := isLimitOfPreserves (Over.forget X) hd'
  have hstage (T : E) : IsAffine (K.obj T).left ∧ Etale (K.obj T).hom := by
    obtain ⟨i, hi⟩ := T.property
    obtain rfl : H.obj i = T := ObjectProperty.FullSubcategory.ext hi
    exact ⟨haff i, het i⟩
  have (j : SmallModel.{u} E) : IsAffine ((D' ⋙ Q).obj j) :=
    (hstage (e.inverse.obj j)).1
  have {i j : SmallModel.{u} E} (f : i ⟶ j) :
      IsAffineHom ((D' ⋙ Q).map f) := inferInstance
  let t : D' ⋙ Q ⟶ (Functor.const _).obj X :=
    { app j := (D'.obj j).hom
      naturality _ _ f := by
        change (D'.map f).left ≫ _ = _
        exact (D'.map f).w }
  obtain ⟨j, b, hb, hbX⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (D' ⋙ Q) t V.hom (Q.mapCone d') hd'' a.left (by
      ext j
      change (d'.π.app j).left ≫ (D'.obj j).hom = a.left ≫ V.hom
      exact (d'.π.app j).w.trans a.w.symm)
  let b' : D'.obj j ⟶ V := MorphismProperty.Over.homMk b hbX
  obtain ⟨i, hi⟩ := (e.inverse.obj j).property
  have he : H.obj i = e.inverse.obj j := ObjectProperty.FullSubcategory.ext hi
  refine ⟨i, eqToHom (congrArg K.obj he) ≫ b', ?_⟩
  have hb' : d'.π.app j ≫ b' = a := by
    apply MorphismProperty.Over.Hom.ext
    exact hb
  rw [← hb']
  dsimp [d', d]
  have hπ := d.w (eqToHom he)
  change c.π.app i ≫ K.map (eqToHom he) = (e.inverse.obj j).obj.hom at hπ
  rw [eqToHom_map] at hπ
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ b') hπ

end AlgebraicGeometry.ProEtale
