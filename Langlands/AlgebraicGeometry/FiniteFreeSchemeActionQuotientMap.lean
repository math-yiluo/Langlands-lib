import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotient

/-! # Equivariant maps and affine quotients of finite free actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry

/-- A square is cartesian if its pullback to an fpqc source cover is cartesian,
expressed using the cover's kernel pair. -/
theorem isPullback_of_fpqc_kernelPair
    {X Y B C K : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ C) (b : B ⟶ C)
    [Surjective p] [Flat p] [QuasiCompact p] {k₁ k₂ : K ⟶ X}
    (w : f ≫ q = p ≫ b) (hk : IsPullback k₁ k₂ p p)
    (ho : IsPullback (k₁ ≫ f) k₂ q (p ≫ b)) : IsPullback f p q b := by
  let d : X ⟶ pullback q b := pullback.lift f p w
  have hd₁ : d ≫ pullback.fst q b = f := by simp [d]
  have hd₂ : d ≫ pullback.snd q b = p := by simp [d]
  have ho' : IsPullback ((k₁ ≫ d) ≫ pullback.fst q b) k₂ q (p ≫ b) := by
    simpa only [Category.assoc, hd₁] using ho
  have hs : IsPullback (k₁ ≫ d) k₂ (pullback.snd q b) p := by
    apply ho'.of_right _ (IsPullback.of_hasPullback q b)
    simpa only [Category.assoc, hd₂] using hk.w
  let e := hs.isoPullback
  have he₁ : e.hom ≫ pullback.fst (pullback.snd q b) p = k₁ ≫ d :=
    hs.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd (pullback.snd q b) p = k₂ :=
    hs.isoPullback_hom_snd
  have hh : IsPullback k₁ e.hom d (pullback.fst (pullback.snd q b) p) := by
    apply IsPullback.of_bot (s := ?_) he₁.symm
      (IsPullback.of_hasPullback (pullback.snd q b) p)
    simpa only [he₂, hd₂] using hk
  have : IsIso d := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hh.flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso d) hd₁ hd₂

namespace FiniteFreeSchemeAction

variable {G : Type u} [Group G] [Finite G] {X Y : Scheme.{u}}
  (A : FiniteFreeSchemeAction G X) (B : FiniteFreeSchemeAction G Y)
  (f : X ⟶ Y) (hf : ∀ g : G, (A.act g).hom ≫ f = f ≫ (B.act g).hom)

/-- The induced map between the two action relations. -/
def equivariantRelationMap : A.relationScheme ⟶ B.relationScheme :=
  Limits.Sigma.map fun _ => f

omit [Finite G] in
@[reassoc (attr := simp)]
theorem equivariantRelationMap_source :
    A.equivariantRelationMap B f ≫ B.source = A.source ≫ f := by
  apply Sigma.hom_ext
  intro g
  simp [equivariantRelationMap]

omit [Finite G] in
include hf in
@[reassoc (attr := simp)]
theorem equivariantRelationMap_target :
    A.equivariantRelationMap B f ≫ B.target = A.target ≫ f := by
  apply Sigma.hom_ext
  intro g
  simpa [equivariantRelationMap] using (hf g).symm

include hf in
/-- An equivariant map induces a cartesian square on the first endpoints of the
action relations. -/
theorem equivariantRelationMap_isPullback_target :
    IsPullback (A.equivariantRelationMap B f) A.target B.target f := by
  have h := IsUniversalColimit.isPullback_of_isColimit_left
    (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G => Y)))
    (fun g => (B.act g).hom) B.target f (fun g => (A.act g).hom)
    (fun _ => f) (fun g => IsPullback.of_horiz_isIso ⟨hf g⟩)
    (coproductIsCoproduct (fun _ : G => X)) (by intro g; simp)
  have ht : Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G => X))
      (fun g => (A.act g).hom) = A.target := by
    apply Sigma.hom_ext
    intro g
    simp only [target, Sigma.ι_comp_desc]
    exact Cofan.IsColimit.fac (coproductIsCoproduct (fun _ : G => X)) _ g
  have hm : Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G => X))
      (fun g => f ≫ Sigma.ι (fun _ : G => Y) g) =
      A.equivariantRelationMap B f := by
    apply Sigma.hom_ext
    intro g
    simp only [equivariantRelationMap, Limits.Sigma.ι_map]
    exact Cofan.IsColimit.fac (coproductIsCoproduct (fun _ : G => X)) _ g
  change IsPullback
    (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G => X))
      (fun g => (A.act g).hom))
    (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G => X))
      (fun g => f ≫ Sigma.ι (fun _ : G => Y) g)) f B.target at h
  simpa only [ht, hm] using h.flip

section Affine

variable [IsAffine X] [IsAffine Y] (Q : A.AffineQuotient) (Q' : B.AffineQuotient)

/-- The map on affine quotients induced by an equivariant map. -/
def quotientMap : Q.scheme ⟶ Q'.scheme :=
  Q.desc (f ≫ Q'.map) (by intro g; rw [← Category.assoc, hf]; simp)

omit [Finite G] [IsAffine X] [IsAffine Y] in
@[reassoc (attr := simp)]
theorem map_quotientMap :
    Q.map ≫ A.quotientMap B f hf Q Q' = f ≫ Q'.map :=
  Q.map_desc _ _

omit [IsAffine X] [IsAffine Y] in
/-- An equivariant map of free actions of the same finite group is cartesian
over the induced map on quotients. -/
theorem quotientMap_isPullback :
    IsPullback f Q.map Q'.map (A.quotientMap B f hf Q Q') := by
  apply isPullback_of_fpqc_kernelPair f Q.map Q'.map _
    (A.map_quotientMap B f hf Q Q').symm Q.isPullback.flip
  have h := (A.equivariantRelationMap_isPullback_target B f hf).paste_horiz
    Q'.isPullback.flip
  simpa only [A.equivariantRelationMap_source B f, A.map_quotientMap B f hf Q Q'] using h

end Affine

end FiniteFreeSchemeAction
end Langlands.AlgebraicGeometry
