import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Small diagrams of pointed affine étale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace PointedAffineEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (g : Spec (CommRingCat.of Ω) ⟶ S)

private abbrev geometricFiber := Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk g))

private abbrev affineFiber := Scheme.AffineEtale.Spec S ⋙ geometricFiber g

private abbrev Pointed := (affineFiber g).Elements

set_option backward.isDefEq.respectTransparency.types false in
private instance pointedCofiltered [IsSepClosed Ω] : IsCofiltered (Pointed g) := by
  let F := Scheme.AffineEtale.Spec S
  let G := geometricFiber g
  let I := Functor.Elements.precomp F G
  have : I.Full := {
    map_surjective {X Y} f := by
      obtain ⟨r, hr⟩ := F.map_surjective f.hom
      refine ⟨Functor.Elements.homMk r ?_, ?_⟩
      · change G.map (F.map r) X.val = Y.val
        rw [hr]
        exact f.map_val
      · exact Functor.Elements.hom_ext hr }
  have : I.Faithful := {
    map_injective {_ _} f h e :=
      Functor.Elements.hom_ext (F.map_injective (congrArg Functor.Elements.Hom.hom e)) }
  apply IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful I
  intro x
  induction x with | @mk X x
  obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
  dsimp [G, geometricFiber] at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ X.left)
      (_ : IsOpenImmersion j) (y' : Spec (CommRingCat.of Ω) ⟶ Spec R), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := y default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  have : Etale X.hom := X.prop
  have hy' : y' ≫ (j ≫ X.hom) = g := by simpa only [Category.assoc] using hy
  exact ⟨Functor.elementsMk (F ⋙ G) (Scheme.AffineEtale.mk (j ≫ X.hom))
      (Over.homMk y' hy'),
    ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk j rfl (by simp)) (by
      apply Over.OverMorphism.ext
      rfl)⟩⟩

private abbrev stageRing (i : Pointed g) : CommRingCat.{u} := i.obj.left.unop

private def stageRings : Pointed g ⥤ CommRingCat.{u}ᵒᵖ where
  obj i := i.obj.left
  map f := f.hom.left

/-- A small model of the category of all affine étale neighbourhoods pointed by `g`. -/
abbrev Index := SmallModel.{u} (Pointed g)

private abbrev smallEquiv := (equivSmallModel.{u} (Pointed g)).symm

instance [IsSepClosed Ω] : IsCofiltered (Index g) :=
  IsCofiltered.of_equivalence (smallEquiv g).symm

private abbrev coordinateRings : Index g ⥤ CommRingCat.{u}ᵒᵖ :=
  (smallEquiv g).functor ⋙ stageRings g

/-- The coordinate rings, viewed as a covariant diagram on the opposite index. -/
abbrev rings : (Index g)ᵒᵖ ⥤ CommRingCat.{u} := (coordinateRings g).leftOp

private abbrev mkStage {A : CommRingCat.{u}} (f : Spec A ⟶ S) [Etale f]
    (φ : A ⟶ CommRingCat.of Ω) (h : Spec.map φ ≫ f = g) : Pointed g :=
  Functor.elementsMk (affineFiber g) (Scheme.AffineEtale.mk f) (Over.homMk _ h)

private def stagePoint (i : Pointed g) : stageRing g i ⟶ CommRingCat.of Ω :=
  Spec.preimage i.val.left

set_option backward.isDefEq.respectTransparency false in
private lemma stagePoint_naturality {i j : Pointed g} (f : i ⟶ j) :
    f.hom.left.unop ≫ stagePoint g i = stagePoint g j := by
  have h := congrArg CategoryTheory.Over.Hom.left f.map_val
  change i.val.left ≫ Spec.map f.hom.left.unop = j.val.left at h
  change f.hom.left.unop ≫ Spec.preimage i.val.left = Spec.preimage j.val.left
  simpa only [Spec.preimage_comp, Spec.preimage_map] using congrArg Spec.preimage h

/-- The chosen geometric points, expressed as compatible maps of coordinate rings. -/
def point : rings g ⟶ (Functor.const (Index g)ᵒᵖ).obj (CommRingCat.of Ω) where
  app i := stagePoint g ((smallEquiv g).functor.obj i.unop)
  naturality i j f := by
    exact (stagePoint_naturality g ((smallEquiv g).functor.map f.unop)).trans
      (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A pointed étale extension of a stage is realized by a refinement in the small model. -/
theorem refinement (i : (Index g)ᵒᵖ) (B : CommRingCat.{u}) (f : (rings g).obj i ⟶ B)
    (p : B ⟶ CommRingCat.of Ω) (hf : f.hom.Etale) (hp : f ≫ p = (point g).app i) :
    ∃ (j : (Index g)ᵒᵖ) (v : i ⟶ j) (b : B ⟶ (rings g).obj j),
      f ≫ b = (rings g).map v ∧ b ≫ (point g).app j = p := by
  let e := (smallEquiv g).functor
  let X := e.obj i.unop
  change stageRing g X ⟶ B at f
  change f ≫ p = Spec.preimage X.val.left at hp
  have hpoint : Spec.map p ≫ Spec.map f = X.val.left := by
    rw [← Spec.map_comp, hp, Spec.map_preimage]
  have hEtale : Etale (Spec.map f) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hf
  have hX : Etale X.obj.hom := X.obj.prop
  have hbase : X.val.left ≫ X.obj.hom = g := Over.w X.val
  let Y := mkStage g (Spec.map f ≫ X.obj.hom) p (by
    rw [← Category.assoc, hpoint, hbase])
  let v : Y ⟶ X := Functor.Elements.homMk
    (MorphismProperty.CostructuredArrow.homMk f.op trivial rfl)
    (Over.OverMorphism.ext hpoint)
  let k := e.objPreimage Y
  let a := e.objObjPreimageIso Y
  let h := e.preimage (a.hom ≫ v)
  let b : B ⟶ (rings g).obj (op k) := a.hom.hom.left.unop
  refine ⟨op k, h.op, b, ?_, ?_⟩
  · exact congrArg (fun q : e.obj k ⟶ X => q.hom.left.unop)
      (e.map_preimage (a.hom ≫ v)).symm
  · exact (stagePoint_naturality g a.hom).trans (Spec.preimage_map p)

/-- The affine schemes of the pointed diagram. -/
abbrev diagram : Index g ⥤ Scheme.{u} := coordinateRings g ⋙ Scheme.Spec

instance diagramAffine (i : Index g) : IsAffine ((diagram g).obj i) :=
  inferInstanceAs (IsAffine (Spec ((rings g).obj (op i))))

set_option backward.isDefEq.respectTransparency false in
/-- The étale structural maps form a natural transformation to the base. -/
def structural : diagram g ⟶ (Functor.const (Index g)).obj S where
  app i := ((smallEquiv g).functor.obj i).obj.hom
  naturality _ _ f := ((smallEquiv g).functor.map f).hom.w

instance structuralEtale (i : Index g) : Etale ((structural g).app i) :=
  ((smallEquiv g).functor.obj i).obj.prop

/-- The geometric point of a stage, recovered from its coordinate-ring map. -/
theorem point_over (i : Index g) : Spec.map ((point g).app (op i)) ≫ (structural g).app i = g := by
  let X := (smallEquiv g).functor.obj i
  exact (congrArg (fun f => f ≫ X.obj.hom) (Spec.map_preimage X.val.left)).trans (Over.w X.val)

/-- The spectrum of a ring cocone point carries a cone on the schemes. -/
def spectrumCone (c : Cocone (rings g)) : Cone (diagram g) :=
  Scheme.Spec.mapCone (coneOfCoconeLeftOp c)

/-- Taking spectra of a colimiting ring cocone gives a limiting scheme cone. -/
def spectrumConeIsLimit {c : Cocone (rings g)} (hc : IsColimit c) :
    IsLimit (spectrumCone g c) :=
  isLimitOfPreserves Scheme.Spec (isLimitConeOfCoconeLeftOp (coordinateRings g) hc)

/-- The cone maps are the spectra of the ring cocone maps. -/
theorem spectrumCone_π_app (c : Cocone (rings g)) (i : Index g) :
    (spectrumCone g c).π.app i = Spec.map (c.ι.app (op i)) := rfl

private def chosenStage [IsSepClosed Ω] : Index g :=
  Classical.choice IsCofiltered.nonempty

/-- The cone maps induce a map from the spectrum to the base. -/
def baseMap [IsSepClosed Ω] (c : Cocone (rings g)) : Spec c.pt ⟶ S :=
  (spectrumCone g c).π.app (chosenStage g) ≫ (structural g).app (chosenStage g)

set_option backward.isDefEq.respectTransparency false in
/-- Every stage gives the same map from the spectrum to the base. -/
theorem spectrumCone_compatible [IsSepClosed Ω] (c : Cocone (rings g)) (i : Index g) :
    (spectrumCone g c).π.app i ≫ (structural g).app i = baseMap g c := by
  let k := chosenStage g
  let fromLeft := IsCofiltered.minToLeft i k
  let fromRight := IsCofiltered.minToRight i k
  have agree {a b : Index g} (f : a ⟶ b) :
      (spectrumCone g c).π.app b ≫ (structural g).app b =
        (spectrumCone g c).π.app a ≫ (structural g).app a := by
    rw [← (spectrumCone g c).w f, Category.assoc,
      (structural g).naturality f, Functor.const_obj_map]
    exact congrArg ((spectrumCone g c).π.app a ≫ ·) (Category.comp_id _)
  exact (agree fromLeft).trans (agree fromRight).symm

set_option backward.isDefEq.respectTransparency false in
/-- The map to the base sends a compatible field point to the original geometric point. -/
theorem baseMap_point [IsSepClosed Ω] (c : Cocone (rings g)) (p : c.pt ⟶ CommRingCat.of Ω)
    (hp : ∀ i, c.ι.app i ≫ p = (point g).app i) :
    Spec.map p ≫ baseMap g c = g := by
  change Spec.map p ≫ ((spectrumCone g c).π.app (chosenStage g) ≫
    (structural g).app (chosenStage g)) = g
  rw [← Category.assoc, spectrumCone_π_app, ← Spec.map_comp, hp, point_over]

end PointedAffineEtale

end Langlands.AlgebraicGeometry
