/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods

/-!
# Function fields in a dominant affine transition limit

## References

* Stacks Project, Tag 0EZJ, generic-fibre limit assertion
* Stacks Project, Tag 0EZJ, the function-field part of the generic-fibre limit assertion
* Stacks Project, Tag 01ZA
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A dominant morphism maps the generic point to the generic point. -/
private lemma dominant_map_genericPoint {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at h

/-- The spectrum map of a stalk map, transported along the specified equality of points. -/
private noncomputable def specStalkMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    Spec (X.presheaf.stalk x) ⟶ Spec (Y.presheaf.stalk y) :=
  Spec.map (eqToHom (congrArg Y.presheaf.stalk h.symm) ≫ f.stalkMap x)

@[reassoc (attr := simp)]
private lemma specStalkMapOfEq_fromSpecStalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    specStalkMapOfEq f x y h ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst y
  simp [specStalkMapOfEq]

/-- The canonical spectrum map on function fields for a dominant morphism. -/
private noncomputable def dominantGenericSpecMap {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : IsDominant f) :
    Spec X.functionField ⟶ Spec Y.functionField :=
  let _ := hf
  specStalkMapOfEq f (genericPoint X) (genericPoint Y) (dominant_map_genericPoint f)

@[reassoc (attr := simp)]
private lemma dominantGenericSpecMap_fromSpecStalk {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : IsDominant f) :
    dominantGenericSpecMap f hf ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  unfold dominantGenericSpecMap
  exact specStalkMapOfEq_fromSpecStalk f _ _ _

/-- The diagram of actual spectra of the generic stalks, with their canonical maps. -/
private noncomputable def dominantGenericSpecDiagram {I : Type u} [SmallCategory I]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hd : ∀ {i j : I} (f : i ⟶ j), IsDominant (X.map f)) : I ⥤ Scheme.{u} where
  obj i := Spec (X.obj i).functionField
  map f := dominantGenericSpecMap (X.map f) (hd f)
  map_id i := by
    apply (cancel_mono ((X.obj i).fromSpecStalk (genericPoint (X.obj i)))).mp
    simp
  map_comp f g := by
    apply (cancel_mono ((X.obj _).fromSpecStalk (genericPoint (X.obj _)))).mp
    simp [Category.assoc]

/-- Generic point inclusions give a natural transformation to the original diagram. -/
private noncomputable def dominantGenericSpecInclusions {I : Type u} [SmallCategory I]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hd : ∀ {i j : I} (f : i ⟶ j), IsDominant (X.map f)) :
    dominantGenericSpecDiagram X hd ⟶ X where
  app i := (X.obj i).fromSpecStalk (genericPoint (X.obj i))
  naturality i j f := by
    exact dominantGenericSpecMap_fromSpecStalk (X.map f) (hd f)

set_option backward.isDefEq.respectTransparency false in
/-- The cone on generic stalk spectra induced by a dominant cone. -/
private noncomputable def dominantGenericSpecCone {I : Type u} [SmallCategory I]
    {S : Scheme.{u}} [IsIntegral S]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hd : ∀ {i j : I} (f : i ⟶ j), IsDominant (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (hdom : ∀ i, IsDominant (α.app i)) :
    Cone (dominantGenericSpecDiagram X hd) where
  pt := Spec S.functionField
  π :=
    { app := fun i ↦ dominantGenericSpecMap (X := S) (Y := X.obj i) (α.app i) (hdom i)
      naturality := fun i j f ↦ by
        apply (cancel_mono ((X.obj j).fromSpecStalk (genericPoint (X.obj j)))).mp
        change (𝟙 _ ≫ dominantGenericSpecMap (X := S) (Y := X.obj j) (α.app j) (hdom j)) ≫ _ =
          (dominantGenericSpecMap (X := S) (Y := X.obj i) (α.app i) (hdom i) ≫
            dominantGenericSpecMap (X.map f) (hd f)) ≫ _
        simp only [Category.id_comp, Category.assoc,
          dominantGenericSpecMap_fromSpecStalk_assoc,
          dominantGenericSpecMap_fromSpecStalk]
        rw [← α.naturality f]
        simp }

private lemma eq_genericPoint_of_projections {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}} [IsIntegral S]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
    (hdom : ∀ i, IsDominant (α.app i)) (s : S)
    (hs : ∀ i, α.app i s = genericPoint (X.obj i)) : s = genericPoint S := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f) := hXa
  have hg : s ⤳ genericPoint S := by
    apply specializes_iff_forall_open.mpr
    intro U hU hηU
    obtain ⟨W, ⟨i, V, hV, rfl⟩, hηV, hWU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (isBasis_preimage_isAffineOpen X (Cone.mk S α) hα) (U := ⟨U, hU⟩) hηU
    apply hWU
    change α.app i s ∈ V
    rw [hs i]
    have : IsDominant (α.app i) := hdom i
    rwa [← dominant_map_genericPoint (X := S) (α.app i)]
  exact (hg.antisymm (genericPoint_specializes s)).eq

private lemma exists_generic_factor {S T : Scheme.{u}} [IsIntegral S]
    (g : T ⟶ S) (hg : ∀ x : T, g x = genericPoint S) :
    ∃ l : T ⟶ Spec S.functionField, l ≫ S.fromSpecStalk (genericPoint S) = g := by
  classical
  let N := {W : S.Opens // IsAffineOpen W ∧ genericPoint S ∈ W}
  have range (W : N) : Set.range g ⊆ Set.range W.1.ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨g x, by rw [hg x]; exact W.2.2⟩, rfl⟩
  let tW (W : N) : T ⟶ W.1.toScheme := IsOpenImmersion.lift W.1.ι g (range W)
  have compat (W V : N) (hVW : V.1 ≤ W.1) :
      tW V ≫ S.homOfLE hVW = tW W := by
    apply (cancel_mono W.1.ι).mp
    simp [tW, Category.assoc]
  obtain ⟨l, hl, _⟩ :=
    (fromSpecStalk_limit_affine_neighbourhoods S (genericPoint S)).2.2.2.2.2.2.2.2.2
      T tW compat
  obtain ⟨W, hW, hηW, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  let w : N := ⟨W, hW, hηW⟩
  refine ⟨l, ?_⟩
  rw [← w.1.fromSpecStalkOfMem_ι (genericPoint S) w.2.2, ← Category.assoc, hl w]
  exact IsOpenImmersion.lift_fac w.1.ι g (range w)

set_option backward.isDefEq.respectTransparency false in
private theorem dominantGenericSpecCone_isLimit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}} [IsIntegral S]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hd : ∀ {i j : I} (f : i ⟶ j), IsDominant (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
    (hdom : ∀ i, IsDominant (α.app i)) :
    Nonempty (IsLimit (dominantGenericSpecCone X hd α hdom)) := by
  classical
  let K := dominantGenericSpecDiagram X hd
  let t := dominantGenericSpecInclusions X hd
  let toX (z : Cone K) : Cone X := (Cone.postcompose t).obj z
  let g (z : Cone K) := hα.lift (toX z)
  have hg (z : Cone K) (x : z.pt) : g z x = genericPoint S := by
    apply eq_genericPoint_of_projections X hXa α hα hdom
    intro i
    have he : g z ≫ α.app i = z.π.app i ≫ (X.obj i).fromSpecStalk
        (genericPoint (X.obj i)) := hα.fac (toX z) i
    change (g z ≫ α.app i) x = _
    rw [he, Hom.comp_apply]
    let p : Spec (X.obj i).functionField := (z.π.app i : z.pt ⟶
      Spec (X.obj i).functionField) x
    have heq : p = IsLocalRing.closedPoint (X.obj i).functionField :=
      Subsingleton.elim (α := PrimeSpectrum (X.obj i).functionField) _ _
    change (X.obj i).fromSpecStalk (genericPoint (X.obj i)) p = _
    rw [heq, fromSpecStalk_closedPoint]
  choose lift hlift using fun z ↦ exists_generic_factor (g z) (hg z)
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro z i
    apply (cancel_mono ((X.obj i).fromSpecStalk (genericPoint (X.obj i)))).mp
    change (lift z ≫ dominantGenericSpecMap (X := S) (α.app i) (hdom i)) ≫ _ = _
    rw [Category.assoc, dominantGenericSpecMap_fromSpecStalk, ← Category.assoc, hlift]
    exact hα.fac (toX z) i
  · intro z m hm
    apply (cancel_mono (S.fromSpecStalk (genericPoint S))).mp
    rw [hlift]
    apply hα.uniq (toX z)
    intro i
    have hi := congrArg (fun f ↦ f ≫ (X.obj i).fromSpecStalk
      (genericPoint (X.obj i))) (hm i)
    change (m ≫ dominantGenericSpecMap (X := S) (α.app i) (hdom i)) ≫ _ = _ at hi
    change (m ≫ S.fromSpecStalk (genericPoint S)) ≫ α.app i =
      z.π.app i ≫ (X.obj i).fromSpecStalk (genericPoint (X.obj i))
    simpa only [Category.assoc, dominantGenericSpecMap_fromSpecStalk] using hi

set_option linter.unusedVariables false in
/-- The spectra of the stage function fields have the spectrum of the limit function
field as their limit, compatibly with the generic point inclusions. -/
theorem exists_dominant_function_field_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}} [IsIntegral S]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hXqc : ∀ i, CompactSpace (X.obj i)) (hXqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
    (hdom : ∀ i, IsDominant (α.app i)) :
    ∃ (K : I ⥤ Scheme.{u}) (b : (Functor.const I).obj (Spec S.functionField) ⟶ K)
      (t : K ⟶ X) (e : ∀ i, K.obj i ≅ Spec (X.obj i).functionField)
      (hb : IsLimit (Cone.mk (Spec S.functionField) b)),
      (∀ i, CompactSpace (K.obj i)) ∧ (∀ i, QuasiSeparatedSpace (K.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f)) ∧
      (∀ i, (e i).inv ≫ t.app i = (X.obj i).fromSpecStalk (genericPoint (X.obj i))) ∧
      (∀ i, b.app i ≫ t.app i = S.fromSpecStalk (genericPoint S) ≫ α.app i) := by
  have hd : ∀ {i j : I} (f : i ⟶ j), IsDominant (X.map f) := by
    intro i j f
    have : IsDominant (α.app i ≫ X.map f) := by
      have he : α.app i ≫ X.map f = α.app j := by
        simpa using (α.naturality f).symm
      rw [he]
      exact hdom j
    exact IsDominant.of_comp (α.app i) (X.map f)
  let K := dominantGenericSpecDiagram X hd
  let c := dominantGenericSpecCone X hd α hdom
  obtain ⟨hb⟩ := dominantGenericSpecCone_isLimit X hXa hd α hα hdom
  refine ⟨K, c.π, dominantGenericSpecInclusions X hd, fun i ↦ Iso.refl _, hb,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change CompactSpace (Spec (X.obj i).functionField)
    infer_instance
  · intro i
    change QuasiSeparatedSpace (Spec (X.obj i).functionField)
    infer_instance
  · intro i j f
    change IsAffineHom (dominantGenericSpecMap (X.map f) (hd f))
    infer_instance
  · intro i
    exact Category.id_comp _
  · intro i
    exact dominantGenericSpecMap_fromSpecStalk (X := S) (α.app i) (hdom i)

end AlgebraicGeometry.Scheme
