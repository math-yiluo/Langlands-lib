/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Fibre products and graphs of schemes over a base

For schemes `W`, `T` over `S`, `AlgebraicGeometry.Scheme.overProd W T` is the fibre product
`W ×_S T` as a scheme over `S`, with products of morphisms (`Scheme.overProdMap`) and of
isomorphisms (`Scheme.overProdIso`), the second projection (`Scheme.overProdSnd`) and the graph
`Z ⟶ Z ×_S T` of a morphism (`Scheme.overGraph`), a closed immersion when `T` is separated over
`S`. The product `a ×_S 𝟙` is the base change of `a` along the first projection
(`Scheme.isPullback_overProdMap_left`), so it inherits the properties of `a` that are stable
under base change.

For an endomorphism `φ` of a scheme `Y` separated over `S`, `Scheme.fixedLocus φ` is the closed
subscheme of `Y` where `φ` is the identity (the equalizer of `𝟙` and `φ`); an automorphism `e`
commuting with `φ` restricts to it (`Scheme.fixedLocusIso`). The empty scheme over `S` is
`Scheme.emptyOver`, with its morphisms `Scheme.emptyOverTo`.

## Implementation notes

`Scheme.overProd W T` is isomorphic to the binary product `W ⨯ T` in `Over S` (a pullback over
`S`), but is defined directly as `pullback W.hom T.hom` over `S`: its underlying scheme is then
literally a pullback of schemes, so that the instances of `Mathlib` for pullbacks (finiteness,
étaleness, smoothness, separatedness of the projections) apply to `(overProd W T).left` and to
`(overProdMap a b).left` without transport along the forgetful functor `Over S ⥤ Scheme`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The fibre product `W ×_S T` of two schemes over `S`, as a scheme over `S`. -/
noncomputable def overProd (W T : Over S) : Over S :=
  Over.mk (pullback.snd W.hom T.hom ≫ T.hom)

instance (W T : Over S) [LocallyOfFiniteType W.hom] [LocallyOfFiniteType T.hom] :
    LocallyOfFiniteType (overProd W T).hom := by
  dsimp only [overProd, Over.mk_hom]; infer_instance

instance (W T : Over S) [QuasiCompact W.hom] [QuasiCompact T.hom] :
    QuasiCompact (overProd W T).hom := by
  dsimp only [overProd, Over.mk_hom]; infer_instance

instance (W T : Over S) [IsSeparated W.hom] [IsSeparated T.hom] :
    IsSeparated (overProd W T).hom := by
  dsimp only [overProd, Over.mk_hom]; infer_instance

/-- The product `a ×_S b` of two morphisms of schemes over `S`. -/
noncomputable def overProdMap {W W' T T' : Over S} (a : W ⟶ W') (b : T ⟶ T') :
    overProd W T ⟶ overProd W' T' :=
  Over.homMk (pullback.map _ _ _ _ a.left b.left (𝟙 S) (by simp) (by simp)) (by
    simp [overProd])

lemma overProdMap_left {W W' T T' : Over S} (a : W ⟶ W') (b : T ⟶ T') :
    (overProdMap a b).left =
      pullback.map _ _ _ _ a.left b.left (𝟙 S) (by simp) (by simp) :=
  rfl

@[simp]
lemma overProdMap_id (W T : Over S) : overProdMap (𝟙 W) (𝟙 T) = 𝟙 _ := by
  ext1
  simp only [overProdMap_left, Over.id_left]
  exact pullback.map_id

@[reassoc]
lemma overProdMap_comp {W W' W'' T T' T'' : Over S} (a : W ⟶ W') (a' : W' ⟶ W'')
    (b : T ⟶ T') (b' : T' ⟶ T'') :
    overProdMap (a ≫ a') (b ≫ b') = overProdMap a b ≫ overProdMap a' b' := by
  ext1
  simp only [overProdMap_left, Over.comp_left]
  exact pullback.hom_ext (by simp) (by simp)

/-- The product `e ×_S e'` of two isomorphisms of schemes over `S`. -/
@[simps]
noncomputable def overProdIso {W W' T T' : Over S} (e : W ≅ W') (e' : T ≅ T') :
    overProd W T ≅ overProd W' T' where
  hom := overProdMap e.hom e'.hom
  inv := overProdMap e.inv e'.inv
  hom_inv_id := by rw [← overProdMap_comp, e.hom_inv_id, e'.hom_inv_id, overProdMap_id]
  inv_hom_id := by rw [← overProdMap_comp, e.inv_hom_id, e'.inv_hom_id, overProdMap_id]

@[simp]
lemma overProdIso_refl (W T : Over S) :
    overProdIso (Iso.refl W) (Iso.refl T) = Iso.refl _ := by
  ext1
  exact overProdMap_id W T

lemma overProdIso_trans {W W' W'' T T' T'' : Over S} (e₁ : W ≅ W') (e₂ : W' ≅ W'')
    (e₁' : T ≅ T') (e₂' : T' ≅ T'') :
    overProdIso (e₁ ≪≫ e₂) (e₁' ≪≫ e₂') = overProdIso e₁ e₁' ≪≫ overProdIso e₂ e₂' := by
  ext1
  exact overProdMap_comp _ _ _ _

/-- `a ×_S 𝟙` intertwines the automorphisms `𝟙 ×_S e` of its source and target. -/
@[reassoc]
lemma overProdIso_refl_hom_comp_overProdMap {W W' T : Over S} (a : W ⟶ W') (e : T ≅ T) :
    (overProdIso (Iso.refl W) e).hom ≫ overProdMap a (𝟙 T) =
      overProdMap a (𝟙 T) ≫ (overProdIso (Iso.refl W') e).hom := by
  simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
    Category.comp_id]

/-- The second projection `W ×_S T ⟶ T`. -/
noncomputable def overProdSnd (W T : Over S) : overProd W T ⟶ T :=
  Over.homMk (pullback.snd _ _) rfl

@[reassoc (attr := simp)]
lemma overProdMap_overProdSnd {W W' T T' : Over S} (a : W ⟶ W') (b : T ⟶ T') :
    overProdMap a b ≫ overProdSnd W' T' = overProdSnd W T ≫ b := by
  ext1
  simp [overProdMap_left, overProdSnd]

/-- The graph `Z ⟶ Z ×_S T` of a morphism `g : Z ⟶ T` of schemes over `S`. -/
noncomputable def overGraph {Z T : Over S} (g : Z ⟶ T) : Z ⟶ overProd Z T :=
  Over.homMk (pullback.lift (𝟙 _) g.left (by simp)) (by simp [overProd])

@[reassoc (attr := simp)]
lemma overGraph_overProdSnd {Z T : Over S} (g : Z ⟶ T) : overGraph g ≫ overProdSnd Z T = g := by
  ext1
  simp [overGraph, overProdSnd]

@[reassoc]
lemma overGraph_overProdMap {Z Z' T T' : Over S} {g : Z ⟶ T} {g' : Z' ⟶ T'} (a : Z ⟶ Z')
    (b : T ⟶ T') (h : g ≫ b = a ≫ g') :
    overGraph g ≫ overProdMap a b = a ≫ overGraph g' := by
  ext1
  simp only [overGraph, overProdMap_left, Over.comp_left, Over.homMk_left]
  refine pullback.hom_ext ?_ (by simp [← Over.comp_left, h])
  simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left,
    Category.comp_id]
  exact Category.id_comp _

/-- The graph of a morphism to a separated scheme is a closed immersion. -/
instance {Z T : Over S} (g : Z ⟶ T) [IsSeparated T.hom] :
    IsClosedImmersion (overGraph g).left := by
  have h : (overGraph g).left ≫ pullback.fst Z.hom T.hom = 𝟙 _ := by simp [overGraph]
  have : IsClosedImmersion ((overGraph g).left ≫ pullback.fst Z.hom T.hom) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst Z.hom T.hom)

/-- `a ×_S 𝟙` is the base change of `a` along the first projection. -/
lemma isPullback_overProdMap_left {W W' : Over S} (a : W ⟶ W') (T : Over S) :
    IsPullback (overProdMap a (𝟙 T)).left (pullback.fst W.hom T.hom)
      (pullback.fst W'.hom T.hom) a.left := by
  have e₁ : (overProdMap a (𝟙 T)).left ≫ pullback.snd W'.hom T.hom =
      pullback.snd W.hom T.hom := by
    simp [overProdMap_left]
  refine IsPullback.of_right (h₁₂ := pullback.snd W'.hom T.hom) (h₂₂ := W'.hom)
    (v₁₃ := T.hom) ?_ (by simp [overProdMap_left]) (IsPullback.of_hasPullback _ _).flip
  rw [e₁, Over.w a]
  exact (IsPullback.of_hasPullback W.hom T.hom).flip

instance {W W' : Over S} (a : W ⟶ W') (T : Over S) [IsClosedImmersion a.left] :
    IsClosedImmersion (overProdMap a (𝟙 T)).left :=
  MorphismProperty.of_isPullback (isPullback_overProdMap_left a T).flip inferInstance

instance {W W' : Over S} (a : W ⟶ W') (T : Over S) [IsFinite a.left] :
    IsFinite (overProdMap a (𝟙 T)).left :=
  MorphismProperty.of_isPullback (isPullback_overProdMap_left a T).flip inferInstance

instance {W W' : Over S} (a : W ⟶ W') (T : Over S) [Etale a.left] :
    Etale (overProdMap a (𝟙 T)).left :=
  MorphismProperty.of_isPullback (isPullback_overProdMap_left a T).flip inferInstance

instance {W W' : Over S} (a : W ⟶ W') (T : Over S) (n : ℕ)
    [SmoothOfRelativeDimension n a.left] :
    SmoothOfRelativeDimension n (overProdMap a (𝟙 T)).left :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
    (isPullback_overProdMap_left a T).flip inferInstance

instance (W T : Over S) [IsIso W.hom] : IsIso (overProdSnd W T).left :=
  inferInstanceAs (IsIso (pullback.snd W.hom T.hom))

/-! ### The fixed locus of an endomorphism -/

section FixedLocus

variable {Y : Over S} (φ : Y ⟶ Y)

/-- The closed subscheme of `Y` on which an endomorphism `φ` is the identity: the equalizer of
`𝟙` and `φ`. -/
noncomputable abbrev fixedLocus : Over S := equalizer (𝟙 Y) φ

instance [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] :
    LocallyOfFiniteType (fixedLocus φ).hom := by
  rw [← Over.w (equalizer.ι (𝟙 Y) φ)]; infer_instance

instance [QuasiCompact Y.hom] [IsSeparated Y.hom] : QuasiCompact (fixedLocus φ).hom := by
  rw [← Over.w (equalizer.ι (𝟙 Y) φ)]; infer_instance

instance [IsSeparated Y.hom] : IsSeparated (fixedLocus φ).hom := by
  rw [← Over.w (equalizer.ι (𝟙 Y) φ)]; infer_instance

variable (e : Y ≅ Y) (he : e.hom ≫ φ = φ ≫ e.hom)

include he in
lemma inv_comp_eq_comp_inv : e.inv ≫ φ = φ ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The automorphism of the fixed locus of `φ` induced by an automorphism `e` commuting with
`φ`. -/
noncomputable def fixedLocusIso : fixedLocus φ ≅ fixedLocus φ where
  hom := equalizer.lift (equalizer.ι _ _ ≫ e.hom) (by
    rw [Category.assoc, Category.assoc, Category.comp_id, he, ← Category.assoc,
      ← equalizer.condition, Category.comp_id])
  inv := equalizer.lift (equalizer.ι _ _ ≫ e.inv) (by
    rw [Category.assoc, Category.assoc, Category.comp_id, inv_comp_eq_comp_inv φ e he,
      ← Category.assoc, ← equalizer.condition, Category.comp_id])
  hom_inv_id := equalizer.hom_ext (by simp)
  inv_hom_id := equalizer.hom_ext (by simp)

@[reassoc (attr := simp)]
lemma fixedLocusIso_hom_ι :
    (fixedLocusIso φ e he).hom ≫ equalizer.ι _ _ = equalizer.ι _ _ ≫ e.hom := by
  simp [fixedLocusIso]

end FixedLocus

/-! ### The empty scheme -/

section Empty

/-- The empty scheme over `S`. -/
noncomputable def emptyOver : Over S := Over.mk (Scheme.emptyTo S)

instance : IsEmpty (emptyOver (S := S)).left := inferInstanceAs (IsEmpty (∅ : Scheme))

instance : LocallyOfFiniteType (emptyOver (S := S)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Scheme.emptyTo _))

instance : QuasiCompact (emptyOver (S := S)).hom :=
  inferInstanceAs (QuasiCompact (Scheme.emptyTo _))

instance : IsSeparated (emptyOver (S := S)).hom :=
  inferInstanceAs (IsSeparated (Scheme.emptyTo _))

/-- The morphism from the empty scheme. -/
noncomputable def emptyOverTo (X : Over S) : emptyOver ⟶ X :=
  Over.homMk (Scheme.emptyTo _) (Scheme.empty_ext _ _)

instance (X : Over S) : IsOpenImmersion (emptyOverTo X).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.emptyTo _))

lemma emptyOverTo_ext {X : Over S} (f g : emptyOver ⟶ X) : f = g :=
  Over.OverMorphism.ext (Scheme.empty_ext _ _)

end Empty

end AlgebraicGeometry.Scheme
