import Langlands.AbelianScheme.RelativeEndomorphismOfAffineHomSchemeGluing

/-! # Representability of relative homomorphisms from affine test schemes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.Cartier

universe u
variable {S : Scheme.{u}}

/-- The inclusion of the full subcategory of schemes over `S` with affine source. -/
abbrev affineOverι (S : Scheme.{u}) :=
  ObjectProperty.ι (fun T : Over S => IsAffine T.left)

/-- A member of the affine open cover of a scheme over `S`, as a scheme over `S`. -/
abbrev affineCoverOver (T : Over S) (i : T.left.affineCover.I₀) : Over S :=
  Over.mk (T.left.affineCover.f i ≫ T.hom)

/-- The inclusion of a member of the affine open cover of a scheme over `S`. -/
abbrev affineCoverHom (T : Over S) (i : T.left.affineCover.I₀) : affineCoverOver T i ⟶ T :=
  Over.homMk (T.left.affineCover.f i)

instance (T : Over S) (i : T.left.affineCover.I₀) : IsAffine (affineCoverOver T i).left :=
  inferInstanceAs (IsAffine (Spec _))

instance (T : Over S) (i : T.left.affineCover.I₀) :
    IsOpenImmersion (affineCoverHom T i).left :=
  inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))

section Extension

variable {G H : CommGroupScheme S} {E : Over S}
  (α : (affineOverι S).op ⋙ (relativeHomFunctor G H ⋙ forget AddCommGrpCat.{u}) ≅
    (affineOverι S).op ⋙ yoneda.obj E)

/-- The component of `α` at an affine scheme over `S`. -/
def affHom (T : Over S) [IsAffine T.left] (χ : RelativeHom G H T) : T ⟶ E :=
  α.hom.app (op ⟨T, inferInstance⟩) χ

/-- The component of `α⁻¹` at an affine scheme over `S`. -/
def affInv (T : Over S) [IsAffine T.left] (g : T ⟶ E) : RelativeHom G H T :=
  α.inv.app (op ⟨T, inferInstance⟩) g

lemma affHom_restrict {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (b : T' ⟶ T)
    (χ : RelativeHom G H T) : affHom α T' (restrict G H b χ) = b ≫ affHom α T χ := by
  have h := α.hom.naturality_apply (ObjectProperty.homMk
    (P := fun T : Over S => IsAffine T.left)
    (X := ⟨T', inferInstance⟩) (Y := ⟨T, inferInstance⟩) b).op χ
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ObjectProperty.ι_map] at h
  exact h

lemma affInv_comp {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (b : T' ⟶ T)
    (g : T ⟶ E) : affInv α T' (b ≫ g) = restrict G H b (affInv α T g) :=
  α.inv.naturality_apply (ObjectProperty.homMk (P := fun T : Over S => IsAffine T.left)
    (X := ⟨T', inferInstance⟩) (Y := ⟨T, inferInstance⟩) b).op g

lemma affHom_affInv (T : Over S) [IsAffine T.left] (g : T ⟶ E) :
    affHom α T (affInv α T g) = g :=
  α.inv_hom_id_app_apply (op ⟨T, inferInstance⟩) g

lemma affInv_affHom (T : Over S) [IsAffine T.left] (χ : RelativeHom G H T) :
    affInv α T (affHom α T χ) = χ :=
  α.hom_inv_id_app_apply (op ⟨T, inferInstance⟩) χ

/-- A relative homomorphism over `E` whose restriction along every morphism from an affine
scheme is given by `α⁻¹`. -/
lemma exists_universal_relativeHom :
    ∃ u : RelativeHom G H E, ∀ (T : Over S) [IsAffine T.left] (g : T ⟶ E),
      restrict G H g u = affInv α T g := by
  obtain ⟨u, hu⟩ := relativeHom_exists_glue (affineCoverOver E) (affineCoverHom E)
    (fun x => by
      obtain ⟨i, y, hy⟩ := E.left.affineCover.exists_eq x
      exact ⟨i, y, hy⟩)
    (fun j => affInv α (affineCoverOver E j) (affineCoverHom E j))
    (fun i j Z p q hpq => by
      refine relativeHom_eq_of_forall_isAffine _ _ fun W b hW _ => ?_
      rw [← restrict_comp, ← restrict_comp, ← affInv_comp, ← affInv_comp, Category.assoc,
        Category.assoc, hpq])
  refine ⟨u, fun T _ g => relativeHom_eq_of_locally _ _ fun x => ?_⟩
  obtain ⟨j, y, hy⟩ := E.left.affineCover.exists_eq (g.left x)
  have hx : x ∈ Set.range (pullback.fst g.left (E.left.affineCover.f j)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  obtain ⟨k, w, hw⟩ := (pullback g.left (E.left.affineCover.f j)).affineCover.exists_eq z
  let W : Over S := Over.mk ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
    pullback.fst g.left (E.left.affineCover.f j) ≫ T.hom)
  have : IsAffine W.left := inferInstanceAs (IsAffine (Spec _))
  let a : W ⟶ T := Over.homMk ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
    pullback.fst g.left (E.left.affineCover.f j))
  let c : W ⟶ affineCoverOver E j :=
    Over.homMk ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
      pullback.snd g.left (E.left.affineCover.f j)) (by
        simp only [W, Over.mk_hom, Category.assoc]
        rw [← pullback.condition_assoc, Over.w g])
  have hac : a ≫ g = c ≫ affineCoverHom E j := by
    apply Over.OverMorphism.ext
    show ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
      pullback.fst g.left (E.left.affineCover.f j)) ≫ g.left =
      ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
      pullback.snd g.left (E.left.affineCover.f j)) ≫ E.left.affineCover.f j
    rw [Category.assoc, Category.assoc, pullback.condition]
  refine ⟨W, a, inferInstanceAs (IsOpenImmersion
    ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
      pullback.fst g.left (E.left.affineCover.f j))), ⟨w, ?_⟩, ?_⟩
  · show ((pullback g.left (E.left.affineCover.f j)).affineCover.f k ≫
      pullback.fst g.left (E.left.affineCover.f j)) w = x
    rw [Scheme.Hom.comp_apply, hw, hz]
  · rw [← restrict_comp, hac, restrict_comp, hu, ← affInv_comp, ← hac, affInv_comp]

include α in
/-- A natural isomorphism between the relative Hom functor and the functor of points of `E` on
affine schemes over `S` extends to all schemes over `S`. -/
theorem nonempty_iso_yoneda_of_affine :
    Nonempty ((relativeHomFunctor G H ⋙ forget AddCommGrpCat.{u}) ≅ yoneda.obj E) := by
  obtain ⟨u, hu⟩ := exists_universal_relativeHom α
  have bij : ∀ T : Over S, Function.Bijective (fun g : T ⟶ E => restrict G H g u) := by
    intro T
    constructor
    · intro g g' h
      simp only at h
      apply Over.OverMorphism.ext
      refine T.left.affineCover.hom_ext _ _ fun i => ?_
      have h1 : restrict G H (affineCoverHom T i ≫ g) u =
          restrict G H (affineCoverHom T i ≫ g') u := by
        rw [restrict_comp, restrict_comp, h]
      rw [hu, hu] at h1
      have h2 := congrArg (affHom α _) h1
      rw [affHom_affInv, affHom_affInv] at h2
      exact congrArg Over.Hom.left h2
    · intro χ
      let gi : ∀ i, affineCoverOver T i ⟶ E := fun i =>
        affHom α _ (restrict G H (affineCoverHom T i) χ)
      have hcompat : ∀ i j,
          pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j) ≫ (gi i).left =
            pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j) ≫ (gi j).left := by
        intro i j
        refine (pullback (T.left.affineCover.f i) (T.left.affineCover.f j)).affineCover.hom_ext
          _ _ fun k => ?_
        let V := pullback (T.left.affineCover.f i) (T.left.affineCover.f j)
        let W : Over S := Over.mk (V.affineCover.f k ≫
          pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j) ≫
          T.left.affineCover.f i ≫ T.hom)
        have : IsAffine W.left := inferInstanceAs (IsAffine (Spec _))
        let p : W ⟶ affineCoverOver T i := Over.homMk (V.affineCover.f k ≫
          pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j))
        let q : W ⟶ affineCoverOver T j := Over.homMk (V.affineCover.f k ≫
          pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j)) (by
            simp only [W, Over.mk_hom, Category.assoc]
            rw [← pullback.condition_assoc])
        have hpq : p ≫ affineCoverHom T i = q ≫ affineCoverHom T j := by
          apply Over.OverMorphism.ext
          show (V.affineCover.f k ≫
              pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j)) ≫
              T.left.affineCover.f i =
            (V.affineCover.f k ≫
              pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j)) ≫
              T.left.affineCover.f j
          rw [Category.assoc, Category.assoc, pullback.condition]
        have hpq' : p ≫ gi i = q ≫ gi j := by
          simp only [gi]
          rw [← affHom_restrict, ← affHom_restrict, ← restrict_comp, ← restrict_comp, hpq]
        have h3 : (V.affineCover.f k ≫
              pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j)) ≫ (gi i).left =
            (V.affineCover.f k ≫
              pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j)) ≫ (gi j).left :=
          congrArg Over.Hom.left hpq'
        simpa only [Category.assoc] using h3
      let m := T.left.affineCover.glueMorphisms (fun i => (gi i).left) hcompat
      have hmi : ∀ i, T.left.affineCover.f i ≫ m = (gi i).left :=
        fun i => T.left.affineCover.ι_glueMorphisms _ hcompat i
      have hm : m ≫ E.hom = T.hom := by
        refine T.left.affineCover.hom_ext _ _ fun i => ?_
        rw [reassoc_of% (hmi i), Over.w (gi i)]
        rfl
      let g : T ⟶ E := Over.homMk m hm
      have hg : ∀ i, affineCoverHom T i ≫ g = gi i := fun i => Over.OverMorphism.ext (hmi i)
      refine ⟨g, relativeHom_eq_of_locally _ _ fun x => ?_⟩
      obtain ⟨i, y, hy⟩ := T.left.affineCover.exists_eq x
      refine ⟨_, affineCoverHom T i, inferInstance, ⟨y, hy⟩, ?_⟩
      rw [← restrict_comp, hu, hg, affInv_affHom]
  refine ⟨(NatIso.ofComponents
    (fun T => (Equiv.ofBijective (fun g : T.unop ⟶ E => restrict G H g u) (bij T.unop)).toIso)
    ?_).symm⟩
  intro T T' b
  ext g
  exact restrict_comp G H b.unop g u

end Extension

end Langlands.GroupScheme.Cartier
