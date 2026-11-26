import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point

/-! # Relative Hom schemes on arbitrary test schemes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AbelianScheme.PointedLaw

universe u

variable {S : Scheme.{u}}

/-- A representing object and evaluation for maps out of the relative product with `P`. -/
structure HomScheme (P X : Over S) where
  obj : Over S
  separated : IsSeparated obj.hom
  finitePresentation : LocallyOfFinitePresentation obj.hom
  evaluation : P ⊗ obj ⟶ X
  bijective (T : Over S) : Function.Bijective (fun f : T ⟶ obj => (P ◁ f) ≫ evaluation)

namespace HomScheme

variable {P X : Over S} (H : HomScheme P X) {T U : Over S}

/-- The morphism classified by a point in the Hom scheme. -/
def eval (a : T ⟶ H.obj) : P ⊗ T ⟶ X := (P ◁ a) ≫ H.evaluation

@[simp]
theorem eval_comp (b : U ⟶ T) (a : T ⟶ H.obj) :
    H.eval (b ≫ a) = (P ◁ b) ≫ H.eval a := by
  simp [eval, whiskerLeft_comp]

/-- The point of the Hom scheme classified by a morphism on the relative product. -/
def classify (f : P ⊗ T ⟶ X) : T ⟶ H.obj :=
  (Equiv.ofBijective _ (H.bijective T)).symm f

@[simp]
theorem eval_classify (f : P ⊗ T ⟶ X) : H.eval (H.classify f) = f :=
  (Equiv.ofBijective _ (H.bijective T)).apply_symm_apply f

@[simp]
theorem classify_eval (a : T ⟶ H.obj) : H.classify (H.eval a) = a :=
  (Equiv.ofBijective _ (H.bijective T)).symm_apply_apply a

@[simp]
theorem comp_classify (b : U ⟶ T) (f : P ⊗ T ⟶ X) :
    b ≫ H.classify f = H.classify ((P ◁ b) ≫ f) := by
  apply (H.bijective U).1
  change H.eval _ = H.eval _
  simp

end HomScheme

section AffineExtension

variable {P X H : Over S} (ev : P ⊗ H ⟶ X)

private abbrev chart (T : Over S) (i : T.left.affineCover.I₀) : Over S :=
  Over.mk (T.left.affineCover.f i ≫ T.hom)

private abbrev chartι (T : Over S) (i : T.left.affineCover.I₀) : chart T i ⟶ T :=
  Over.homMk (T.left.affineCover.f i)

local instance chart_isAffine (T : Over S) (i : T.left.affineCover.I₀) :
    IsAffine (chart T i).left := inferInstanceAs (IsAffine (Spec _))

private theorem hom_ext_of_affine_cover {T : Over S} {a b : P ⊗ T ⟶ X}
    (h : ∀ i, (P ◁ chartι T i) ≫ a = (P ◁ chartι T i) ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  refine (Scheme.Pullback.openCoverOfRight T.left.affineCover P.hom T.hom).hom_ext _ _ ?_
  intro i
  change (P ◁ chartι T i).left ≫ a.left = (P ◁ chartι T i).left ≫ b.left
  exact congrArg Over.Hom.left (h i)

private theorem extend_bijective
    (haff : ∀ (T : Over S) [IsAffine T.left],
      Function.Bijective (fun a : T ⟶ H => (P ◁ a) ≫ ev)) (T : Over S) :
    Function.Bijective (fun a : T ⟶ H => (P ◁ a) ≫ ev) := by
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun i => ?_
    have hi : chartι T i ≫ a = chartι T i ≫ b := by
      apply (haff (chart T i)).1
      simp only [whiskerLeft_comp, Category.assoc, hab]
    exact congrArg Over.Hom.left hi
  · intro m
    have hex (i : T.left.affineCover.I₀) :
        ∃ a : chart T i ⟶ H, (P ◁ a) ≫ ev = (P ◁ chartι T i) ≫ m :=
      (haff (chart T i)).2 ((P ◁ chartι T i) ≫ m)
    choose a ha using hex
    have hcompat (i j : T.left.affineCover.I₀) :
        pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j) ≫ (a i).left =
          pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j) ≫ (a j).left := by
      let V := pullback (T.left.affineCover.f i) (T.left.affineCover.f j)
      refine V.affineCover.hom_ext _ _ fun k => ?_
      let W := Over.mk (V.affineCover.f k ≫
        pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j) ≫
        T.left.affineCover.f i ≫ T.hom)
      let : IsAffine W.left := inferInstanceAs (IsAffine (Spec _))
      let p : W ⟶ chart T i := Over.homMk (V.affineCover.f k ≫ pullback.fst _ _)
      let q : W ⟶ chart T j := Over.homMk (V.affineCover.f k ≫ pullback.snd _ _) (by
        simp only [W, Over.mk_hom, Category.assoc, pullback.condition_assoc])
      have hpq : p ≫ chartι T i = q ≫ chartι T j := by
        apply Over.OverMorphism.ext
        change (V.affineCover.f k ≫ pullback.fst _ _) ≫ T.left.affineCover.f i =
          (V.affineCover.f k ≫ pullback.snd _ _) ≫ T.left.affineCover.f j
        simp only [Category.assoc, pullback.condition]
      have hab : p ≫ a i = q ≫ a j := by
        apply (haff W).1
        change (P ◁ (p ≫ a i)) ≫ ev = (P ◁ (q ≫ a j)) ≫ ev
        rw [whiskerLeft_comp, whiskerLeft_comp, Category.assoc, Category.assoc, ha, ha,
          ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hpq]
      simpa only [Over.comp_left, Over.homMk_left, p, q, Category.assoc] using
        congrArg Over.Hom.left hab
    let b := T.left.affineCover.glueMorphisms (fun i => (a i).left) hcompat
    have hb (i : T.left.affineCover.I₀) : T.left.affineCover.f i ≫ b = (a i).left :=
      T.left.affineCover.ι_glueMorphisms _ hcompat i
    let c : T ⟶ H := Over.homMk b (by
      refine T.left.affineCover.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, hb, Over.w (a i)]
      rfl)
    have hc (i : T.left.affineCover.I₀) : chartι T i ≫ c = a i :=
      Over.OverMorphism.ext (hb i)
    refine ⟨c, hom_ext_of_affine_cover fun i => ?_⟩
    rw [← whiskerLeft_comp_assoc, hc, ha]

end AffineExtension

/-- The Hom schemes for two flat, locally finitely presented, H-projective families over an
    affine base classify maps on arbitrary schemes over that base. -/
theorem exists_homScheme {R : Type u} [CommRing R] {P X : Over (Spec (CommRingCat.of R))}
    [Flat P.hom] [Flat X.hom] [LocallyOfFinitePresentation P.hom]
    [LocallyOfFinitePresentation X.hom]
    (hP : Langlands.AlgebraicGeometry.IsHProjective P.hom)
    (hX : Langlands.AlgebraicGeometry.IsHProjective X.hom) : Nonempty (HomScheme P X) := by
  have : IsProper P.hom := hP.isProper
  have : IsProper X.hom := hX.isProper
  obtain ⟨LP, hLP, hLP'⟩ :=
    (Langlands.AlgebraicGeometry.Picard.exists_closedImmersionBySections_iff_isHProjective _).2 hP
  obtain ⟨LX, hLX, hLX'⟩ :=
    (Langlands.AlgebraicGeometry.Picard.exists_closedImmersionBySections_iff_isHProjective _).2 hX
  obtain ⟨H, q, pt, hnat, hsurj, hinj, hsep, hfp, -⟩ :=
    AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
      R P.hom X.hom LP hLP hLP' LX hLX hLX'
  obtain ⟨φ, hφ, hφspec⟩ :=
    AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
      R P.hom X.hom q pt hnat hsurj hinj
  let E := Over.mk q
  let ev : P ⊗ E ⟶ X := Over.homMk φ (hφ.trans pullback.condition.symm)
  refine ⟨⟨E, hsep, hfp, ev, extend_bijective ev ?_⟩⟩
  have hspec {A : Type u} [CommRing A] (t : Spec (CommRingCat.of A) ⟶ _) :
      Function.Bijective (fun a : Over.mk t ⟶ E => (P ◁ a) ≫ ev) := by
    let fromHom (m : P ⊗ Over.mk t ⟶ X) : Over.mk t ⟶ E :=
      let a := pt A t m.left ((Over.w m).trans pullback.condition)
      Over.homMk a.1 a.2
    have hr (m : P ⊗ Over.mk t ⟶ X) : (P ◁ fromHom m) ≫ ev = m := by
      apply Over.OverMorphism.ext
      exact hφspec A t m.left ((Over.w m).trans pullback.condition)
    have hs (a : Over.mk t ⟶ E) : fromHom ((P ◁ a) ≫ ev) = a := by
      obtain ⟨m, hm, hpt⟩ := hsurj A t ⟨a.left, Over.w a⟩
      let m' : P ⊗ Over.mk t ⟶ X := Over.homMk m (hm.trans pullback.condition.symm)
      have he : fromHom m' = a := Over.OverMorphism.ext (congrArg Subtype.val hpt)
      rw [← he, hr]
    exact ⟨Function.LeftInverse.injective hs, Function.RightInverse.surjective hr⟩
  intro T _
  let i := T.left.isoSpec.inv
  let t := i ≫ T.hom
  let e : Over.mk t ≅ T := Over.isoMk T.left.isoSpec.symm rfl
  constructor
  · intro a b hab
    have he : e.hom ≫ a = e.hom ≫ b := by
      apply (hspec t).1
      simp only [whiskerLeft_comp, Category.assoc, hab]
    exact (cancel_epi e.hom).1 he
  · intro m
    obtain ⟨a, ha⟩ := (hspec t).2 ((P ◁ e.hom) ≫ m)
    refine ⟨e.inv ≫ a, ?_⟩
    change (P ◁ (e.inv ≫ a)) ≫ ev = m
    simp only [whiskerLeft_comp, Category.assoc, ha, ← whiskerLeft_comp_assoc,
      Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

end Langlands.AbelianScheme.PointedLaw
