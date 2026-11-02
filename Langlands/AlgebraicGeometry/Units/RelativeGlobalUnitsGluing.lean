import Langlands.AlgebraicGeometry.Units.RelativeGlobalUnits
import Mathlib.AlgebraicGeometry.Gluing

/-! # Extending representation of relative units from affine tests -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.RelativeGlobalUnits

variable {S X : Scheme.{u}} (f : X ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Relative units can be compared on any open cover of the test scheme. -/
lemma sections_ext_of_openCover (T : Over S) (𝒰 : T.left.OpenCover)
    (s t : sections f T)
    (h : ∀ i, restriction f
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) s =
      restriction f
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) t) :
    s = t := by
  apply _root_.Units.ext
  apply Scheme.OpenCover.ext_elem _ _ (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f)
  intro i
  have hm :
      (Picard.relativeSpace f).map
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) =
        (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).f i := by
    apply pullback.hom_ext <;>
      simp [Picard.relativeSpace, Over.pullback, Scheme.Pullback.openCoverOfLeft,
        pullback.map]
  change ((Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).f i).appTop s.val =
    ((Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).f i).appTop t.val
  have hi := congrArg _root_.Units.val (h i)
  dsimp only [restriction_val] at hi
  rw [hm] at hi
  exact hi

/-- Injectivity of pullback of a universal unit is local on the test scheme. -/
lemma restriction_injective_of_affine (U : Over S) (a : sections f U)
    (h : ∀ (V : Over S) [IsAffine V.left],
      Function.Injective (fun j : V ⟶ U => restriction f j a))
    (T : Over S) :
    Function.Injective (fun j : T ⟶ U => restriction f j a) := by
  intro j l hj
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro i
  let V : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let : IsAffine V.left :=
    inferInstanceAs (IsAffine (T.left.affineCover.X i))
  let ι : V ⟶ T := Over.homMk (T.left.affineCover.f i)
  have he : ι ≫ j = ι ≫ l := by
    apply h V
    simpa only [restriction_comp] using congrArg (restriction f ι) hj
  exact congrArg (fun e : V ⟶ U => e.left) he

set_option backward.isDefEq.respectTransparency false in
/-- Bijectivity on affine tests extends by gluing to every test scheme. -/
lemma restriction_bijective_of_affine (U : Over S) (a : sections f U)
    (h : ∀ (V : Over S) [IsAffine V.left],
      Function.Bijective (fun j : V ⟶ U => restriction f j a))
    (T : Over S) :
    Function.Bijective (fun j : T ⟶ U => restriction f j a) := by
  classical
  have hinj : ∀ (V : Over S) [IsAffine V.left],
      Function.Injective (fun j : V ⟶ U => restriction f j a) := by
    intro V hV j l hj
    exact (h V).1 hj
  refine ⟨restriction_injective_of_affine f U a hinj T, ?_⟩
  intro t
  let 𝒰 := T.left.affineCover
  let V (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)
  let ι (i : 𝒰.I₀) : V i ⟶ T := Over.homMk (𝒰.f i)
  have ha (i : 𝒰.I₀) : IsAffine (V i).left :=
    inferInstanceAs (IsAffine (T.left.affineCover.X i))
  choose g hg using fun i => (h (V i)).2 (restriction f (ι i) t)
  dsimp only at hg
  have hc (i j : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (g i).left =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ (g j).left := by
    let W : Over S :=
      Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)
    let p : W ⟶ V i := Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j))
    let q : W ⟶ V j := Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
      (by simpa only [W, V, Over.mk_hom] using
        (pullback.condition_assoc (f := 𝒰.f i) (g := 𝒰.f j) T.hom).symm)
    have hpq : p ≫ ι i = q ≫ ι j := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have he : p ≫ g i = q ≫ g j := by
      apply restriction_injective_of_affine f U a hinj W
      dsimp only
      rw [restriction_comp, restriction_comp, hg i, hg j,
        ← restriction_comp, ← restriction_comp, hpq]
    exact congrArg (fun e : W ⟶ U => e.left) he
  let glued : T.left ⟶ U.left := 𝒰.glueMorphisms (fun i => (g i).left) hc
  have hw : glued ≫ U.hom = T.hom := by
    apply 𝒰.hom_ext
    intro i
    dsimp only [glued]
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
    exact Over.w (g i)
  let j : T ⟶ U := Over.homMk glued hw
  refine ⟨j, ?_⟩
  apply sections_ext_of_openCover f T 𝒰
  intro i
  have he : ι i ≫ j = g i := by
    apply Over.OverMorphism.ext
    exact Scheme.Cover.ι_glueMorphisms 𝒰 _ hc i
  change restriction f (ι i) (restriction f j a) = restriction f (ι i) t
  rw [← restriction_comp, he, hg i]

/-- The canonical natural transformation is an isomorphism if its affine
components are bijective. -/
lemma fromUniversalUnit_isIso_of_affine (U : Over S) (a : sections f U)
    (h : ∀ (V : Over S) [IsAffine V.left],
      Function.Bijective ((fromUniversalUnit f U a).app (op V))) :
    IsIso (fromUniversalUnit f U a) := by
  have hb : ∀ (V : Over S) [IsAffine V.left],
      Function.Bijective (fun j : V ⟶ U => restriction f j a) := by
    intro V hV
    constructor
    · intro j l hj
      have he : (⟨j⟩ : ULift.{u + 1} (V ⟶ U)) = ⟨l⟩ :=
        (h V).1 (ULift.ext _ _ hj)
      exact congrArg ULift.down he
    · intro t
      obtain ⟨j, hj⟩ := (h V).2 ⟨t⟩
      exact ⟨j.down, congrArg ULift.down hj⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  have hV := restriction_bijective_of_affine f U a hb V.unop
  constructor
  · intro j l hj
    apply ULift.ext
    apply hV.1
    exact congrArg ULift.down hj
  · intro t
    obtain ⟨j, hj⟩ := hV.2 t.down
    exact ⟨⟨j⟩, ULift.ext _ _ hj⟩

/-- The actual presheaf isomorphism obtained from affine bijectivity of pullback
of the specified universal unit. -/
def fromUniversalUnitIsoOfAffine (U : Over S) (a : sections f U)
    (h : ∀ (V : Over S) [IsAffine V.left],
      Function.Bijective ((fromUniversalUnit f U a).app (op V))) :
    (AlgebraicSpace.schemeYoneda S).obj U ≅ presheaf f := by
  let := fromUniversalUnit_isIso_of_affine f U a h
  exact asIso (fromUniversalUnit f U a)

@[simp]
lemma fromUniversalUnitIsoOfAffine_hom (U : Over S) (a : sections f U)
    (h : ∀ (V : Over S) [IsAffine V.left],
      Function.Bijective ((fromUniversalUnit f U a).app (op V))) :
    (fromUniversalUnitIsoOfAffine f U a h).hom = fromUniversalUnit f U a := rfl

end Langlands.AlgebraicGeometry.RelativeGlobalUnits
