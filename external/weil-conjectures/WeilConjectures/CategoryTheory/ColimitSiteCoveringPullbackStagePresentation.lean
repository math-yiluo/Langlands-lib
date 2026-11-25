/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ColimitSiteCoveringFamiliesAtStage
import WeilConjectures.CategoryTheory.FilteredColimitPreservesPullback
import WeilConjectures.CategoryTheory.FilteredColimitFiniteIsoLift
public import Mathlib.CategoryTheory.Sites.Precoverage

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem pullback_comparison
    {C K : Type u} [SmallCategory C] [SmallCategory K] (W : C ⥤ K)
    {T A B D : C} (b : B ⟶ T) (a : A ⟶ T) (q₁ : D ⟶ B) (q₂ : D ⟶ A)
    (hsq : IsPullback q₁ q₂ b a) [PreservesLimit (cospan b a) W]
    {S X Y P' : K} (f : X ⟶ S) (g : Y ⟶ S) (p₁ : P' ⟶ Y) (p₂ : P' ⟶ X)
    (h : IsPullback p₁ p₂ g f)
    (hg : Arrow.mk (W.map b) = Arrow.mk g)
    (ha : Arrow.mk (W.map a) = Arrow.mk f) (eB : W.obj B = Y) :
    ∃ E : W.obj D ≅ P', E.inv ≫ W.map q₁ ≫ eqToHom eB = p₁ := by
  obtain ⟨hY, hS, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst Y
  subst S
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g
  obtain ⟨hX, _, ha⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
  subst X
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha
  subst f
  let hm := hsq.map W
  exact ⟨hm.isoIsPullback _ _ h, by simp [hm.isoIsPullback_inv_fst _ _ h]⟩

private theorem arrow_comp_eq
    {C : Type u} [SmallCategory C] {A B X Y Z : C}
    (r : A ⟶ B) (s : B ⟶ X) (r' : Y ⟶ Z) (s' : Z ⟶ X)
    (hr : Arrow.mk r = Arrow.mk r') (hs : Arrow.mk s = Arrow.mk s') :
    Arrow.mk (r ≫ s) = Arrow.mk (r' ≫ s') := by
  obtain ⟨hA, hB, hr⟩ := (Arrow.mk_eq_mk_iff _ _).mp hr
  subst Y
  subst Z
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hr
  subst r'
  obtain ⟨_, _, hs⟩ := (Arrow.mk_eq_mk_iff _ _).mp hs
  simpa using congrArg (fun s ↦ Arrow.mk (r ≫ s)) hs

private theorem presieve_mem_of_arrow_eq
    {C : Type u} [SmallCategory C] {X Z B : C}
    (f : X ⟶ B) (g : Z ⟶ B) (h : Arrow.mk f = Arrow.mk g)
    (R : Presieve B) (hg : R g) : R f := by
  obtain ⟨hX, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst Z
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  exact hg

private theorem presieve_eq_of_arrow_eq
    {C : Type u} [SmallCategory C] {ι : Type u} {B Y : C}
    (D : ι → C) (q : ∀ i, D i ⟶ B) (Z : ι → C) (p : ∀ i, Z i ⟶ Y)
    (e : B = Y) (h : ∀ i, Arrow.mk (q i) = Arrow.mk (p i)) :
    e ▸ Presieve.ofArrows D q = Presieve.ofArrows Z p := by
  subst Y
  apply le_antisymm
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact presieve_mem_of_arrow_eq _ _ (h i) _ (Presieve.ofArrows.mk i)
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact presieve_mem_of_arrow_eq _ _ (h i).symm _ (Presieve.ofArrows.mk i)

/-- A finite family of prescribed covering pullback squares admits a common stage presentation.
The conclusion supplies a stage cover and pullback squares, without asserting that their first
projections cover. In particular no stage base-change or composition axiom is assumed.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram and pullback paragraphs.
(blueprint: lem-weil-pbc-colimit-site-covering-pullback-stage-presentation)

Proof: The equality himage represents the indexed family by the finite stage presieve R₀.
For each f i choose a representing arrow in R₀, including its endpoint equalities. Conversely,
for each arrow of R₀ choose an index whose image is that arrow's image. There are finitely many
choices in both directions by Finite ι and hfinite. Lift the objects, g and these equalities
using surjectivity and eventual equality of the object and arrow colimits. Move everything
above j₀ to a common stage and impose the finitely many equalities. The resulting indexed
presieve equals the transition image of R₀, so is covering by hcover; its cocone image is f.
Form its stage pullbacks along the lifted g. Each covering arrow belongs to this stage presieve,
so hpullback preserves its pullback under every further transition. The limiting-cone argument
of filteredColimit_preservesPullback makes its cocone image a pullback. Uniqueness of pullbacks
gives an isomorphism from each prescribed vertex P' i to the corresponding image pullback,
commuting with both projections. Lift the vertices, these isomorphisms and their inverses,
and enforce both inverse equations and both leg equations at one later stage by eventual
equality. Transport the preserved stage pullbacks along these stage isomorphisms. Their first
projections now have precisely the prescribed cocone images. Mapping the indexed presieve
and transporting its target equality gives the final presieve equality. The transitioned
source family remains covering by hcover. For an empty index, himage forces R₀ to be empty;
lift only g and its endpoints, so all square and leg conditions are vacuous. No covering
property of the first projections is used in this construction. -/
theorem colimit_site_covering_pullback_stage_presentation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j₀ : J) (T₀ : F.obj j₀) (R₀ : Presieve T₀) (hR₀ : R₀ ∈ P j₀ T₀)
    {ι : Type (max u u)} [Finite ι] {S : V.pt} {X : ι → V.pt}
    (e₀ : (V.ι.app j₀).toFunctor.obj T₀ = S) (f : ∀ i, X i ⟶ S)
    (himage : e₀ ▸ R₀.map (V.ι.app j₀).toFunctor = Presieve.ofArrows X f)
    {Y : V.pt} (g : Y ⟶ S) {P' : ι → V.pt}
    (p₁ : ∀ i, P' i ⟶ Y) (p₂ : ∀ i, P' i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    ∃ (j : J) (T : F.obj j) (A : ι → F.obj j) (a : ∀ i, A i ⟶ T)
      (B : F.obj j) (b : B ⟶ T) (D : ι → F.obj j)
      (q₁ : ∀ i, D i ⟶ B) (q₂ : ∀ i, D i ⟶ A i)
      (e : (V.ι.app j).toFunctor.obj B = Y),
      Presieve.ofArrows A a ∈ P j T ∧
      (∀ i, IsPullback (q₁ i) (q₂ i) b (a i)) ∧
      e ▸ (Presieve.ofArrows D q₁).map (V.ι.app j).toFunctor =
        Presieve.ofArrows P' p₁ := by
  classical
  have cocone_arrow_eq
      {K : Type u} [SmallCategory K] (G : K ⥤ Cat.{u, u}) (W : Cocone G)
      {j k : K} (a : j ⟶ k) {X Y : G.obj j} (f : Y ⟶ X) :
      Arrow.mk ((W.ι.app k).toFunctor.map ((G.map a).toFunctor.map f)) =
        Arrow.mk ((W.ι.app j).toFunctor.map f) := by
    exact congrArg (fun U ↦ Arrow.mk (U.toFunctor.map f)) (W.w a)
  have lift_arrow_above_stage
      {K : Type u} [SmallCategory K] [IsFiltered K] (G : K ⥤ Cat.{u, u})
      (W : Cocone G) (hobjects : IsColimit (Cat.objects.mapCocone W))
      (harrows : IsColimit (Cat.arrows.mapCocone W))
      (j : K) (X : G.obj j) {Y : W.pt} (g : Y ⟶ (W.ι.app j).toFunctor.obj X) :
      ∃ (k : K) (a : j ⟶ k) (Z : G.obj k)
        (g' : Z ⟶ (G.map a).toFunctor.obj X),
        Arrow.mk ((W.ι.app k).toFunctor.map g') = Arrow.mk g := by
    obtain ⟨i, b, hb⟩ := Types.jointly_surjective (G ⋙ Cat.arrows) harrows (Arrow.mk g)
    have he : (Cat.objects.mapCocone W).ι.app j X =
        (Cat.objects.mapCocone W).ι.app i b.right :=
      (congrArg Arrow.right hb).symm
    obtain ⟨k, a, c, h⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff (G ⋙ Cat.objects) hobjects).mp he
    change (G.map a).toFunctor.obj X = (G.map c).toFunctor.obj b.right at h
    refine ⟨k, a, (G.map c).toFunctor.obj b.left,
      (G.map c).toFunctor.map b.hom ≫ eqToHom h.symm, ?_⟩
    rw [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
    exact (cocone_arrow_eq G W c b.hom).trans hb
  let Q : Precoverage V.pt := ⟨fun S R ↦
    ∃ (j : J) (T : F.obj j) (R₀ : Presieve T) (e : (V.ι.app j).toFunctor.obj T = S),
      R₀ ∈ P j T ∧ e ▸ R₀.map (V.ι.app j).toFunctor = R⟩
  have hQ : ∀ S R, R ∈ Q S ↔
      ∃ (j : J) (T : F.obj j) (R₀ : Presieve T) (e : (V.ι.app j).toFunctor.obj T = S),
        R₀ ∈ P j T ∧ e ▸ R₀.map (V.ι.app j).toFunctor = R := fun _ _ ↦ Iff.rfl
  have hf : Presieve.ofArrows X f ∈ Q S := ⟨j₀, T₀, R₀, e₀, hR₀, himage⟩
  obtain ⟨j, c, A, a, hA, ha⟩ :=
    colimit_site_covering_families_at_stage J F P hfinite hcover V hobjects harrows Q hQ
      (κ := PUnit.{u + 1}) j₀ (fun _ ↦ T₀) (fun _ ↦ e₀)
      (τ := fun _ ↦ ι) (X := fun _ ↦ X) (fun _ ↦ f) (fun _ ↦ hf)
  let T := (F.map c).toFunctor.obj T₀
  have eT : (V.ι.app j).toFunctor.obj T = S :=
    (congrArg (fun H : F.obj j₀ ⟶ V.pt ↦ H.toFunctor.obj T₀) (V.w c)).trans e₀
  obtain ⟨k, d, B, b, hb⟩ :=
    lift_arrow_above_stage F V hobjects harrows j T (g ≫ eqToHom eT.symm)
  have hb : Arrow.mk ((V.ι.app k).toFunctor.map b) = Arrow.mk g := by
    simpa only [Arrow.arrow_mk_comp_eqToHom] using hb
  let U := (F.map d).toFunctor
  let Ak : ι → F.obj k := fun i ↦ U.obj (A PUnit.unit i)
  let ak : ∀ i, Ak i ⟶ U.obj T := fun i ↦ U.map (a PUnit.unit i)
  have hAk : Presieve.ofArrows Ak ak ∈ P k (U.obj T) := by
    simpa only [Presieve.map_ofArrows] using hcover j k d T _ (hA PUnit.unit)
  have hak (i : ι) : Arrow.mk ((V.ι.app k).toFunctor.map (ak i)) = Arrow.mk (f i) :=
    (cocone_arrow_eq F V d (a PUnit.unit i)).trans (ha PUnit.unit i)
  have eB : (V.ι.app k).toFunctor.obj B = Y := congrArg Arrow.left hb
  have hp (i : ι) : HasPullback (ak i) b :=
    ((P k).hasPullbacks_of_mem b hAk).hasPullback (Presieve.ofArrows.mk i)
  let D : ι → F.obj k := fun i ↦ @pullback _ _ _ _ _ (ak i) b (hp i)
  let q₁ : ∀ i, D i ⟶ B := fun i ↦ have := hp i; pullback.snd (ak i) b
  let q₂ : ∀ i, D i ⟶ Ak i := fun i ↦ have := hp i; pullback.fst (ak i) b
  have hsq (i : ι) : IsPullback (q₁ i) (q₂ i) b (ak i) := by
    have := hp i
    exact (IsPullback.of_hasPullback (ak i) b).flip
  have hpres (i : ι) : PreservesLimit (cospan b (ak i)) (V.ι.app k).toFunctor := by
    have := hp i
    have := filteredColimit_preservesPullback J F V hobjects harrows k (ak i) b
      (fun l t ↦ hpullback k l t _ _ _ _ hAk (ak i) b (Presieve.ofArrows.mk i))
    exact preservesPullback_symmetry _ (ak i) b
  have hex (i : ι) : ∃ E : (V.ι.app k).toFunctor.obj (D i) ≅ P' i,
      E.inv ≫ (V.ι.app k).toFunctor.map (q₁ i) ≫ eqToHom eB = p₁ i := by
    have := hpres i
    exact pullback_comparison _ b (ak i) (q₁ i) (q₂ i) (hsq i)
      (f i) g (p₁ i) (p₂ i) (h i) hb (hak i) eB
  choose E hE using hex
  obtain ⟨l, t, D', s, hs⟩ := filteredColimit_finite_iso_lift J F V hobjects harrows k D P' E
  let W := (F.map t).toFunctor
  let r₁ : ∀ i, D' i ⟶ W.obj B := fun i ↦ (s i).hom ≫ W.map (q₁ i)
  let r₂ : ∀ i, D' i ⟶ W.obj (Ak i) := fun i ↦ (s i).hom ≫ W.map (q₂ i)
  have eB' : (V.ι.app l).toFunctor.obj (W.obj B) = Y :=
    (congrArg (fun H : F.obj k ⟶ V.pt ↦ H.toFunctor.obj B) (V.w t)).trans eB
  refine ⟨l, W.obj (U.obj T), fun i ↦ W.obj (Ak i), fun i ↦ W.map (ak i),
    W.obj B, W.map b, D', r₁, r₂, eB', ?_, ?_, ?_⟩
  · simpa only [Presieve.map_ofArrows] using hcover k l t _ _ hAk
  · intro i
    have := hpullback k l t _ _ _ _ hAk (ak i) b (Presieve.ofArrows.mk i)
    have : PreservesLimit (cospan b (ak i)) W := preservesPullback_symmetry W (ak i) b
    exact ((hsq i).map W).of_iso' (s i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [r₁]) (by simp [r₂]) (by simp) (by simp)
  · rw [Presieve.map_ofArrows]
    apply presieve_eq_of_arrow_eq _ _ _ _ eB'
    intro i
    dsimp [r₁]
    rw [Functor.map_comp]
    have hq := cocone_arrow_eq F V t (q₁ i)
    have hq' : Arrow.mk ((V.ι.app l).toFunctor.map (W.map (q₁ i)) ≫ eqToHom eB') =
        Arrow.mk ((V.ι.app k).toFunctor.map (q₁ i) ≫ eqToHom eB) := by
      simpa only [Arrow.arrow_mk_comp_eqToHom] using hq
    have hh := arrow_comp_eq _ _ _ _ (hs i) hq'
    rw [hE i, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom] at hh
    exact hh

end CategoryTheory
