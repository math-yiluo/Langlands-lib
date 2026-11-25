/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Eventual equality of maps from larger affine étale limits

Source: Stacks Project, Tags 01ZC and 099S.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

/-- Sections of an affine étale scheme over a field form a finite set. -/
private theorem finite_etale_sections {Ω : Type u} [Field Ω]
    {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ Spec (.of Ω)) [Etale q] :
    Finite {g : Spec (.of Ω) ⟶ Y // g ≫ q = 𝟙 _} := by
  have : Finite Y := by
    have h := q.finite_preimage_singleton (default : Spec (.of Ω))
    apply Set.finite_univ_iff.mp
    convert h using 1
    ext y
    simp [Subsingleton.elim (q y) default]
  apply Finite.of_injective (fun g ↦ g.val (default : Spec (.of Ω)))
  intro g h heval
  have hh : IsOpenImmersion (h.val ≫ q) := by rw [h.property]; infer_instance
  have : IsOpenImmersion h.val := FormallyUnramified.isOpenImmersion_of_comp q h.val
  have hr : Set.range g.val ⊆ Set.range h.val := by
    rintro _ ⟨x, rfl⟩
    exact ⟨default, by rw [Subsingleton.elim x default]; exact heval.symm⟩
  let l := IsOpenImmersion.lift h.val g.val hr
  have hl : l ≫ h.val = g.val := IsOpenImmersion.lift_fac _ _ _
  have hid : l = 𝟙 _ := by
    calc
      l = l ≫ (h.val ≫ q) := by rw [h.property]; simp
      _ = g.val ≫ q := by rw [← Category.assoc, hl]
      _ = 𝟙 _ := g.property
  apply Subtype.ext
  simpa [hid] using hl.symm

/-- Geometric lifts through an affine étale morphism form a finite set. -/
private theorem finite_etale_lifts {S : Scheme.{u}} [IsAffine S]
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (Y : Over S) [IsAffine Y.left] [Etale Y.hom] :
    Finite (Over.mk s ⟶ Y) := by
  let P := pullback Y.hom s
  let q : P ⟶ Spec (.of Ω) := pullback.snd Y.hom s
  have : IsAffine P := inferInstance
  have : Etale q := inferInstanceAs (Etale (pullback.snd Y.hom s))
  have := finite_etale_sections q
  let f : (Over.mk s ⟶ Y) → {g : Spec (.of Ω) ⟶ P // g ≫ q = 𝟙 _} :=
    fun a ↦ ⟨pullback.lift a.left (𝟙 _) (by simp), by simp [q]⟩
  apply Finite.of_injective f
  intro a b hab
  apply Over.OverMorphism.ext
  have h := congrArg (fun g ↦ g.val ≫ pullback.fst Y.hom s) hab
  simpa [f] using h

/-- Compactness supplies a geometric cone for a large nonempty affine étale system. -/
private theorem affineEtale_nonempty_cone {S : Scheme.{u}} [IsAffine S]
    {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Over S) (haff : ∀ j, IsAffine (D.obj j).left)
    (het : ∀ j, Etale (D.obj j).hom) (hne : ∀ j, Nonempty (D.obj j).left) :
    ∃ c : Cone D, Nonempty c.pt.left := by
  have (j : J) : IsAffine (D.obj j).left := haff j
  have (j : J) : Etale (D.obj j).hom := het j
  let R (j : J) : Set (WithConstructibleTopology S) :=
    WithTopology.ofTopology ⁻¹' Set.range (D.obj j).hom
  have hRc (j : J) : IsClosed (R j) := by
    rw [WithConstructibleTopology.isClosed_iff]
    change IsClosed[constructibleTopology S] (Set.range (D.obj j).hom)
    have hr : IsCompact (Set.range (D.obj j).hom) := by
      simpa only [Set.image_univ] using isCompact_univ.image (D.obj j).hom.continuous
    exact hr.isClosed_constructibleTopology_of_isOpen (D.obj j).hom.isOpenMap.isOpen_range
  have hRn (j : J) : (R j).Nonempty := by
    obtain ⟨x⟩ := hne j
    exact ⟨WithTopology.toTopology _ ((D.obj j).hom x), x, rfl⟩
  have hRd : Directed (· ⊇ ·) R := by
    intro i j
    refine ⟨IsCofiltered.min i j, ?_, ?_⟩
    · rintro x ⟨y, hy⟩
      refine ⟨(D.map (IsCofiltered.minToLeft i j)).left y, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hy
    · rintro x ⟨y, hy⟩
      refine ⟨(D.map (IsCofiltered.minToRight i j)).left y, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hy
  have : Nonempty J := IsCofiltered.nonempty
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    R hRd hRn (fun j ↦ (hRc j).isCompact) hRc
  let s := S.algClosurePoint (WithTopology.ofTopology x)
  let F := D ⋙ coyoneda.obj (op (Over.mk s))
  have (j : J) : Finite (F.obj j) := finite_etale_lifts s (D.obj j)
  have (j : J) : Nonempty (F.obj j) := by
    obtain ⟨y, hy⟩ := Set.mem_iInter.mp hx j
    obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (D.obj j).hom s y
      (by simpa [s, Scheme.algClosurePoint_base] using hy)
    exact ⟨Over.homMk l hl⟩
  obtain ⟨a, ha⟩ := nonempty_sections_of_finite_cofiltered_system F
  refine ⟨{ pt := Over.mk s, π := { app := a, naturality := ?_ } }, ?_⟩
  · intro i j f
    simpa [F] using (ha f).symm
  · change Nonempty (Spec (.of (AlgebraicClosure (S.residueField
      (WithTopology.ofTopology x)))))
    exact ⟨default⟩

/-- The complement of the agreement locus for maps to an affine étale target. -/
private theorem etale_equality_complement {S T Z : Scheme.{u}} [IsAffine Z]
    (p : Z ⟶ S) [Etale p] (a b : T ⟶ Z) (h : a ≫ p = b ≫ p) :
    ∃ U : T.Opens, IsClosed (U : Set T) ∧
      ∀ (W : Scheme.{u}) (f : W ⟶ T),
        f ≫ a = f ≫ b ↔ ∀ x : W, f x ∉ U := by
  let d := pullback.diagonal p
  let q : T ⟶ pullback p p := pullback.lift a b h
  let E := pullback d q
  let e : E ⟶ T := pullback.snd d q
  have : IsOpenImmersion e := inferInstanceAs (IsOpenImmersion (pullback.snd d q))
  have : IsClosedImmersion e := inferInstanceAs (IsClosedImmersion (pullback.snd d q))
  have he : e ≫ a = e ≫ b := by
    have H := pullback.condition (f := d) (g := q)
    have H₁ := congrArg (fun k ↦ k ≫ pullback.fst p p) H
    have H₂ := congrArg (fun k ↦ k ≫ pullback.snd p p) H
    calc
      e ≫ a = pullback.fst d q := by simpa [e, d, q, Category.assoc] using H₁.symm
      _ = e ≫ b := by simpa [e, d, q, Category.assoc] using H₂
  let U : T.Opens := ⟨(Set.range e)ᶜ, e.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  refine ⟨U, e.isOpenEmbedding.isOpen_range.isClosed_compl, ?_⟩
  intro W f
  constructor
  · intro hf x
    let g : W ⟶ E := pullback.lift (f ≫ a) f (by
      apply pullback.hom_ext <;> simp [d, q, Category.assoc, hf])
    have hg : g ≫ e = f := pullback.lift_snd _ _ _
    change f x ∉ (Set.range e)ᶜ
    exact fun hn ↦ hn ⟨g x, by rw [← Scheme.Hom.comp_apply, hg]⟩
  · intro hf
    have hr : Set.range f ⊆ Set.range e := by
      rintro _ ⟨x, rfl⟩
      exact not_not.mp (hf x)
    let g := IsOpenImmersion.lift e f hr
    have hg : g ≫ e = f := IsOpenImmersion.lift_fac _ _ _
    rw [← hg, Category.assoc, Category.assoc, he]

/-- Equality of two maps from one affine étale stage to an affine étale target
is witnessed after a refinement of that stage, for the larger index universe.

Source: Stacks Project, limits.tex, Proposition 32.6.1 (Tag 01ZC), injectivity
in (1) implies (3); compare Mathlib's
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.
(auxiliary; not a blueprint node).

Proof: The relative diagonal of the affine étale target is open and closed.
Its pullback along the pair of stage maps is their agreement locus. Its
complement U is closed and open in the affine stage, hence affine. Suppose
no refinement equalises the maps. Pulling U back along all stages over i gives
a cofiltered diagram of nonempty affine schemes étale over U.

The images of these schemes in U are nonempty compact opens, hence closed in
the compact constructible topology. Cofilteredness gives a point in all images.
Over an algebraic closure of its residue field, the sets of lifts to the stages
are finite and nonempty: étale geometric fibres are finite, and sections into an
unramified scheme are determined by their image point. Mathlib's finite
cofiltered-system theorem, which permits independent index and value universes,
gives compatible lifts. They form a cone with nonempty vertex Spec Ω. Initiality
of the category of stages over i and the given limit produce a map Spec Ω → c.
Its image at stage i lies in U, contradicting equality of the two maps on c.
Thus some refinement equalises the underlying scheme maps, hence the maps in
X.ProEt. No size change of a scheme or small-index limit theorem is used. -/
theorem affineEtale_largeLimit_eventualEquality {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ X.ProEt) (haff : ∀ i, IsAffine (D.obj i).left)
    (het : ∀ i, Etale (D.obj i).hom) (c : Cone D)
    (hc : IsLimit ((Scheme.ProEt.forget X).mapCone c))
    (V : X.ProEt) [IsAffine V.left] [Etale V.hom]
    (i : I) (a b : D.obj i ⟶ V)
    (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (k : I) (f : k ⟶ i), D.map f ≫ a = D.map f ≫ b := by
  classical
  let L := Scheme.ProEt.forget X ⋙ Over.forget X
  let D' := D ⋙ L
  let c' := L.mapCone c
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget X) hc
  have (j : I) : IsAffine (D'.obj j) := haff j
  have (j : I) : Etale (D.obj j).hom := het j
  obtain ⟨U, hUc, hU⟩ := etale_equality_complement (Z := V.left) V.hom a.left b.left
    (by rw [MorphismProperty.Over.w, MorphismProperty.Over.w])
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by simpa only [Scheme.Opens.range_ι] using hUc)
  have : IsAffine U.toScheme := isAffine_of_isAffineHom U.ι
  by_contra! h
  let E := Over.post D' ⋙ Over.pullback U.ι
  have hEa (j : Over i) : IsAffine (E.obj j).left := by
    change IsAffine (pullback (D'.map j.hom) U.ι)
    infer_instance
  have hEe (j : Over i) : Etale (E.obj j).hom := by
    have hf : Etale (D'.map j.hom) := by
      change Etale (D.map j.hom).left
      have : Etale ((D.map j.hom).left ≫ (D.obj i).hom) := by
        rw [MorphismProperty.Over.w]
        exact het j.left
      exact Etale.of_comp (D.map j.hom).left (D.obj i).hom
    exact inferInstanceAs (Etale (pullback.snd (D'.map j.hom) U.ι))
  have hEn (j : Over i) : Nonempty (E.obj j).left := by
    have hn : ¬ ∀ x, D'.map j.hom x ∉ U := by
      intro hx
      apply h j.left j.hom
      apply MorphismProperty.Over.Hom.ext
      exact (hU _ (D'.map j.hom)).mpr hx
    push Not at hn
    obtain ⟨x, hx⟩ := hn
    have hr : x ∈ Set.range (pullback.fst (D'.map j.hom) U.ι) := by
      rw [IsOpenImmersion.range_pullbackFst]
      simpa using hx
    obtain ⟨y, _⟩ := hr
    exact ⟨y⟩
  obtain ⟨s, hs⟩ := affineEtale_nonempty_cone E hEa hEe hEn
  let t : Cone (Over.forget i ⋙ D') :=
    { pt := s.pt.left
      π :=
        { app j := (s.π.app j).left ≫ pullback.fst (D'.map j.hom) U.ι
          naturality {j k} f := by
            dsimp
            simp only [Category.id_comp, Category.assoc]
            have H := congrArg (fun g ↦ g.left ≫ pullback.fst (D'.map k.hom) U.ι)
              (s.w f)
            simpa [E, Over.pullback, Over.post, Category.assoc] using H.symm } }
  have hci : IsLimit (c'.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c').symm hc'
  let l := hci.lift t
  let j₀ : Over i := Over.mk (𝟙 i)
  have hl : l ≫ (c.π.app i).left =
      (s.π.app j₀).left ≫ pullback.fst (D'.map j₀.hom) U.ι := hci.fac t j₀
  have heq : (l ≫ (c.π.app i).left) ≫ a.left =
      (l ≫ (c.π.app i).left) ≫ b.left := by
    have hh := congrArg (fun g ↦ l ≫ g.left) hab
    change l ≫ ((c.π.app i).left ≫ a.left) =
      l ≫ ((c.π.app i).left ≫ b.left) at hh
    simpa only [Category.assoc] using hh
  obtain ⟨x⟩ := hs
  apply (hU _ (l ≫ (c.π.app i).left)).mp heq x
  rw [hl]
  have H : (s.π.app j₀).left ≫ pullback.fst (D'.map j₀.hom) U.ι =
      s.pt.hom ≫ U.ι := by
    have hw := congrArg (fun g ↦ (s.π.app j₀).left ≫ g)
      (pullback.condition (f := D'.map j₀.hom) (g := U.ι))
    have hw' : (s.π.app j₀).left ≫ pullback.snd (D'.map j₀.hom) U.ι =
        s.pt.hom := (s.π.app j₀).w
    have hw₀ : (s.π.app j₀).left ≫ pullback.fst (D'.map j₀.hom) U.ι =
        (s.π.app j₀).left ≫ pullback.snd (D'.map j₀.hom) U.ι ≫ U.ι := by
      simpa [j₀, Category.assoc] using hw
    exact hw₀.trans (by rw [← Category.assoc, hw'])
  rw [H]
  exact (s.pt.hom x).property

end AlgebraicGeometry.ProEtale
