/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineLift

/-!
# Sheaves on the affine pro-étale site and disjoint open covers

We refine the sheaf criterion `AlgebraicGeometry.Scheme.AffineProEt.isSheaf`: instead of the
full Zariski sheaf condition, it suffices to check the sheaf condition for finite jointly
surjective families of open immersions with pairwise disjoint ranges, together with the sheaf
condition for single surjections.

Conversely, a sheaf `G` with values in any category sends such a disjoint finite open cover
`U i ⟶ Y` to a product decomposition `G(Y) ≅ ∏ᵢ G(U i)`.

## Main statements

* `AlgebraicGeometry.Scheme.AffineProEt.isSheaf_of_isSheafFor_disjoint`: a presheaf of types
  which is a sheaf for disjoint finite open covers and for single surjections is a sheaf.
* `AlgebraicGeometry.Scheme.AffineProEt.isTerminalObjOfIsEmpty`: the value of a sheaf at an
  object with empty underlying scheme is terminal.
* `AlgebraicGeometry.Scheme.AffineProEt.isIso_piLift_map_of_disjoint`: a sheaf turns a disjoint
  open cover into a product.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- If `r ≫ g = s ≫ j`, then `g` maps every point in the image of `r` into the range of `j`. -/
lemma left_base_mem_range_of_comp_eq {P Q W V : S.AffineProEt} {r : P ⟶ Q} {g : Q ⟶ W}
    {s : P ⟶ V} {j : V ⟶ W} (h : r ≫ g = s ≫ j) (z : P.left) :
    g.left.base (r.left.base z) ∈ Set.range j.left.base :=
  ⟨s.left.base z, (congr_arg (fun φ : P ⟶ W ↦ φ.left.base z) h).symm⟩

/-- A morphism in the affine pro-étale site whose underlying morphism of schemes is an open
immersion is a monomorphism. -/
lemma mono_of_isOpenImmersion {U Y : S.AffineProEt} (j : U ⟶ Y) [IsOpenImmersion j.left] :
    Mono j := by
  refine ⟨fun g g' h ↦ MorphismProperty.Over.Hom.ext ?_⟩
  have hl : (g ≫ j).left = (g' ≫ j).left := by rw [h]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left] at hl
  exact (cancel_mono _).mp hl

/-- If two morphisms `ga : Q ⟶ U a` and `gb : Q ⟶ U b` agree after composing with morphisms
`j a`, `j b` with disjoint ranges, then `Q` has empty underlying scheme. -/
lemma isEmpty_of_comp_eq_of_disjoint {Q U U' Y : S.AffineProEt} {j : U ⟶ Y} {j' : U' ⟶ Y}
    (hd : Disjoint (Set.range j.left.base) (Set.range j'.left.base)) {g : Q ⟶ U} {g' : Q ⟶ U'}
    (h : g ≫ j = g' ≫ j') : IsEmpty Q.left :=
  ⟨fun x ↦ Set.disjoint_left.mp hd ⟨g.left.base x, rfl⟩
    ⟨g'.left.base x, (congr_arg (fun φ : Q ⟶ Y ↦ φ.left.base x) h).symm⟩⟩

/-- The sheaf condition for a finite, jointly surjective family in the affine pro-étale site
follows from the sheaf condition for finite jointly surjective families of open immersions with
pairwise disjoint ranges together with the sheaf condition for single surjections. -/
lemma isSheafFor_ofArrows_of_finite_of_disjoint {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : ∀ {Y : S.AffineProEt} {ι : Type u} [Finite ι] (U : ι → S.AffineProEt)
      (j : ∀ i, U i ⟶ Y), (∀ i, IsOpenImmersion (j i).left) →
      (∀ y : Y.left, ∃ i, y ∈ Set.range (j i).left.base) →
      (∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base)) →
      (Presieve.ofArrows U j).IsSheafFor F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.left],
      (Presieve.singleton f).IsSheafFor F)
    {X : S.AffineProEt} {ι : Type u} [Finite ι] (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    (Presieve.ofArrows V f).IsSheafFor F := by
  obtain ⟨W, q, j, hq, hcomp, hoi, hcov, hdisj⟩ :=
    exists_surjective_factorization_disjoint V f hsurj
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- Step 1: glue the `x i` over the disjoint cover `{j i}` of `W` to obtain `z: F(W)`.
  have hW : (Presieve.ofArrows V j).IsSheafFor F := h₁ V j hoi hcov hdisj
  rw [Presieve.isSheafFor_arrows_iff] at hW
  obtain ⟨z, hz, hzuniq⟩ := hW x (fun a b Q ga gb hab ↦ hx a b Q ga gb (by
    rw [← hcomp a, ← hcomp b, ← Category.assoc, hab, Category.assoc]))
  -- Step 2: the singleton family `q ↦ z` is compatible. This is checked on a disjoint cover
  -- by double pullbacks, using compatibility of `x` over `X`.
  have hsep : ∀ {Q : S.AffineProEt} (g₁ g₂ : Q ⟶ W), g₁ ≫ q = g₂ ≫ q →
      F.map g₁.op z = F.map g₂.op z := by
    intro Q g₁ g₂ hg
    have hAoi : ∀ a : ι, IsOpenImmersion (pullback.fst g₁ (j a)).left := fun a ↦
      MorphismProperty.of_isPullback
        (isPullback_left (IsPullback.of_hasPullback g₁ (j a)).flip) (hoi a)
    have hBoi : ∀ a b : ι,
        IsOpenImmersion (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b)).left := fun a b ↦
      MorphismProperty.of_isPullback
        (isPullback_left (IsPullback.of_hasPullback (pullback.fst g₁ (j a) ≫ g₂) (j b)).flip)
        (hoi b)
    let r : ∀ p : ι × ι, pullback (pullback.fst g₁ (j p.1) ≫ g₂) (j p.2) ⟶ Q := fun p ↦
      pullback.fst (pullback.fst g₁ (j p.1) ≫ g₂) (j p.2) ≫ pullback.fst g₁ (j p.1)
    have hroi : ∀ p : ι × ι, IsOpenImmersion (r p).left := fun p ↦ by
      have := hAoi p.1
      have := hBoi p.1 p.2
      rw [MorphismProperty.Comma.comp_left]
      infer_instance
    have hrcov : ∀ zq : Q.left, ∃ p : ι × ι, zq ∈ Set.range ((r p).left.base) := by
      intro zq
      obtain ⟨a, v₁, hv₁⟩ := hcov (g₁.left.base zq)
      obtain ⟨pA, hpA₁, hpA₂⟩ := exists_left_base_preimage
        (IsPullback.of_hasPullback g₁ (j a)) zq v₁ hv₁.symm
      obtain ⟨b, v₂, hv₂⟩ := hcov (g₂.left.base ((pullback.fst g₁ (j a)).left.base pA))
      obtain ⟨pB, hpB₁, hpB₂⟩ := exists_left_base_preimage
        (IsPullback.of_hasPullback (pullback.fst g₁ (j a) ≫ g₂) (j b)) pA v₂ (by
          calc (pullback.fst g₁ (j a) ≫ g₂).left.base pA
              = g₂.left.base ((pullback.fst g₁ (j a)).left.base pA) := rfl
            _ = (j b).left.base v₂ := hv₂.symm)
      refine ⟨⟨a, b⟩, pB, ?_⟩
      calc (r (a, b)).left.base pB
          = (pullback.fst g₁ (j a)).left.base
              ((pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b)).left.base pB) := rfl
        _ = (pullback.fst g₁ (j a)).left.base pA := by rw [hpB₁]
        _ = zq := hpA₁
    have e₁ (a b : ι) : r (a, b) ≫ g₁ =
        (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.snd g₁ (j a)) ≫ j a := by
      simp only [r]
      rw [Category.assoc, pullback.condition (f := g₁) (g := j a), Category.assoc]
    have e₂ (a b : ι) : r (a, b) ≫ g₂ =
        pullback.snd (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ j b := by
      simp only [r]
      rw [Category.assoc, pullback.condition (f := pullback.fst g₁ (j a) ≫ g₂) (g := j b)]
    have hrdisj : ∀ p p' : ι × ι, p ≠ p' →
        Disjoint (Set.range (r p).left.base) (Set.range (r p').left.base) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hne
      rw [Set.disjoint_left]
      rintro _ ⟨z₁, rfl⟩ ⟨z₂, hz₂⟩
      refine hne ?_
      have ha : a = a' := by
        by_contra hne'
        refine Set.disjoint_left.mp (hdisj a a' hne')
          (left_base_mem_range_of_comp_eq (e₁ a b) z₁) ?_
        rw [← hz₂]
        exact left_base_mem_range_of_comp_eq (e₁ a' b') z₂
      have hb : b = b' := by
        by_contra hne'
        refine Set.disjoint_left.mp (hdisj b b' hne')
          (left_base_mem_range_of_comp_eq (e₂ a b) z₁) ?_
        rw [← hz₂]
        exact left_base_mem_range_of_comp_eq (e₂ a' b') z₂
      rw [ha, hb]
    have hsepZ : (Presieve.ofArrows _ r).IsSeparatedFor F :=
      (h₁ _ r hroi hrcov hrdisj).isSeparatedFor
    refine hsepZ.ext fun Q' g' hg' ↦ ?_
    obtain ⟨p⟩ := hg'
    obtain ⟨a, b⟩ := p
    have key : (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.snd g₁ (j a)) ≫ f a =
        pullback.snd (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ f b := by
      rw [← hcomp a, ← hcomp b, ← Category.assoc, ← Category.assoc, ← e₁, ← e₂,
        Category.assoc, Category.assoc, hg]
      simp only [r, Category.assoc]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      e₁, e₂]
    simp only [op_comp, Functor.map_comp_apply, hz]
    simpa using hx a b _ _ _ key
  -- Step 3: amalgamate `z` along the single surjection `q` using `h₂`.
  have : Surjective q.left := hq
  have hqsheaf := h₂ q
  rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_arrows_iff] at hqsheaf
  obtain ⟨t, ht, htuniq⟩ := hqsheaf (fun _ ↦ z) fun _ _ Q g₁ g₂ hgq ↦ hsep g₁ g₂ hgq
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [← hcomp i, op_comp, Functor.map_comp_apply, ht PUnit.unit, hz i]
  · refine htuniq t' fun _ ↦ ?_
    refine hzuniq (F.map q.op t') fun i ↦ ?_
    rw [← Functor.map_comp_apply, ← op_comp, hcomp i]
    exact ht' i

variable (S) in
/-- To show a presheaf of types is a sheaf on the affine pro-étale site, it suffices to show it
satisfies the sheaf condition for finite jointly surjective families of open immersions with
pairwise disjoint ranges and for single surjective morphisms. -/
lemma isSheaf_of_isSheafFor_disjoint {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : ∀ {Y : S.AffineProEt} {ι : Type u} [Finite ι] (U : ι → S.AffineProEt)
      (j : ∀ i, U i ⟶ Y), (∀ i, IsOpenImmersion (j i).left) →
      (∀ y : Y.left, ∃ i, y ∈ Set.range (j i).left.base) →
      (∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base)) →
      (Presieve.ofArrows U j).IsSheafFor F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X T hT
  obtain ⟨ι, _, V, f, hmem, hsurj⟩ := exists_finite_jointly_surjective_of_mem_topology hT
  refine Presieve.IsSheafFor.of_le (R := Presieve.ofArrows V f) ?_
    (isSheafFor_ofArrows_of_finite_of_disjoint h₁ h₂ V f hsurj) ?_
  · rintro Y g ⟨i⟩
    exact hmem i
  · intro Y g hg
    have hsurj' : ∀ y : Y.left, ∃ i, y ∈ Set.range ((pullback.snd (f i) g).left.base) := by
      intro y
      obtain ⟨i, v, hv⟩ := hsurj (g.left.base y)
      obtain ⟨p, -, hp⟩ := exists_left_base_preimage (IsPullback.of_hasPullback (f i) g) v y hv
      exact ⟨i, p, hp⟩
    refine ((isSheafFor_ofArrows_of_finite_of_disjoint h₁ h₂ _ _ hsurj').isSeparatedFor).of_le ?_
    rintro Q' h' ⟨i⟩
    exact ⟨V i, pullback.fst (f i) g, f i, ⟨i⟩, pullback.condition⟩

variable {A : Type*} [Category* A]

/-- The value of a sheaf on the affine pro-étale site at an object with empty underlying scheme
is a terminal object: the empty family is a covering. -/
noncomputable def isTerminalObjOfIsEmpty (G : Sheaf (topology S) A) {Z : S.AffineProEt}
    [IsEmpty Z.left] : IsTerminal (G.obj.obj (op Z)) := by
  refine IsTerminal.ofUniqueHom (fun a ↦ ?_) fun a m ↦ ?_
  · let V : PEmpty.{u + 2} → S.AffineProEt := PEmpty.elim
    let g : ∀ i, V i ⟶ Z := fun i ↦ i.elim
    have hsh : (Presieve.ofArrows V g).IsSheafFor (G.obj ⋙ coyoneda.obj (op a)) :=
      (Presieve.isSheafFor_iff_generate _).mpr (G.property a _
        (generate_mem_topology g (fun i ↦ i.elim) fun x ↦ isEmptyElim x))
    rw [Presieve.isSheafFor_arrows_iff] at hsh
    exact (hsh (fun i ↦ i.elim) fun i ↦ i.elim).choose
  · have := subsingleton_of_isEmpty ((isSheaf_iff_isSheaf_of_type _ _).mpr (G.property a))
      (inferInstance : IsEmpty Z.left)
    exact @Subsingleton.elim _ this _ _

/-- A sheaf on the affine pro-étale site turns a jointly surjective family of open immersions
`j i : U i ⟶ Y` with pairwise disjoint ranges into a product: the map
`G(Y) ⟶ ∏ᵢ G(U i)` is an isomorphism. -/
lemma isIso_piLift_map_of_disjoint (G : Sheaf (topology S) A) {Y : S.AffineProEt} {ι : Type*}
    (U : ι → S.AffineProEt) (j : ∀ i, U i ⟶ Y) (hoi : ∀ i, IsOpenImmersion (j i).left)
    (hsurj : ∀ y : Y.left, ∃ i, y ∈ Set.range (j i).left.base)
    (hdisj : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base))
    [HasProduct fun i ↦ G.obj.obj (op (U i))] :
    IsIso (Pi.lift fun i ↦ G.obj.map (j i).op :
      G.obj.obj (op Y) ⟶ ∏ᶜ fun i ↦ G.obj.obj (op (U i))) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro a
  have hsh : (Presieve.ofArrows U j).IsSheafFor (G.obj ⋙ coyoneda.obj (op a)) :=
    (Presieve.isSheafFor_iff_generate _).mpr (G.property a _ (generate_mem_topology j hoi hsurj))
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hcompat (x : ∀ i, a ⟶ G.obj.obj (op (U i))) :
      ∀ i k (Q : S.AffineProEt) (gi : Q ⟶ U i) (gk : Q ⟶ U k), gi ≫ j i = gk ≫ j k →
        x i ≫ G.obj.map gi.op = x k ≫ G.obj.map gk.op := by
    intro i k Q gi gk h
    by_cases hik : i = k
    · subst hik
      have := hoi i
      have := mono_of_isOpenImmersion (j i)
      obtain rfl := (cancel_mono _).mp h
      rfl
    · have := isEmpty_of_comp_eq_of_disjoint (hdisj i k hik) h
      exact (isTerminalObjOfIsEmpty G).hom_ext _ _
  refine ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := hsh (fun i ↦ y ≫ G.obj.map (j i).op) (hcompat _)
    have hx : x = t := ht x fun i ↦ by
      simpa using congr_arg (· ≫ Pi.π _ i) hxy
    have hy : y = t := ht y fun i ↦ rfl
    rw [hx, hy]
  · obtain ⟨t, ht, -⟩ := hsh (fun i ↦ φ ≫ Pi.π _ i) (hcompat _)
    refine ⟨t, Pi.hom_ext _ _ fun i ↦ ?_⟩
    simpa using ht i

end AlgebraicGeometry.Scheme.AffineProEt
