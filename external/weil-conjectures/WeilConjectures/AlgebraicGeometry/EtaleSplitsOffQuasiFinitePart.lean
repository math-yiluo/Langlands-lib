/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Étale splitting of the quasi-finite part

Source: Stacks Project, More on Morphisms, Lemma 37.41.6, Tag 02LP
(blueprint: lem-weil-pbc-etale-splits-off-quasi-finite-part).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The union of two disjoint finite open pieces is finite over the base.
This is the coproduct argument in Stacks 02LP, using Mathlib scheme coproducts. -/
private theorem isFinite_sup_of_disjoint
    {Y T : Scheme.{v}} (g : Y ⟶ T) (A B : Y.Opens)
    (hab : Disjoint A B) [IsFinite (A.ι ≫ g)] [IsFinite (B.ι ≫ g)] :
    IsFinite ((A ⊔ B).ι ≫ g) := by
  let a := Y.homOfLE (show A ≤ A ⊔ B from le_sup_left)
  let b := Y.homOfLE (show B ≤ A ⊔ B from le_sup_right)
  have hc : IsCompl a.opensRange b.opensRange := by
    simp only [a, b, Scheme.opensRange_homOfLE]
    constructor
    · rw [disjoint_iff] at hab ⊢
      rw [← Scheme.Hom.preimage_inf, hab]
      rfl
    · rw [codisjoint_iff, ← Scheme.Hom.preimage_sup]
      simp
  have hi : IsIso (coprod.desc a b) :=
    (coprodIsCoprod A.toScheme B.toScheme).nonempty_isColimit_iff_isIso_desc.mp
      (nonempty_isColimit_binaryCofanMk_of_isCompl a b hc)
  have he : coprod.desc a b ≫ (A ⊔ B).ι ≫ g = coprod.desc (A.ι ≫ g) (B.ι ≫ g) := by
    apply coprod.hom_ext <;> simp [a, b]
  have : IsFinite (coprod.desc a b ≫ (A ⊔ B).ι ≫ g) := by
    rw [he]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (coprod.desc a b) _).mp this

set_option backward.isDefEq.respectTransparency false in
/-- A finite disjoint family of finite open pieces has finite union over the base.
Induct on the family, using the empty finite scheme and the binary coproduct argument
in Stacks 02LP. -/
private theorem isFinite_iSup_of_pairwiseDisjoint
    {Y T : Scheme.{v}} (g : Y ⟶ T) (n : ℕ) (V : Fin n → Y.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hfin : ∀ i, IsFinite ((V i).ι ≫ g)) :
    IsFinite ((⨆ i, V i).ι ≫ g) := by
  induction n with
  | zero =>
    rw [iSup_of_empty V]
    have : IsEmpty (⊥ : Y.Opens).toScheme :=
      inferInstanceAs (IsEmpty (∅ : Set Y))
    infer_instance
  | succ n ih =>
    have heq : (⨆ i, V i) = V 0 ⊔ ⨆ i : Fin n, V i.succ := by
      apply le_antisymm
      · apply iSup_le
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact (le_iSup (fun j : Fin n => V j.succ) j).trans le_sup_right
      · exact sup_le (le_iSup V 0) (iSup_le fun i => le_iSup V i.succ)
    rw [heq]
    have := hfin 0
    have : IsFinite ((⨆ i : Fin n, V i.succ).ι ≫ g) :=
      ih (fun i => V i.succ)
        (fun i j hij => hdisj _ _ (fun h => hij (Fin.succ_injective n h)))
        (fun i => hfin i.succ)
    apply isFinite_sup_of_disjoint
    exact disjoint_iSup_iff.mpr fun i => hdisj 0 i.succ (Fin.succ_ne_zero i).symm

set_option backward.isDefEq.respectTransparency false in
/-- The complementary fibre embeds openly into the original fibre in an elementary
neighbourhood. As used in Stacks 02LP, paste the fibre pullbacks to base change the open
immersion, then compose with the fibre isomorphism induced by the residue-field isomorphism. -/
private theorem exists_openImmersion_fiber_of_elementary
    {X S U : Scheme.{v}} (f : X ⟶ S) (φ : U ⟶ S) (u : U)
    [IsIso (φ.residueFieldMap u)] (W : (pullback φ f).Opens) :
    ∃ j : (W.ι ≫ pullback.fst φ f).fiber u ⟶ f.fiber (φ u),
      IsOpenImmersion j ∧
      j ≫ f.fiberι (φ u) =
        (W.ι ≫ pullback.fst φ f).fiberι u ≫ W.ι ≫ pullback.snd φ f := by
  let q := pullback.fst φ f
  let p := pullback.snd φ f
  let a := U.fromSpecResidueField u
  let b := S.fromSpecResidueField (φ u)
  let k := Spec.map (φ.residueFieldMap u)
  let h : q.fiber u ⟶ f.fiber (φ u) :=
    pullback.map q a f b p k φ pullback.condition (by simp [k, a, b])
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback φ f).flip u
  have : IsIso h := hpb.isIso_fst_of_isIso
  let l : (W.ι ≫ q).fiber u ⟶ q.fiber u :=
    pullback.lift ((W.ι ≫ q).fiberι u ≫ W.ι)
      ((W.ι ≫ q).fiberToSpecResidueField u) (by simp [Category.assoc, Scheme.Hom.fiber_fac])
  have hlpb : IsPullback l ((W.ι ≫ q).fiberι u) (q.fiberι u) W.ι := by
    apply IsPullback.of_right (t := (IsPullback.of_hasPullback q a).flip)
    · simpa [l, a, Scheme.Hom.fiberι, Scheme.Hom.fiberToSpecResidueField] using
        (IsPullback.of_hasPullback (W.ι ≫ q) a).flip
    · simp [l, a, Scheme.Hom.fiberι]
  have : IsOpenImmersion l :=
    MorphismProperty.of_isPullback hlpb.flip (inferInstanceAs (IsOpenImmersion W.ι))
  refine ⟨l ≫ h, inferInstance, ?_⟩
  simp [l, h, a, b, p, q, Scheme.Hom.fiberι, Category.assoc]

/-- Stacks Project, Tag 02LP
(blueprint: lem-weil-pbc-etale-splits-off-quasi-finite-part).
A separated locally finite type morphism whose fibre has finitely many isolated points
admits an elementary étale neighbourhood on which a finite clopen part splits off and the
remaining fibre has no isolated points. If the original fibre is finite, the remaining
fibre is empty.

Proof outline:
1. List all isolated points of `f.fiber s`, and their images in `X`
   (def-pc-scheme-fibre).
2. Apply lem-weil-pbc-etale-splits-off-isolated-points-technical (Stacks 02LN) to obtain
   an elementary étale neighbourhood and disjoint finite clopen pieces around those points,
   with a complementary open `W` whose fibre avoids them.
3. Take `V` to be the union of those pieces. It is finite over `U` by
   lem-weil-pbc-finite-coproduct and def-weil-finite-integral-morphism; the empty union is
   the empty finite scheme.
4. Identify the fibre of the base change at `u` with `f.fiber s`, using
   lem-weil-pbc-fibre-of-base-change, def-pc-fibre-product and def-weil-affine-spectrum:
   the induced residue-field map is an isomorphism.
5. The fibre of `W` maps openly into the original fibre: pullback pasting exhibits
   the first map as a base change of `W.ι`, and step 4 supplies the fibre isomorphism.
   The avoidance clause excludes every isolated point from its image.
6. An isolated point of this open subscheme would be isolated in the whole fibre,
   contradicting step 5.
7. If the original set-theoretic fibre is finite, `f.fiberHomeo s` makes the scheme
   fibre finite. Mathlib supplies a Jacobson space instance for a locally finite type
   fibre, using lem-weil-pbc-lft-base-change. Its finite Jacobson space discreteness
   instance makes every point isolated (Stacks 02NG).
8. Step 5 excludes every point of `W`'s fibre in this case; hence it is empty.
-/
theorem exists_etale_splits_off_quasiFinitePart
    {X S : Scheme.{v}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] (s : S)
    (hfinite : Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}) :
    ∃ (U : Scheme.{v}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = s ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (W V : (pullback φ f).Opens),
        IsCompl W V ∧ IsFinite (V.ι ≫ pullback.fst φ f) ∧
        (∀ w : (W.ι ≫ pullback.fst φ f).fiber u,
          ¬ IsOpen ({w} : Set ((W.ι ≫ pullback.fst φ f).fiber u))) ∧
        ((f ⁻¹' ({s} : Set S)).Finite → IsEmpty ((W.ι ≫ pullback.fst φ f).fiber u)) := by
  classical
  -- Enumerate the isolated fibre points, including the empty family.
  let A := {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}
  let := hfinite.fintype
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let ξ : Fin n → f.fiber s := fun i => (e i).val
  let x : Fin n → X := fun i => f.fiberι s (ξ i)
  have hx : Function.Injective x :=
    (f.fiberι s).isEmbedding.injective.comp (Subtype.val_injective.comp e.injective)
  have hover : ∀ i, f (x i) = s := fun i => (f.fiberHomeo s (ξ i)).property
  have hiso : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i)))) := by
    intro i
    have hi : IsOpen ({ξ i} : Set (f.fiber s)) := (e i).property
    have heq : ∀ (y : X) (hy : f y = s) (z : f.fiber s),
        f.fiberι s z = y →
        IsOpen ({z} : Set (f.fiber s)) →
        IsOpen ({f.asFiber y} : Set (f.fiber (f y))) := by
      intro y hy z hz hopen
      subst s
      have hz' : z = f.asFiber y := (f.fiberι (f y)).isEmbedding.injective (by simpa)
      simpa [hz'] using hopen
    exact heq (x i) (hover i) (ξ i) rfl hi
  obtain ⟨U, φ, u, hφ, hu, hres, W, V, hWV, hVV, hcover, hfin, _, havoid⟩ :=
    exists_etale_splits_off_isolated_points f s n x hx hover hiso
  -- Compare the complementary fibre with an open subscheme of the original fibre.
  have := hres
  subst s
  obtain ⟨j, hj, hcomm⟩ := exists_openImmersion_fiber_of_elementary f φ u W
  have := hj
  have hnot : ∀ w : (W.ι ≫ pullback.fst φ f).fiber u,
      ¬ IsOpen ({j w} : Set (f.fiber (φ u))) := by
    intro w hopen
    let i := e.symm ⟨j w, hopen⟩
    have he : ξ i = j w := congrArg Subtype.val (e.apply_symm_apply ⟨j w, hopen⟩)
    have hw := (W.ι ≫ pullback.fst φ f).fiberHomeo u w |>.property
    apply havoid ((W.ι ≫ pullback.fst φ f).fiberι u w) hw i
    have hc := congrArg (fun z => z w) hcomm
    simpa [x, he, Scheme.Hom.comp_apply] using hc.symm
  refine ⟨U, φ, u, hφ, rfl, hres, W, ⨆ i, V i, ?_, ?_, ?_, ?_⟩
  · exact ⟨disjoint_iSup_iff.mpr hWV, codisjoint_iff.mpr hcover⟩
  · exact isFinite_iSup_of_pairwiseDisjoint (pullback.fst φ f) n V hVV hfin
  · intro w hopen
    apply hnot w
    simpa only [Set.image_singleton] using j.isOpenEmbedding.isOpenMap _ hopen
  · intro hfiniteFiber
    -- A finite Jacobson fibre is discrete, so every point would be isolated.
    let := hfiniteFiber.fintype
    have : Finite (f.fiber (φ u)) :=
      Finite.of_equiv _ (f.fiberHomeo (φ u)).toEquiv.symm
    exact ⟨fun w => hnot w (isOpen_discrete _)⟩

end AlgebraicGeometry
