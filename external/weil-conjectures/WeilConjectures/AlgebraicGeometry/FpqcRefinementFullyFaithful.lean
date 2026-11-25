/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.DescentPullbackCanonicalIso
import WeilConjectures.AlgebraicGeometry.FpqcSingletonFullyFaithful

/-!
# Full faithfulness of refinement for fpqc descent data

Source: Stacks Project, Descent, Lemma 35.35.11 (Tag 02W0), specialized to singleton
fpqc coverings (blueprint: lem-galois-fpqc-refinement-fully-faithful).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

-- A map between two realizations of the same base change respects transport.
private theorem pullback_map_commutes {S X T : Scheme.{u}}
    {a : X ⟶ S} {b : T ⟶ S} {r : T ⟶ X} (hr : r ≫ a = b)
    (D : Over.DescentDataCategory a) (A B : Over.DescentDataCategory b)
    (qA : A.V.left ⟶ D.V.left) (qB : B.V.left ⟶ D.V.left)
    (hqA : qA ≫ D.V.hom = A.V.hom ≫ r)
    (hqB : qB ≫ D.V.hom = B.V.hom ≫ r)
    (pbB : IsPullback qB B.V.hom D.V.hom r)
    (bcA : Over.DescentDatum.IsBaseChange hr hqA D.datum A.datum)
    (bcB : Over.DescentDatum.IsBaseChange hr hqB D.datum B.datum)
    (m : A.V ⟶ B.V) (hm : m.left ≫ qB = qA) :
    ∀ {U : Scheme.{u}} (i j : U ⟶ T) (hij : i ≫ b = j ≫ b)
      (z : Over.mk i ⟶ A.V),
      B.datum.transport i j hij (z ≫ m) = A.datum.transport i j hij z ≫ m := by
  intro U i j hij z
  apply Over.OverMorphism.ext
  apply pbB.hom_ext
  · have e : (Over.homMk ((z ≫ m).left ≫ qB) (by simp [hqB]) :
        Over.mk (i ≫ r) ⟶ D.V) =
        (Over.homMk (z.left ≫ qA) (by simp [hqA]) : Over.mk (i ≫ r) ⟶ D.V) := by
      ext
      simp [hm]
    rw [← bcB i j hij (z ≫ m), e, bcA i j hij z]
    simp [hm]
  · simp

-- The universal isomorphism of pullbacks is also an isomorphism of descent data.
private theorem pullback_datum_iso {S X T : Scheme.{u}}
    {a : X ⟶ S} {b : T ⟶ S} {r : T ⟶ X} (hr : r ≫ a = b)
    (D : Over.DescentDataCategory a) (A B : Over.DescentDataCategory b)
    (qA : A.V.left ⟶ D.V.left) (qB : B.V.left ⟶ D.V.left)
    (hqA : qA ≫ D.V.hom = A.V.hom ≫ r)
    (hqB : qB ≫ D.V.hom = B.V.hom ≫ r)
    (pbA : IsPullback qA A.V.hom D.V.hom r)
    (pbB : IsPullback qB B.V.hom D.V.hom r)
    (bcA : Over.DescentDatum.IsBaseChange hr hqA D.datum A.datum)
    (bcB : Over.DescentDatum.IsBaseChange hr hqB D.datum B.datum) :
    ∃ e : A ≅ B, e.hom.hom.left ≫ qB = qA := by
  let e := pbA.isoIsPullback _ _ pbB
  have eh : e.hom ≫ qB = qA := pbA.isoIsPullback_hom_fst _ _ pbB
  have ei : e.inv ≫ qA = qB := pbA.isoIsPullback_inv_fst _ _ pbB
  let m : A.V ⟶ B.V := Over.homMk e.hom (pbA.isoIsPullback_hom_snd _ _ pbB)
  let n : B.V ⟶ A.V := Over.homMk e.inv (pbA.isoIsPullback_inv_snd _ _ pbB)
  refine ⟨{ hom := ⟨m, pullback_map_commutes hr D A B qA qB hqA hqB pbB bcA bcB m eh⟩
            inv := ⟨n, pullback_map_commutes hr D B A qB qA hqB hqA pbA bcB bcA n ei⟩
            hom_inv_id := ?_, inv_hom_id := ?_ }, eh⟩
  · apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    exact e.hom_inv_id
  · apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    exact e.inv_hom_id

-- Pullback realizations give naturally isomorphic functors.
private theorem pullback_functor_iso {S X T : Scheme.{u}}
    {a : X ⟶ S} {b : T ⟶ S} {r : T ⟶ X} (hr : r ≫ a = b)
    (F G : Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
    (qF : ∀ D, (F.obj D).V.left ⟶ D.V.left)
    (qG : ∀ D, (G.obj D).V.left ⟶ D.V.left)
    (hqF : ∀ D, qF D ≫ D.V.hom = (F.obj D).V.hom ≫ r)
    (hqG : ∀ D, qG D ≫ D.V.hom = (G.obj D).V.hom ≫ r)
    (pbF : ∀ D, IsPullback (qF D) (F.obj D).V.hom D.V.hom r)
    (pbG : ∀ D, IsPullback (qG D) (G.obj D).V.hom D.V.hom r)
    (bcF : ∀ D, Over.DescentDatum.IsBaseChange hr (hqF D) D.datum (F.obj D).datum)
    (bcG : ∀ D, Over.DescentDatum.IsBaseChange hr (hqG D) D.datum (G.obj D).datum)
    (mapF : ∀ D E (m : D ⟶ E), (F.map m).hom.left ≫ qF E = qF D ≫ m.hom.left)
    (mapG : ∀ D E (m : D ⟶ E), (G.map m).hom.left ≫ qG E = qG D ≫ m.hom.left) :
    Nonempty (F ≅ G) := by
  classical
  choose e he using fun D ↦ pullback_datum_iso hr D (F.obj D) (G.obj D)
    (qF D) (qG D) (hqF D) (hqG D) (pbF D) (pbG D) (bcF D) (bcG D)
  refine ⟨NatIso.ofComponents e ?_⟩
  intro D E m
  apply Over.DescentDataCategory.Hom.ext
  apply Over.OverMorphism.ext
  apply (pbG E).hom_ext
  · change ((F.map m).hom.left ≫ (e E).hom.hom.left) ≫ qG E =
      ((e D).hom.hom.left ≫ (G.map m).hom.left) ≫ qG E
    rw [Category.assoc, he, Category.assoc, mapG, ← Category.assoc, he, mapF]
  · change ((F.map m).hom.left ≫ (e E).hom.hom.left) ≫ (G.obj E).V.hom =
      ((e D).hom.hom.left ≫ (G.map m).hom.left) ≫ (G.obj E).V.hom
    simp

-- Full faithfulness is independent of the chosen pullback realization.
private theorem pullback_functor_fullyFaithful {S X T : Scheme.{u}}
    {a : X ⟶ S} {b : T ⟶ S} {r : T ⟶ X} (hcomp : r ≫ a = b)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X)
    (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
    (qF : ∀ D, (F.obj D).V.left ⟶ D.V.left)
    (hqF : ∀ D, qF D ≫ D.V.hom = (F.obj D).V.hom ≫ r)
    (pbF : ∀ D, IsPullback (qF D) (F.obj D).V.hom D.V.hom r)
    (bcF : ∀ D, Over.DescentDatum.IsBaseChange hcomp (hqF D) D.datum (F.obj D).datum)
    (mapF : ∀ D E (m : D ⟶ E), (F.map m).hom.left ≫ qF E = qF D ≫ m.hom.left) :
    Nonempty F.FullyFaithful := by
  classical
  subst b
  obtain ⟨G, qG, ⟨ffG⟩, objG, mapG⟩ := fpqc_singleton_pullback_fullyFaithful a r hr
  choose hqG pbG bcG using objG
  obtain ⟨e⟩ := pullback_functor_iso rfl G F qG qF hqG hqF pbG pbF bcG bcF mapG mapF
  exact ⟨ffG.ofIso e⟩

private theorem singleton_cover_baseChange {S X Y Z : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {p : Z ⟶ Y} {q : Z ⟶ X}
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (pb : IsPullback p q g f) :
    Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y := by
  rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
  exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit ↦ f) hf g
    (fun _ ↦ p) (fun _ ↦ q) (fun _ ↦ pb)

/-- For singleton fpqc coverings `f` and `g` of `S`, with `g = h ≫ f`, descent data
pull back along `h`. Every morphism of the pulled-back data uniquely descends to a
morphism of the original data. The pullback objects and their data are described by
`IsPullback` and `Over.DescentDatum.IsBaseChange` respectively.

The proof of Stacks, Tag 02W0, forms `X' ×_S X`. Its projections to `X` and `X'` are
singleton fpqc coverings by base change (Tag 022D). The singleton full-faithfulness
theorem (Tag 0241) applies to both projections. The canonical comparison of pullbacks
(Tags 02VS and 023Y) identifies pullback along the projection to `X` with pullback
along `h` followed by the projection to `X'`. Given a morphism between the data pulled
back along `h`, fullness for the projection to `X` lifts its further pullback to a
morphism of the original data. Faithfulness for the projection to `X'` shows that this
lift pulls back to the given morphism. Faithfulness for the projection to `X` makes the
lift unique.

(blueprint: lem-galois-fpqc-refinement-fully-faithful) -/
theorem fpqcRefinementFullyFaithful {S X X' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S) (h : X' ⟶ X)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage S)
    (hcomp : h ≫ f = g) :
    (∀ (V : Over X) (D : Over.DescentDatum f V),
      ∃ (V' : Over X') (q : V'.left ⟶ V.left) (hq : q ≫ V.hom = V'.hom ≫ h)
        (D' : Over.DescentDatum g V'),
        IsPullback q V'.hom V.hom h ∧
          Over.DescentDatum.IsBaseChange hcomp hq D D') ∧
    (∀ (V W : Over X) (D : Over.DescentDatum f V) (E : Over.DescentDatum f W)
        (V' W' : Over X') (qV : V'.left ⟶ V.left) (qW : W'.left ⟶ W.left)
        (hqV : qV ≫ V.hom = V'.hom ≫ h) (hqW : qW ≫ W.hom = W'.hom ≫ h)
        (D' : Over.DescentDatum g V') (E' : Over.DescentDatum g W'),
      IsPullback qV V'.hom V.hom h → IsPullback qW W'.hom W.hom h →
      Over.DescentDatum.IsBaseChange hcomp hqV D D' →
      Over.DescentDatum.IsBaseChange hcomp hqW E E' →
      ∀ (u' : V' ⟶ W'),
        (∀ {T : Scheme.{u}} (a b : T ⟶ X') (hab : a ≫ g = b ≫ g)
            (x : Over.mk a ⟶ V'),
          (D'.transport a b hab x) ≫ u' =
            E'.transport a b hab (x ≫ u')) →
        ∃! (u : V ⟶ W),
          (∀ {T : Scheme.{u}} (a b : T ⟶ X) (hab : a ≫ f = b ≫ f)
              (x : Over.mk a ⟶ V),
            (D.transport a b hab x) ≫ u =
              E.transport a b hab (x ≫ u)) ∧
          u'.left ≫ qW = qV ≫ u.left) := by
  classical
  obtain ⟨pull, q, hq, obj, map, compare, compose⟩ := descent_pullback_canonical_iso S
  have ff : ∀ {A B : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
      (r : B ⟶ A) (hr : r ≫ a = b),
      Presieve.singleton r ∈ Scheme.fpqcPrecoverage A →
        Nonempty (pull a b r hr).FullyFaithful := by
    intro A B a b r hr hcover
    exact pullback_functor_fullyFaithful hr hcover (pull a b r hr) (q a b r hr)
      (hq a b r hr) (fun D ↦ (obj a b r hr D).1)
      (fun D ↦ (obj a b r hr D).2) (map a b r hr)
  let Y := pullback g f
  let p : Y ⟶ X := pullback.snd g f
  let t : Y ⟶ X' := pullback.fst g f
  let c : Y ⟶ S := p ≫ f
  have htc : t ≫ g = c := pullback.condition
  have hpc : p ≫ f = c := rfl
  have hthc : (t ≫ h) ≫ f = c := by rw [Category.assoc, hcomp, htc]
  have hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage X :=
    singleton_cover_baseChange hg (IsPullback.of_hasPullback g f).flip
  have ht : Presieve.singleton t ∈ Scheme.fpqcPrecoverage X' :=
    singleton_cover_baseChange hf (IsPullback.of_hasPullback g f)
  obtain ⟨ffP⟩ := ff f c p hpc hp
  obtain ⟨ffT⟩ := ff g c t htc ht
  obtain ⟨e₁, _⟩ := compare f c p (t ≫ h) hpc hthc
  obtain ⟨e₂, _⟩ := compose f g c h t hcomp htc hthc
  let e := e₁ ≪≫ e₂
  let F := pull f g h hcomp
  let G := pull g c t htc
  let : (pull f c p hpc).Full := ffP.full
  let : (pull f c p hpc).Faithful := ffP.faithful
  let : G.Faithful := ffT.faithful
  let : F.Full := Functor.Full.of_comp_faithful_iso e.symm
  let : F.Faithful := Functor.Faithful.of_comp_iso e.symm
  constructor
  · intro V D
    let A : Over.DescentDataCategory f := ⟨V, D⟩
    exact ⟨(F.obj A).V, q f g h hcomp A, hq f g h hcomp A,
      (F.obj A).datum, obj f g h hcomp A⟩
  · intro V W D E V' W' qV qW hqV hqW D' E' pbV pbW bcV bcW u' hu'
    let A : Over.DescentDataCategory f := ⟨V, D⟩
    let B : Over.DescentDataCategory f := ⟨W, E⟩
    let A' : Over.DescentDataCategory g := ⟨V', D'⟩
    let B' : Over.DescentDataCategory g := ⟨W', E'⟩
    obtain ⟨i, hi⟩ := pullback_datum_iso hcomp A (F.obj A) A'
      (q f g h hcomp A) qV (hq f g h hcomp A) hqV
      (obj f g h hcomp A).1 pbV (obj f g h hcomp A).2 bcV
    obtain ⟨j, hj⟩ := pullback_datum_iso hcomp B (F.obj B) B'
      (q f g h hcomp B) qW (hq f g h hcomp B) hqW
      (obj f g h hcomp B).1 pbW (obj f g h hcomp B).2 bcW
    let m' : A' ⟶ B' := ⟨u', fun a b hab x ↦ (hu' a b hab x).symm⟩
    let m : A ⟶ B := F.preimage (i.hom ≫ m' ≫ j.inv)
    have hm : F.map m ≫ j.hom = i.hom ≫ m' := by simp [m]
    have hiInv : i.inv.hom.left ≫ i.hom.hom.left = 𝟙 V'.left :=
      congrArg (fun z : A' ⟶ A' ↦ z.hom.left) i.inv_hom_id
    have hfac : u'.left ≫ qW = qV ≫ m.hom.left := by
      have eq := congrArg (fun z : F.obj A ⟶ B' ↦ z.hom.left ≫ qW) hm
      change ((F.map m).hom.left ≫ j.hom.hom.left) ≫ qW =
        (i.hom.hom.left ≫ u'.left) ≫ qW at eq
      rw [Category.assoc, hj, map f g h hcomp A B m, ← hi] at eq
      have eq' := congrArg (fun z ↦ i.inv.hom.left ≫ z) eq
      simp only [← Category.assoc, hiInv] at eq'
      dsimp only [A', B] at eq'
      simpa only [Category.id_comp] using eq'.symm
    refine ⟨m.hom, ⟨fun a b hab x ↦ (m.commutes a b hab x).symm, hfac⟩, ?_⟩
    intro n hn
    let nn : A ⟶ B := ⟨n, fun a b hab x ↦ (hn.1 a b hab x).symm⟩
    have hnmap : F.map nn ≫ j.hom = i.hom ≫ m' := by
      apply Over.DescentDataCategory.Hom.ext
      apply Over.OverMorphism.ext
      apply pbW.hom_ext
      · change ((F.map nn).hom.left ≫ j.hom.hom.left) ≫ qW =
          (i.hom.hom.left ≫ u'.left) ≫ qW
        rw [Category.assoc, hj, map f g h hcomp A B nn,
          Category.assoc, hn.2, ← Category.assoc, hi]
      · exact (Over.w ((F.map nn).hom ≫ j.hom.hom)).trans
          (Over.w (i.hom.hom ≫ m'.hom)).symm
    have hnm : nn = m := F.map_injective (by
      apply (cancel_mono j.hom).1
      exact hnmap.trans hm.symm)
    exact congrArg (fun z : A ⟶ B ↦ z.hom) hnm

end AlgebraicGeometry
