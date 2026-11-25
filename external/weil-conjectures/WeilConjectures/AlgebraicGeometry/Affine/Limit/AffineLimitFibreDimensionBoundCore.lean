/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.Local.LocalFibreDimensionOpen

/-!
# Bad-locus contradiction for affine limit fibre dimensions

This is the bad-locus and Noetherian-fibre stabilization part of the affine limit dimension
argument. It is split from the final existence theorem so that the top-level implication remains
fully checked while this long construction can be proved independently.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`.
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem surjective_of_isPushout
    {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {a : S ⟶ P} {b : T ⟶ P} (h : IsPushout f g a b)
    (hf : Function.Surjective f) : Function.Surjective b := by
  have hs := RingHom.surjective_isStableUnderBaseChange.pushout_inl
    RingHom.surjective_respectsIso g f hf
  have he : pushout.inl g f ≫ h.flip.isoPushout.inv = b := h.flip.inl_isoPushout_inv
  rw [← he]
  exact (ConcreteCategory.bijective_of_isIso h.flip.isoPushout.inv).2.comp hs

private theorem finiteType_of_isPushout
    {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {a : S ⟶ P} {b : T ⟶ P} (h : IsPushout f g a b)
    (hf : f.hom.FiniteType) : b.hom.FiniteType := by
  have hs := RingHom.finiteType_isStableUnderBaseChange.pushout_inl
    RingHom.finiteType_respectsIso g f hf
  rw [← h.flip.inl_isoPushout_inv, CommRingCat.hom_comp]
  exact (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso h.flip.isoPushout.inv).2).comp hs

private theorem fibreSystem
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (K : CommRingCat.{u}) (a : colimit A ⟶ K) :
    ∃ (B : I ⥤ CommRingCat.{u}) (b : C ⟶ B)
      (k : (Functor.const I).obj K ⟶ B)
      (t : B ⟶ (Functor.const I).obj (pushout (colimMap φ) a)),
      Nonempty (IsColimit (Cocone.mk _ t)) ∧
      (∀ i, IsPushout (φ.app i) (colimit.ι A i ≫ a) (b.app i) (k.app i)) ∧
      (∀ i, b.app i ≫ t.app i = colimit.ι C i ≫ pushout.inl (colimMap φ) a) ∧
      (∀ i, k.app i ≫ t.app i = pushout.inr (colimMap φ) a) := by
  classical
  let ai (i : I) := colimit.ι A i ≫ a
  have hai {i j : I} (f : i ⟶ j) : A.map f ≫ ai j = ai i := by
    simp [ai]
  let B : I ⥤ CommRingCat.{u} :=
    { obj := fun i ↦ pushout (φ.app i) (ai i)
      map := fun {i j} f ↦ pushout.desc (C.map f ≫ pushout.inl (φ.app j) (ai j))
        (pushout.inr (φ.app j) (ai j)) (by
          rw [← Category.assoc, ← φ.naturality f, Category.assoc, pushout.condition,
            ← Category.assoc, hai])
      map_id := by intro i; apply pushout.hom_ext <;> simp
      map_comp := by intro i j k f g; apply pushout.hom_ext <;> simp [Category.assoc] }
  let b : C ⟶ B :=
    { app := fun i ↦ pushout.inl (φ.app i) (ai i)
      naturality := by intro i j f; simp [B] }
  let k : (Functor.const I).obj K ⟶ B :=
    { app := fun i ↦ pushout.inr (φ.app i) (ai i)
      naturality := by intro i j f; simp [B] }
  have hw (i : I) : φ.app i ≫ colimit.ι C i ≫ pushout.inl (colimMap φ) a =
      ai i ≫ pushout.inr (colimMap φ) a := by
    rw [← Category.assoc, ← ι_colimMap, Category.assoc, pushout.condition]
    rfl
  let c : Cocone B :=
    { pt := pushout (colimMap φ) a
      ι :=
        { app := fun i ↦ pushout.desc (colimit.ι C i ≫ pushout.inl (colimMap φ) a)
            (pushout.inr (colimMap φ) a) (hw i)
          naturality := by
            intro i j f
            apply pushout.hom_ext <;> simp [B, Category.assoc] } }
  have hc : IsColimit c := by
    let i₀ : I := Classical.arbitrary I
    have hconst (s : Cocone B) (i j : I) : k.app i ≫ s.ι.app i = k.app j ≫ s.ι.app j := by
      obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
      calc
        k.app i ≫ s.ι.app i = k.app l ≫ s.ι.app l := by
          rw [← s.w (homOfLE hil), ← Category.assoc, ← k.naturality]
          simp
        _ = k.app j ≫ s.ι.app j := by
          rw [← s.w (homOfLE hjl), ← Category.assoc, ← k.naturality]
          simp
    let t (s : Cocone B) : Cocone C :=
      { pt := s.pt
        ι := b ≫ s.ι }
    have hcompat (s : Cocone B) : colimMap φ ≫ colimit.desc C (t s) =
        a ≫ k.app i₀ ≫ s.ι.app i₀ := by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, ι_colimMap, Category.assoc, colimit.ι_desc]
      change φ.app i ≫ b.app i ≫ s.ι.app i = _
      rw [← Category.assoc, pushout.condition, Category.assoc, hconst s i i₀]
      rfl
    refine
      { desc := fun s ↦ pushout.desc (colimit.desc C (t s))
          (k.app i₀ ≫ s.ι.app i₀) (hcompat s)
        fac := ?_
        uniq := ?_ }
    · intro s i
      apply pushout.hom_ext
      · simp [c, t, b, Category.assoc]
      · simpa [c, k, Category.assoc] using (hconst s i₀ i)
    · intro s m hm
      apply pushout.hom_ext
      · apply colimit.hom_ext
        intro i
        have hi := congrArg (fun e ↦ b.app i ≫ e) (hm i)
        simpa [c, t, b, Category.assoc] using hi
      · have hi := congrArg (fun e ↦ k.app i₀ ≫ e) (hm i₀)
        simpa [c, k, Category.assoc] using hi
  exact ⟨B, b, k, c.ι, ⟨hc⟩, fun i ↦ IsPushout.of_hasPushout _ _,
    fun i ↦ by simp [b, c], fun i ↦ by simp [k, c]⟩

private theorem fibreSystem_surjective
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C B : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (K : CommRingCat.{u}) (a : colimit A ⟶ K)
    (b : C ⟶ B) (k : (Functor.const I).obj K ⟶ B)
    (hb : ∀ i, IsPushout (φ.app i) (colimit.ι A i ≫ a) (b.app i) (k.app i))
    (hsurj : ∀ (i j : I) (hij : i ≤ j), Function.Surjective
      (pushout.desc (φ.app j) (C.map (homOfLE hij))
        (φ.naturality (homOfLE hij))).hom) :
    ∀ {i j : I} (f : i ⟶ j), Function.Surjective (B.map f) := by
  intro i j f
  let ai := colimit.ι A i ≫ a
  let aj := colimit.ι A j ≫ a
  have ha : A.map f ≫ aj = ai := by simp [ai, aj]
  let P := pushout (A.map f) (φ.app i)
  let q : P ⟶ C.obj j := pushout.desc (φ.app j) (C.map f) (φ.naturality f)
  let m : P ⟶ B.obj i := pushout.desc (aj ≫ k.app i) (b.app i) (by
    rw [← Category.assoc, ha]; exact (hb i).w.symm)
  have h₁ : IsPushout (A.map f ≫ aj) (φ.app i) (k.app i)
      (pushout.inr (A.map f) (φ.app i) ≫ m) := by
    simpa only [ha, m, pushout.inr_desc] using (hb i).flip
  have h₂ : IsPushout (pushout.inl (A.map f) (φ.app i)) aj m (k.app i) :=
    (h₁.of_left (by simp [m]) (IsPushout.of_hasPushout _ _)).flip
  have hk : k.app i ≫ B.map f = k.app j := by
    simpa using (k.naturality f).symm
  have h₃ : IsPushout (pushout.inl (A.map f) (φ.app i) ≫ q) aj (b.app j)
      (k.app i ≫ B.map f) := by
    simpa only [q, pushout.inl_desc, hk, aj] using hb j
  have hm : q ≫ b.app j = m ≫ B.map f := by
    apply pushout.hom_ext
    · simpa [q, m, Category.assoc, hk, aj] using (hb j).w
    · simp [q, m]
  have h₄ := h₃.of_left hm h₂
  exact surjective_of_isPushout h₄ (hsurj i j (leOfHom f))

private theorem surjective_ι_of_surjective_maps
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hsurj : ∀ {i j : I} (f : i ⟶ j), Function.Surjective (F.map f))
    (i : I) : Function.Surjective (c.ι.app i) := by
  intro x
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  let k := IsFiltered.max i j
  let f : i ⟶ k := IsFiltered.leftToMax i j
  let g : j ⟶ k := IsFiltered.rightToMax i j
  obtain ⟨z, hz⟩ := hsurj f (F.map g y)
  refine ⟨z, ?_⟩
  calc
    c.ι.app i z = c.ι.app k (F.map f z) :=
      (ConcreteCategory.congr_hom (c.w f) z).symm
    _ = c.ι.app k (F.map g y) := congrArg (c.ι.app k) hz
    _ = c.ι.app j y := ConcreteCategory.congr_hom (c.w g) y

private theorem exists_bijective_ι_of_noetherian
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hsurj : ∀ {i j : I} (f : i ⟶ j), Function.Surjective (F.map f))
    (i : I) [IsNoetherianRing (F.obj i)] :
    ∃ j : I, Function.Bijective (c.ι.app j) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (c.ι.app i).hom))
  have hkill (x : s) : ∃ (j : I) (f : i ⟶ j), F.map f x = 0 := by
    have hx : c.ι.app i x = c.ι.app i 0 := by
      rw [map_zero]
      exact (show x.1 ∈ RingHom.ker (c.ι.app i).hom from hs ▸ Ideal.subset_span x.2)
    obtain ⟨j, f, g, he⟩ := (Concrete.isColimit_rep_eq_iff_exists F hc x.1 0).mp hx
    exact ⟨j, f, by simpa using he⟩
  choose j f hf using hkill
  obtain ⟨t⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i j f)
  let k := t.pt
  let g : i ⟶ k := t.ι.app none
  have hker : RingHom.ker (c.ι.app i).hom ≤ RingHom.ker (F.map g).hom := by
    rw [← hs, Ideal.span_le]
    intro x hx
    change F.map g x = 0
    have he := t.w (WidePushoutShape.Hom.init (⟨x, hx⟩ : s))
    change f ⟨x, hx⟩ ≫ t.ι.app (some ⟨x, hx⟩) = g at he
    rw [← he, F.map_comp, CommRingCat.comp_apply, hf, map_zero]
  refine ⟨k, ?_, surjective_ι_of_surjective_maps F c hc hsurj k⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj g x
  obtain ⟨b, rfl⟩ := hsurj g y
  have hab : a - b ∈ RingHom.ker (c.ι.app i).hom := by
    change c.ι.app i (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact (ConcreteCategory.congr_hom (c.w g) a).symm.trans
      (hxy.trans (ConcreteCategory.congr_hom (c.w g) b))
  have he := hker hab
  change F.map g (a - b) = 0 at he
  rwa [map_sub, sub_eq_zero] at he

private theorem localDim_embedding_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (f x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
  exact (iInf₂_le V hx).trans
    ((hf.restrictPreimage (U : Set Y)).isInducing.topologicalKrullDim_le)

private theorem localDim_fiber_point {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) (x : X) (hy : f.fiberι s y = x) :
    topologicalKrullDimAt y = topologicalKrullDimAt (f.asFiber x) := by
  have hx : f x = s := by
    rw [← hy, ← Scheme.Hom.comp_apply, f.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst s
  congr 1
  apply (f.fiberι (f x)).isEmbedding.injective
  simpa using hy

private theorem localDim_fibre_le_of_closed_comparison
    {Xi Xj Si Sj : Scheme.{u}} (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj)
    [LocallyOfFiniteType fi] (g : Sj ⟶ Si)
    (h : Xj ⟶ pullback fi g) [IsClosedImmersion h]
    (hh : h ≫ pullback.snd fi g = fj) (x : Xj) :
    topologicalKrullDimAt (fj.asFiber x) ≤
      topologicalKrullDimAt (fi.asFiber (pullback.fst fi g (h x))) := by
  let f' := pullback.snd fi g
  let e : fj.fiber (fj x) ⟶ f'.fiber (fj x) :=
    pullback.lift (fj.fiberι _ ≫ h) (fj.fiberToSpecResidueField _) (by
      rw [Category.assoc, hh, fj.fiber_fac])
  have he : e ≫ f'.fiberι (fj x) = fj.fiberι (fj x) ≫ h := pullback.lift_fst ..
  have hemb : Topology.IsEmbedding e := by
    apply Topology.IsEmbedding.of_comp e.continuous (f'.fiberι _).continuous
    change Topology.IsEmbedding (e ≫ f'.fiberι (fj x))
    rw [he]
    exact h.isClosedEmbedding.isEmbedding.comp (fj.fiberι _).isEmbedding
  have hp := localDim_fiber_point f' (fj x) (e (fj.asFiber x)) (h x) (by
    change (e ≫ f'.fiberι _) (fj.asFiber x) = h x
    rw [he, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber])
  exact (localDim_embedding_le hemb (fj.asFiber x)).trans_eq
    (hp.trans (fibre_dimension_after_base_change fi g (h x)).2.2)

private theorem raw_fibre_dim_eq {R S : CommRingCat.{u}} (f : R ⟶ S)
    (p : PrimeSpectrum R) :
    topologicalKrullDim
      (pullback (Spec.map f) (Spec.map (CommRingCat.ofHom
        (algebraMap R p.asIdeal.ResidueField))) : Scheme.{u}) =
      topologicalKrullDim ((Spec.map f).fiber p) := by
  let i := Scheme.Spec.residueFieldIso R p
  have hi := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p
  let e : (Spec.map f).fiber p ≅ pullback (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) :=
    (pullback.congrHom rfl hi.symm) ≪≫
      (pullbackLeftPullbackSndIso _ _ _).symm ≪≫
      asIso (pullback.fst _ _)
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm

private theorem localDim_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e.hom x) := by
  apply le_antisymm (localDim_embedding_le e.hom.homeomorph.isEmbedding x)
  simpa using localDim_embedding_le e.inv.homeomorph.isEmbedding (e.hom x)

private theorem localDim_asFiber_field {K : CommRingCat.{u}} (hK : IsField K)
    {X : Scheme.{u}} (f : X ⟶ Spec K) (x : X) :
    topologicalKrullDimAt (f.asFiber x) = topologicalKrullDimAt x := by
  let := hK.toField
  have : IsIso (CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (f x).asIdeal.algEquivResidueFieldOfField.bijective
  have : IsIso ((Spec K).fromSpecResidueField (f x)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    infer_instance
  have : IsIso (f.fiberι (f x)) := by
    dsimp [Scheme.Hom.fiberι]
    infer_instance
  simpa using localDim_iso (asIso (f.fiberι (f x))) (f.asFiber x)

private theorem localDim_in_pullback
    {X S : Scheme.{u}} {K : CommRingCat.{u}} (hK : IsField K)
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : Spec K ⟶ S)
    {Y : Scheme.{u}} (a : Y ⟶ X) (b : Y ⟶ Spec K)
    (h : IsPullback a b f g) (y : Y) :
    topologicalKrullDimAt y = topologicalKrullDimAt (f.asFiber (a y)) := by
  let e := h.isoPullback
  have hdim := (fibre_dimension_after_base_change f g (e.hom y)).2.2
  rw [localDim_asFiber_field hK] at hdim
  have he : pullback.fst f g (e.hom y) = a y := by
    change (e.hom ≫ pullback.fst f g) y = a y
    rw [h.isoPullback_hom_fst]
  exact (localDim_iso e y).trans (he ▸ hdim)

private theorem exists_bad_point {R S : CommRingCat.{u}} (f : R ⟶ S)
    (p : PrimeSpectrum R) (d : ℕ)
    (hd : (d : WithBot ℕ∞) < topologicalKrullDim
      (pullback (Spec.map f) (Spec.map (CommRingCat.ofHom
        (algebraMap R p.asIdeal.ResidueField))) : Scheme.{u})) :
    ∃ x : Spec S, (d : WithBot ℕ∞) < topologicalKrullDimAt ((Spec.map f).asFiber x) := by
  rw [raw_fibre_dim_eq, topologicalKrullDim_eq_iSup_topologicalKrullDimAt] at hd
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hd
  refine ⟨(Spec.map f).fiberι p y, ?_⟩
  rwa [← localDim_fiber_point (Spec.map f) p y _ rfl]

private theorem localDim_stage_le
    {I : Type u} [PartialOrder I] (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (hfinite : ∀ i, (φ.app i).hom.FiniteType)
    (hsurj : ∀ (i j : I) (hij : i ≤ j), Function.Surjective
      (pushout.desc (φ.app j) (C.map (homOfLE hij))
        (φ.naturality (homOfLE hij))).hom)
    {i j : I} (f : i ⟶ j) (x : Spec (C.obj j)) :
    topologicalKrullDimAt ((Spec.map (φ.app j)).asFiber x) ≤
      topologicalKrullDimAt
        ((Spec.map (φ.app i)).asFiber (Spec.map (C.map f) x)) := by
  let q := pushout.desc (φ.app j) (C.map f) (φ.naturality f)
  let hp := (isPullback_SpecMap_pushout (A.map f) (φ.app i)).flip
  let c := Spec.map q ≫ hp.isoPullback.hom
  have : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q (hsurj i j (leOfHom f))
  have : IsClosedImmersion c := by dsimp [c]; infer_instance
  have : LocallyOfFiniteType (Spec.map (φ.app i)) :=
    HasRingHomProperty.Spec_iff.mpr (hfinite i)
  have hc : c ≫ pullback.snd (Spec.map (φ.app i)) (Spec.map (A.map f)) =
      Spec.map (φ.app j) := by
    simp [c, Category.assoc, ← Spec.map_comp, q]
  have hc' : c ≫ pullback.fst (Spec.map (φ.app i)) (Spec.map (A.map f)) =
      Spec.map (C.map f) := by
    simp [c, Category.assoc, ← Spec.map_comp, q]
  have h := localDim_fibre_le_of_closed_comparison _ _ _ c hc x
  have hx : pullback.fst (Spec.map (φ.app i)) (Spec.map (A.map f)) (c x) =
      Spec.map (C.map f) x := by
    change (c ≫ pullback.fst _ _) x = _
    rw [hc']
  rwa [hx] at h

/-- If every finite stage has a fibre of dimension strictly greater than `d`, then the limiting
fibre cannot have dimension at most `d`, under the finite type and closed-comparison hypotheses.
This is the bad-locus contradiction in Tag 05M5: the bad local-dimension loci are open complements,
their reduced closed subschemes have a nonempty affine inverse limit, and Noetherian stabilization
of a fixed limiting fibre produces a point contradicting the assumed bound.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`, affine specialization.
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound-core).
-/
theorem fibre_dimension_contradiction_of_all_stages_bad
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (hfinite : ∀ i : I, (φ.app i).hom.FiniteType)
    (hsurj : ∀ (i j : I) (hij : i ≤ j),
      Function.Surjective
        (pushout.desc (φ.app j) (C.map (homOfLE hij))
          (φ.naturality (homOfLE hij))).hom)
    (d : ℕ)
    (hbound : ∀ (p : Ideal ↥(colimit A)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (colimMap φ))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(colimit A) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞))
    (hbad : ∀ i : I, ∃ p : PrimeSpectrum (A.obj i),
      (d : WithBot ℕ∞) <
        topologicalKrullDim
          ↥(pullback (Spec.map (φ.app i))
            (Spec.map (CommRingCat.ofHom
              (algebraMap (A.obj i) p.asIdeal.ResidueField))) : Scheme.{u})) :
    False := by
  classical
  let D := C.op ⋙ Scheme.Spec
  let c := Scheme.Spec.mapCone (colimit.cocone C).op
  have hc : IsLimit c := isLimitOfPreserves _ (colimit.isColimit C).op
  let Z (i : Iᵒᵖ) : Set (D.obj i) :=
    {x | ¬ topologicalKrullDimAt ((Spec.map (φ.app i.unop)).asFiber x) ≤
      (d : WithBot ℕ∞)}
  have hft (i : I) : LocallyOfFiniteType (Spec.map (φ.app i)) :=
    HasRingHomProperty.Spec_iff.mpr (hfinite i)
  have hZc (i : Iᵒᵖ) : IsClosed (Z i) :=
    (isOpen_localFibreDimension_le (Spec.map (φ.app i.unop)) d).isClosed_compl
  have hZne (i : Iᵒᵖ) : (Z i).Nonempty := by
    obtain ⟨p, hp⟩ := hbad i.unop
    obtain ⟨x, hx⟩ := exists_bad_point (φ.app i.unop) p d hp
    exact ⟨x, not_le.mpr hx⟩
  have (i : Iᵒᵖ) : CompactSpace (D.obj i) := inferInstanceAs (CompactSpace (Spec _))
  have {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  have hZcompact (i : Iᵒᵖ) : IsCompact (Z i) := (hZc i).isCompact
  have hmaps : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), Set.MapsTo (D.map g) (Z i) (Z j) := by
    intro i j g x hx hle
    exact hx ((localDim_stage_le A C φ hfinite hsurj g.unop x).trans hle)
  obtain ⟨x, hx⟩ := exists_mem_of_isClosed_of_nonempty D c hc Z hZc hZne hZcompact hmaps
  change Spec (colimit C) at x
  have hx' (i : I) : ¬ topologicalKrullDimAt
      ((Spec.map (φ.app i)).asFiber (Spec.map (colimit.ι C i) x)) ≤ (d : WithBot ℕ∞) :=
    hx (Opposite.op i)
  let f := Spec.map (colimMap φ)
  let s := f x
  let K := (Spec (colimit A)).residueField s
  let a : colimit A ⟶ K :=
    CommRingCat.ofHom (algebraMap ↥(colimit A) s.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (colimit A) s).inv
  have ha : Spec.map a = (Spec (colimit A)).fromSpecResidueField s := by
    rw [Spec.map_comp]
    exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _
  have hbound' : topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞) := by
    have hb := hbound s.asIdeal
    rwa [raw_fibre_dim_eq] at hb
  obtain ⟨B, b, k, t, ⟨hB⟩, hb, hbt, hkt⟩ := fibreSystem A C φ K a
  have hs : ∀ {i j : I} (g : i ⟶ j), Function.Surjective (B.map g) :=
    fun g ↦ fibreSystem_surjective A C B φ K a b k hb hsurj g
  let i : I := Classical.arbitrary I
  let : Algebra K (B.obj i) := (k.app i).hom.toAlgebra
  let : Algebra.FiniteType K (B.obj i) := finiteType_of_isPushout (hb i) (hfinite i)
  let : IsNoetherianRing (B.obj i) := Algebra.FiniteType.isNoetherianRing K _
  obtain ⟨j, hj⟩ := exists_bijective_ι_of_noetherian B (Cocone.mk _ t) hB hs i
  have : IsIso (t.app j) := (ConcreteCategory.isIso_iff_bijective _).mpr hj
  let P := pushout (colimMap φ) a
  have hp : IsPullback (Spec.map (pushout.inl (colimMap φ) a))
      (Spec.map (pushout.inr (colimMap φ) a)) f
      ((Spec (colimit A)).fromSpecResidueField s) := by
    rw [← ha]
    exact isPullback_SpecMap_pushout _ _
  let e : Spec P ≅ f.fiber s := hp.isoPullback
  let y : Spec P := e.inv (f.asFiber x)
  have he : e.hom ≫ f.fiberι s = Spec.map (pushout.inl (colimMap φ) a) :=
    hp.isoPullback_hom_fst
  have hy : Spec.map (pushout.inl (colimMap φ) a) y = x := by
    rw [← he, Scheme.Hom.comp_apply]
    change f.fiberι s ((e.inv ≫ e.hom) (f.asFiber x)) = x
    rw [e.inv_hom_id]
    exact f.fiberι_asFiber x
  let yj := Spec.map (t.app j) y
  have hyj : Spec.map (b.app j) yj = Spec.map (colimit.ι C j) x := by
    change (Spec.map (t.app j) ≫ Spec.map (b.app j)) y = _
    rw [← Spec.map_comp, hbt, Spec.map_comp, Scheme.Hom.comp_apply]
    exact congrArg (Spec.map (colimit.ι C j)) hy
  have hdim := localDim_in_pullback (Field.toIsField K) (Spec.map (φ.app j))
    (Spec.map (colimit.ι A j ≫ a)) (Spec.map (b.app j)) (Spec.map (k.app j))
    (isPullback_SpecMap_of_isPushout _ _ _ _ (hb j)) yj
  rw [hyj] at hdim
  have hdim' : topologicalKrullDimAt y = topologicalKrullDimAt
      ((Spec.map (φ.app j)).asFiber (Spec.map (colimit.ι C j) x)) :=
    (localDim_iso (asIso (Spec.map (t.app j))) y).trans hdim
  have hle : topologicalKrullDimAt (f.asFiber x) ≤ (d : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt] at hbound'
    exact (le_iSup _ (f.asFiber x)).trans hbound'
  have hey : e.hom y = f.asFiber x := by
    change (e.inv ≫ e.hom) (f.asFiber x) = f.asFiber x
    rw [e.inv_hom_id]
    rfl
  exact hx' j (hdim' ▸ ((localDim_iso e y).trans_le (hey ▸ hle)))

end AlgebraicGeometry
