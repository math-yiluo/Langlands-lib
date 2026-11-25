/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentPreorder
import WeilConjectures.AlgebraicGeometry.ProperSupportDescent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Eventual flatness and proper support of a chosen finite-stage module

Source: Stacks Project, Tags 05LY, 081G, 0CYS, 0032 and 0097.
(blueprint: lem-pc-chosen-module-flat-proper-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem supportProper_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {M N : X.Modules} (e : M ≅ N)
    (hN : Scheme.Modules.HasSupportProperOver f N) :
    Scheme.Modules.HasSupportProperOver f M := by
  obtain ⟨Z, hZ, hp⟩ := hN
  refine ⟨Z, hZ.trans ?_, hp⟩
  ext x
  let es := ((Scheme.Modules.toPresheaf X) ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso e
  have hs : Subsingleton (M.presheaf.stalk x) ↔ Subsingleton (N.presheaf.stalk x) := by
    constructor
    · intro h
      have : Subsingleton (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).obj M) := h
      exact Function.Surjective.subsingleton
        ((ConcreteCategory.bijective_of_isIso es.hom).2)
    · intro h
      have : Subsingleton (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).obj N) := h
      exact Function.Injective.subsingleton
        ((ConcreteCategory.bijective_of_isIso es.hom).1)
  exact not_congr hs.symm

private theorem supportProper_cartesian
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ T)
    [LocallyOfFiniteType f] [LocallyOfFiniteType b]
    (a : Y ⟶ X) (g : T ⟶ S) (h : IsPullback a b f g)
    (M : X.Modules) [M.IsFinitePresentation]
    (hp : Scheme.Modules.HasSupportProperOver f M) :
    Scheme.Modules.HasSupportProperOver b ((Scheme.Modules.tensorPullback a).obj M) := by
  obtain ⟨Z, hZ, hpZ⟩ := hp
  let W : TopologicalSpace.Closeds Y :=
    ⟨a.base ⁻¹' (Z : Set X), Z.isClosed.preimage a.base.hom.continuous⟩
  refine ⟨W, ?_, ?_⟩
  · exact (congrArg (fun A : Set X ↦ a.base ⁻¹' A) hZ).trans
      ((Scheme.Modules.finiteType_module_support_pullback M).2.2 Y a).2.symm
  · obtain ⟨Z', z, hz, hrange, hpz⟩ :=
      (Scheme.closed_subset_proper_over_base_properties f Z).1.mp hpZ
    have : IsClosedImmersion z := hz
    have : IsProper (z ≫ f) := hpz
    let w := pullback.snd z a
    have hw : Set.range w.base = (W : Set Y) := by
      change Set.range (pullback.snd z a) = a ⁻¹' (Z : Set X)
      rw [Scheme.Pullback.range_snd]
      exact congrArg (fun A : Set X ↦ a ⁻¹' A) hrange
    apply (Scheme.closed_subset_proper_over_base_properties b W).1.mpr
    refine ⟨pullback z a, w, inferInstance, hw, ?_⟩
    exact MorphismProperty.of_isPullback (P := @IsProper)
      ((IsPullback.of_hasPullback z a).paste_vert h) hpz

private theorem supportProper_of_cartesian_model
    {P Q X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {b : P ⟶ T} {a' : Q ⟶ X} {b' : Q ⟶ T}
    [LocallyOfFiniteType b] [LocallyOfFiniteType b']
    (hp : IsPullback a b f g) (hq : IsPullback a' b' f g)
    (M : X.Modules) [M.IsFinitePresentation]
    (hs : Scheme.Modules.HasSupportProperOver b'
      ((Scheme.Modules.tensorPullback a').obj M)) :
    Scheme.Modules.HasSupportProperOver b ((Scheme.Modules.tensorPullback a).obj M) := by
  let e : P ≅ Q := hp.isoPullback ≪≫ hq.isoPullback.symm
  have ha : e.hom ≫ a' = a := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_fst, hp.isoPullback_hom_fst]
  have hb : e.hom ≫ b' = b := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_snd, hp.isoPullback_hom_snd]
  have he : IsPullback e.hom b b' (𝟙 T) := by
    exact IsPullback.of_horiz_isIso ⟨by simpa using hb⟩
  have hfp : ((Scheme.Modules.tensorPullback a').obj M).IsFinitePresentation := by
    obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a'
    exact Scheme.Modules.isFinitePresentation_of_iso
      ((adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction a')).app M).symm
  have ht := supportProper_cartesian b' b e.hom (𝟙 T) he
    ((Scheme.Modules.tensorPullback a').obj M) hs
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom a'
  let δ' : Scheme.Modules.tensorPullback a ≅
      Scheme.Modules.tensorPullback a' ⋙ Scheme.Modules.tensorPullback e.hom :=
    eqToIso (congrArg (fun k ↦ Scheme.Modules.tensorPullback k) ha.symm) ≪≫ δ
  exact supportProper_of_iso b (δ'.app M) ht

/-- A chosen finitely presented module becomes flat with proper support at every later stage.

Source: Stacks Project, Tags 05LY, 081G, 0CYS, 0032 and 0097.
(blueprint: lem-pc-chosen-module-flat-proper-stage).

Proof: View M on X_j with its finitely presented structure morphism to Spec R_j.
Pullback pasting identifies its pullback to the limiting base with the module in the
hypotheses. Tag 05LY gives eventual flatness for this finitely presented module.
Tag 081G gives a stage with proper support, interpreted as properness of the reduced
closed support by Tag 0CYS. Choose an upper bound of the two stages. Cartesian tensor
pullback preserves finite presentation, relative flatness and proper support; hence the
properties hold at every later stage. The tensor-pullback composition isomorphism and
pullback pasting identify these modules with the displayed moduleBaseChange objects.
For a preorder, apply Tag 0032 to choose a final directed poset in its thin filtered
category, with an object mapping above j. Restrict the diagram and its limit to this
poset, apply the preceding argument, and take its image stage in I. For any later stage
of I, the cartesian tensor-pullback preservation theorem transports both properties
from that image stage; no lifting of the later stage through the final functor is needed.
The zero module, an empty source and an empty support cause no exception: tensor
pullback preserves zero and the empty closed subscheme is proper over any base. -/
theorem exists_eventually_chosen_module_flat_proper
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    [M.IsFinitePresentation]
    (hflat : ((Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj M).IsFlatOver
        (pullback.snd f (c.π.app (op i))))
    (hproper : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj M)) :
    ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
      let hjl := hjk.trans hkl
      let B := Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjl)))
          (by simp [← Functor.map_comp, ← Spec.map_comp]))
      (B.obj M).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjl))))) ∧
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjl)))))
        (B.obj M) := by
  classical
  let tj : Over (Spec (R.obj i)) := Over.mk (Spec.map (R.map (homOfLE hij)))
  let tLimit : Over (Spec (R.obj i)) := Over.mk (c.π.app (op i))
  let gLimit : tLimit ⟶ tj := Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  let fj := pullback.snd f tj.hom
  have hflat' : ((Scheme.Modules.tensorPullback (baseChangeMap f gLimit)).obj M).IsFlatOver
      (pullback.snd f tLimit.hom) := hflat
  obtain ⟨kf, hjkf, hf⟩ :=
    exists_eventually_isFlatOver_of_isPullback_limit_preorder R c hc j fj M
      (baseChangeMap f gLimit) (pullback.snd f tLimit.hom)
      (isPullback_baseChangeMap f gLimit) hflat'
  have hproper' : Scheme.Modules.HasSupportProperOver
      (pullback.snd fj (c.π.app (op j)))
      ((Scheme.Modules.tensorPullback (pullback.fst fj (c.π.app (op j)))).obj M) := by
    apply supportProper_of_cartesian_model (IsPullback.of_hasPullback _ _)
      (isPullback_baseChangeMap f gLimit) M
    exact hproper
  obtain ⟨kp, hjkp, hp⟩ :=
    exists_hasSupportProperOver_baseChange_of_isLimit R c hc j fj M hproper'
  obtain ⟨k, hfk, hpk⟩ := exists_ge_ge kf kp
  refine ⟨k, hjkf.trans hfk, ?_⟩
  intro l hkl
  let hjl := (hjkf.trans hfk).trans hkl
  let tl : Over (Spec (R.obj i)) :=
    Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl))))
  let gjl : tl ⟶ tj := Over.homMk (Spec.map (R.map (homOfLE hjl)))
    (by simp [tl, tj, ← Functor.map_comp, ← Spec.map_comp])
  change ((Scheme.Modules.tensorPullback (baseChangeMap f gjl)).obj M).IsFlatOver
      (pullback.snd f tl.hom) ∧
    Scheme.Modules.HasSupportProperOver (pullback.snd f tl.hom)
      ((Scheme.Modules.tensorPullback (baseChangeMap f gjl)).obj M)
  refine ⟨hf l (hfk.trans hkl) (baseChangeMap f gjl) (pullback.snd f tl.hom)
    (isPullback_baseChangeMap f gjl), ?_⟩
  let tp : Over (Spec (R.obj i)) :=
    Over.mk (Spec.map (R.map (homOfLE (hij.trans hjkp))))
  let gjp : tp ⟶ tj := Over.homMk (Spec.map (R.map (homOfLE hjkp)))
    (by simp [tp, tj, ← Functor.map_comp, ← Spec.map_comp])
  have hp' : Scheme.Modules.HasSupportProperOver (pullback.snd f tp.hom)
      ((Scheme.Modules.tensorPullback (baseChangeMap f gjp)).obj M) := by
    exact supportProper_of_cartesian_model (isPullback_baseChangeMap f gjp)
      (IsPullback.of_hasPullback _ _) M hp
  have hfp :
      ((Scheme.Modules.tensorPullback (baseChangeMap f gjp)).obj M).IsFinitePresentation := by
    obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f gjp)
    exact Scheme.Modules.isFinitePresentation_of_iso
      ((adj.leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f gjp))).app M).symm
  let gpl : tl ⟶ tp := Over.homMk (Spec.map (R.map (homOfLE (hpk.trans hkl))))
    (by simp [tl, tp, ← Functor.map_comp, ← Spec.map_comp])
  have hg : gpl ≫ gjp = gjl := by
    ext
    simp [gpl, gjp, gjl, ← Functor.map_comp, ← Spec.map_comp]
  have ht := supportProper_cartesian (pullback.snd f tp.hom) (pullback.snd f tl.hom)
    (baseChangeMap f gpl) gpl.left (isPullback_baseChangeMap f gpl)
    ((Scheme.Modules.tensorPullback (baseChangeMap f gjp)).obj M) hp'
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (baseChangeMap f gpl) (baseChangeMap f gjp)
  have hcomp : baseChangeMap f gpl ≫ baseChangeMap f gjp = baseChangeMap f gjl := by
    rw [← baseChangeMap_comp, hg]
  let δ' : Scheme.Modules.tensorPullback (baseChangeMap f gjl) ≅
      Scheme.Modules.tensorPullback (baseChangeMap f gjp) ⋙
        Scheme.Modules.tensorPullback (baseChangeMap f gpl) :=
    eqToIso (congrArg Scheme.Modules.tensorPullback hcomp.symm) ≪≫ δ
  exact supportProper_of_iso _ (δ'.app M) ht

end AlgebraicGeometry
