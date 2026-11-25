/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.FinitePresentationModuleMapDescent
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentAffineCharts
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation

/-! # A flat module on a fixed affine-limit model descends to a later stage

Source: Stacks Project, Tags 01ZR and 05LY.
(blueprint: lem-pc-flat-module-on-later-stage).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- The sectionwise comparison proofs below follow PullbackModelFlatnessComparison.
-- They are local because importing that module would close a cycle through DirectImage.
private theorem flatOver_restrict
    {P Q T : Scheme.{u}} (e : P ⟶ Q) [IsOpenImmersion e]
    (b : Q ⟶ T) (M : Q.Modules) (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.restrictFunctor e).obj M).IsFlatOver (e ≫ b) := by
  intro V U hU
  let U' : Q.affineOpens := ⟨e ''ᵁ U.1, U.2.image_of_isOpenImmersion e⟩
  have hU' : U'.1 ≤ b ⁻¹ᵁ V.1 :=
    (e.image_mono (show U.1 ≤ e ⁻¹ᵁ (b ⁻¹ᵁ V.1) from hU)).trans
      (e.image_preimage_le _)
  have hh := hflat V U' hU'
  convert hh using 1 <;> try rfl
  ext r m
  change (M.smul ((e.appIso U.1).inv.hom
    (((e ≫ b).appLE V.1 U.1 hU).hom r))).asHom.hom m =
      (M.smul ((b.appLE V.1 U'.1 hU').hom r)).asHom.hom m
  have he : U.1 ≤ e ⁻¹ᵁ U'.1 := (e.preimage_image_eq U.1).ge
  have hcomp := e.appLE_comp_appLE b V.1 U'.1 U.1 hU' he
  have hring : (e ≫ b).appLE V.1 U.1 hU ≫ (e.appIso U.1).inv =
      b.appLE V.1 U'.1 hU' := by
    rw [← hcomp, Category.assoc, ← Scheme.Hom.appIso_hom', Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun t : Γ(T, V.1) ⟶ Γ(Q, U'.1) ↦ (M.smul (t.hom r)).asHom.hom m) hring

private theorem flatOver_tensorPullback_iso
    {P Q T : Scheme.{u}} (e : P ≅ Q) (b : Q ⟶ T) (M : Q.Modules)
    (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.tensorPullback e.hom).obj M).IsFlatOver (e.hom ≫ b) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction e.hom
  let δ := adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction e.hom)
  exact (flatOver_restrict e.hom b M hflat).of_iso (δ.app M).symm

private theorem flatOver_of_cartesian_model
    {P Q X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {b : P ⟶ T} {a' : Q ⟶ X} {b' : Q ⟶ T}
    (hp : IsPullback a b f g) (hq : IsPullback a' b' f g) (M : X.Modules)
    (hflat : ((Scheme.Modules.tensorPullback a').obj M).IsFlatOver b') :
    ((Scheme.Modules.tensorPullback a).obj M).IsFlatOver b := by
  let e : P ≅ Q := hp.isoPullback ≪≫ hq.isoPullback.symm
  have ha : e.hom ≫ a' = a := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_fst, hp.isoPullback_hom_fst]
  have hb : e.hom ≫ b' = b := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_snd, hp.isoPullback_hom_snd]
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom a'
  let δ' : Scheme.Modules.tensorPullback a ≅
      Scheme.Modules.tensorPullback a' ⋙ Scheme.Modules.tensorPullback e.hom :=
    eqToIso (congrArg (fun k ↦ Scheme.Modules.tensorPullback k) ha.symm) ≪≫ δ
  have hP := flatOver_tensorPullback_iso e b'
    ((Scheme.Modules.tensorPullback a').obj M) hflat
  refine Scheme.Modules.IsFlatOver.of_iso (δ'.app M).symm ?_
  simpa only [Functor.comp_obj, hb] using hP

-- Tag 05LY: use the acyclic chart and algebra interfaces from the FlatModuleDescent proof.
private theorem exists_eventually_isFlatOver_of_limit
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
    (hflat : Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (Opposite.op i)))).obj M)
      (pullback.snd f (c.π.app (Opposite.op i)))) :
    ∃ j : I, ∃ hij : i ≤ j, ∀ (k : I) (hjk : j ≤ k),
      Scheme.Modules.IsFlatOver
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE (hij.trans hjk)))))).obj M)
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := by
  open scoped TensorProduct in
    classical
    obtain ⟨n, B, N, a, hB, hN, hlimit, hstage⟩ :=
      exists_flat_module_descent_affine_charts R c hc i f M hflat
    have hdescent (b : Fin n) : ∃ j : I, i ≤ j ∧
        ∀ (k : I) (hij : i ≤ j) (hjk : j ≤ k),
          (letI : Module (R.obj i : Type u) (N b) := Module.compHom _ (a b)
          letI : Algebra (R.obj i : Type u) (R.obj k : Type u) :=
            (R.map (homOfLE (hij.trans hjk))).hom.toAlgebra
          letI : Algebra (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.TensorProduct.rightAlgebra
          letI : Module (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.toModule
          Module.Flat ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
            (((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
              ⊗[(R.obj i : Type u)] (N b))) := by
      let := (a b).toAlgebra
      let := hB b
      let := hN b
      exact exists_eventually_flat_of_finitePresentation (Ni := (N b : Type u))
        R (colimit.cocone R)
        (colimit.isColimit R) (Algebra.ofId (R.obj i : Type u) (B b : Type u)) (hlimit b)
    choose j hij hj using hdescent
    have hbound (s : Finset (Fin n)) : ∃ k : I, i ≤ k ∧ ∀ b ∈ s, j b ≤ k := by
      induction s using Finset.induction_on with
      | empty => exact ⟨i, le_rfl, by simp⟩
      | @insert b s _ ih =>
        obtain ⟨k, hik, hk⟩ := ih
        obtain ⟨l, hkl, hbl⟩ := exists_ge_ge k (j b)
        refine ⟨l, hik.trans hkl, ?_⟩
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hbl
        · exact (hk d hd).trans hkl
    obtain ⟨k, hik, hk⟩ := hbound Finset.univ
    refine ⟨k, hik, ?_⟩
    intro l hkl
    apply hstage l (hik.trans hkl)
    intro b
    exact hj b l (hij b) ((hk b (Finset.mem_univ b)).trans hkl)


/-- On the limit base change of a fixed finitely presented scheme, a finitely presented
relatively flat module descends to a finitely presented relatively flat module at a
later stage. The source model is fixed; no scheme approximation or properness is asserted.

Source: Stacks Project, limits.tex, Tag 01ZR (lemma-descend-modules-finite-presentation)
and Tag 05LY (lemma-descend-module-flat-finite-presentation).
(blueprint: lem-pc-flat-module-on-later-stage).

Proof: Work on the directed tail of indices above i; it is cofinal, so the limit
is unchanged. The base changes of Zi on this tail are quasi-compact and quasi-separated,
since fi is so and every base is affine. Their transition maps are affine, as base
changes of morphisms between affine schemes. Base change preserves the limit.
Finite presentation of M implies quasi-coherence. Apply Tag 01ZR to obtain j above i,
a finitely presented module N on the base change of the fixed source to Spec R_j,
and an isomorphism of its limit tensor pullback with M. Transport relative flatness
of M through this isomorphism, by restriction of scalars of the sectionwise linear
isomorphisms on affine opens. Apply Tag 05LY to N, starting at j, to obtain a stage k
above j at which its pullback is flat over Spec R_k. Take M_k to be this pullback;
finite presentation is preserved by tensor pullback. Cartesian pasting identifies the
iterated source base change with the direct base change from i to k. The canonical
composition isomorphism for tensor pullback, followed by the initial comparison with M,
gives the displayed comparison. This does not require proper support or derived objects.
The starting index excludes an empty index set. Empty sources, zero modules and zero
rings cause no exception; no transition map is assumed flat. -/
theorem exists_flat_module_on_later_stage
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Zi : Scheme.{u}} (fi : Zi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (M : (pullback fi (c.π.app (Opposite.op i))).Modules) [M.IsFinitePresentation]
    (hM : M.IsFlatOver (pullback.snd fi (c.π.app (Opposite.op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Mj : (pullback fi (Spec.map (R.map (homOfLE hij)))).Modules),
      Mj.IsFinitePresentation ∧
      Mj.IsFlatOver (pullback.snd fi (Spec.map (R.map (homOfLE hij)))) ∧
      Nonempty ((Scheme.Modules.moduleBaseChange fi
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (Opposite.op i)))
        (Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M) := by
  classical
  obtain ⟨j, hij, N, hN, hNq, ⟨eN⟩⟩ :=
    (finitePresentation_module_map_descent R c hc i fi).1 M inferInstance inferInstance
  let := hN
  let := hNq
  let fj := pullback.snd fi (Spec.map (R.map (homOfLE hij)))
  let g : Over.mk (c.π.app (Opposite.op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op)
  have hflat := hM.of_iso eN.symm
  have hflat' := flatOver_of_cartesian_model
    (IsPullback.of_hasPullback fj (c.π.app (Opposite.op j)))
    (isPullback_baseChangeMap fi g) N hflat
  obtain ⟨k, hjk, hk⟩ := exists_eventually_isFlatOver_of_limit R c hc j fj N hflat'
  let gk : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let gLimit : Over.mk (c.π.app (Opposite.op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) :=
    Over.homMk (c.π.app (Opposite.op k)) (c.w (homOfLE (hij.trans hjk)).op)
  let Nk := (Scheme.Modules.moduleBaseChange fi gk).obj N
  have hNk : Nk.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorPullback (baseChangeMap fi gk) N
  have hNkflat : Nk.IsFlatOver
      (pullback.snd fi (Spec.map (R.map (homOfLE (hij.trans hjk))))) := by
    apply flatOver_of_cartesian_model (isPullback_baseChangeMap fi gk)
      (IsPullback.of_hasPullback fj (Spec.map (R.map (homOfLE hjk)))) N
    simpa using hk k le_rfl
  have hw : baseChangeMap fi gLimit ≫ baseChangeMap fi gk = baseChangeMap fi g := by
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa [gLimit, gk, g] using c.w (homOfLE hjk).op
  let e := Scheme.Modules.tensorPullbackCompositionIso
    (baseChangeMap fi gLimit) (baseChangeMap fi gk) (baseChangeMap fi g) hw
  exact ⟨k, hij.trans hjk, Nk, hNk, hNkflat, ⟨(e.app N).symm ≪≫ eN⟩⟩

end AlgebraicGeometry
