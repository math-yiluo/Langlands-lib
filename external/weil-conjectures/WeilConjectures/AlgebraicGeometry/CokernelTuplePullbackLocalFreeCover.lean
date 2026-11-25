/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import all WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Data.Fintype.EquivFin

/-! # Local finite-free covers of a cokernel tuple pullback

Source: Stacks Project, Modules, Lemma 01BY, cokernel paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

-- Pulling back the second arrow of an exact complex preserves exactness.
private theorem exact_pullback
    {C : Type*} [Category C] [Abelian C] {A B H L : C}
    (f : A ⟶ B) (q : B ⟶ H) (hfq : f ≫ q = 0)
    (he : (ShortComplex.mk f q hfq).Exact) (g : L ⟶ H) :
    (ShortComplex.mk (pullback.lift 0 f (by simp [hfq])) (pullback.fst g q)
      (by simp)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Z z hz
  obtain ⟨Z', r, hr, a, ha⟩ := he.exact_up_to_refinements
    (z ≫ pullback.snd g q) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      simpa using hz =≫ g)
  refine ⟨Z', r, hr, a, ?_⟩
  apply pullback.hom_ext
  · simpa using r ≫= hz
  · simpa using ha

-- Adjoin lifts of quotient generators to generators of the first term.
private theorem epi_pullback_generators
    {C : Type*} [Category C] [Abelian C] {A B H L E K : C}
    (f : A ⟶ B) (q : B ⟶ H) (hfq : f ≫ q = 0)
    (he : (ShortComplex.mk f q hfq).Exact) (g : L ⟶ H)
    (p : E ⟶ A) [Epi p] (e : K ≅ L) (l : K ⟶ B)
    (hl : e.hom ≫ g = l ≫ q) :
    Epi (coprod.desc (p ≫ pullback.lift 0 f (by simp [hfq]))
      (pullback.lift e.hom l hl)) := by
  let a : A ⟶ pullback g q := pullback.lift 0 f (by simp [hfq])
  let b : K ⟶ pullback g q := pullback.lift e.hom l hl
  let S := ShortComplex.mk a (pullback.fst g q) (by simp [a])
  have hS : S.Exact := exact_pullback f q hfq he g
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z t ht
  have ha : a ≫ t = 0 := by
    apply (cancel_epi p).mp
    simpa [a] using congrArg (fun k ↦ coprod.inl ≫ k) ht
  have : Epi S.g := epi_of_epi_fac
    (show b ≫ S.g = e.hom by simp [b, S])
  let d := hS.desc t ha
  have hb : e.hom ≫ d = 0 := by
    rw [← show b ≫ S.g = e.hom by simp [b, S], Category.assoc]
    change b ≫ S.g ≫ hS.desc t ha = 0
    rw [hS.g_desc]
    simpa [b] using congrArg (fun k ↦ coprod.inr ≫ k) ht
  have hd : d = 0 := by
    apply (cancel_epi e.hom).mp
    simpa using hb
  rw [← hS.g_desc t ha]
  change S.g ≫ d = 0
  rw [hd, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem tuple_over_eval (X : RingedSpace.{u})
    (M : SheafOfModules.{u} (moduleRings X)) {U V : Opens X} (hVU : V ≤ U)
    {I : Type u} (g : SheafOfModules.free (R := (moduleRings X).over U) I ⟶ M.over U)
    (i : I) :
    let D := SheafOfModules.overMap (moduleRings X) (homOfLE hVU)
    let e := SheafOfModules.mapFreeIso D I
      (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE hVU)).symm
    let c := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app M
    (((M.over V).freeHomEquiv (e.hom ≫ D.map g ≫ c.hom) i).val
      (Opposite.op (Over.mk (𝟙 V)))) =
      M.val.map (homOfLE hVU).op
        (((M.over U).freeHomEquiv g i).val (Opposite.op (Over.mk (𝟙 U)))) := by
  dsimp only
  let D := SheafOfModules.overMap (moduleRings X) (homOfLE hVU)
  let η := (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE hVU)).symm
  let c := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app M
  have he : SheafOfModules.ιFree i ≫
      (SheafOfModules.mapFreeIso D I η).hom ≫ D.map g ≫ c.hom =
      η.hom ≫ D.map (SheafOfModules.ιFree i ≫ g) ≫ c.hom := by
    simp only [SheafOfModules.ιFree_mapFreeIso_hom_assoc, D.map_comp, Category.assoc]
  have hs := congrArg
    (fun f ↦ ((M.over V).unitHomEquiv f).val (Opposite.op (Over.mk (𝟙 V)))) he
  change _ = ((M.over U).freeHomEquiv g i).val
    (Opposite.op (Over.mk (homOfLE hVU))) at hs
  exact hs.trans (((M.over U).val.sections_property ((M.over U).freeHomEquiv g i)
    (Over.homMk (homOfLE hVU) : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U)).op).symm)

-- Enumerate finite free sources without unfolding the target or its construction.
private theorem finite_free_cover_of_finite_coprod
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I K : Type u) [Finite I] [Finite K] {M : SheafOfModules.{u} R}
    (p : SheafOfModules.free (R := R) I ⨿ SheafOfModules.free K ⟶ M) [Epi p] :
    ∃ (m : ℕ) (q : SheafOfModules.free (R := R) (ULift.{u} (Fin m)) ⟶ M), Epi q := by
  classical
  let : Fintype (I ⊕ K) := Fintype.ofFinite (I ⊕ K)
  let eI : ULift.{u} (Fin (Fintype.card (I ⊕ K))) ≃ (I ⊕ K) :=
    Equiv.ulift.trans (Fintype.equivFin (I ⊕ K)).symm
  let eFree := (SheafOfModules.freeFunctor (R := R)).mapIso (Equiv.toIso eI)
  let q := eFree.hom ≫ (SheafOfModules.freeSumIso (R := R) I K).inv ≫ p
  exact ⟨Fintype.card (I ⊕ K), q, by dsimp [q]; infer_instance⟩

-- Convert a family of section lifts to a commuting free-sheaf map for arbitrary modules.
private theorem free_tuple_lift_of_sections (X : RingedSpace.{u})
    (G H : SheafOfModules.{u} (moduleRings X)) (q : G ⟶ H)
    {U V : Opens X} (hVU : V ≤ U) {I : Type u}
    (g : SheafOfModules.free (R := (moduleRings X).over U) I ⟶ H.over U)
    (t : I → G.val.obj (Opposite.op V))
    (ht : ∀ i, q.val.app (Opposite.op V) (t i) =
      H.val.map (homOfLE hVU).op
        (((H.over U).freeHomEquiv g i).val (Opposite.op (Over.mk (𝟙 U))))) :
    let D := SheafOfModules.overMap (moduleRings X) (homOfLE hVU)
    let e := SheafOfModules.mapFreeIso D I
      (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE hVU)).symm
    let c := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app H
    (G.over V).freeHomEquiv.symm (fun i ↦ section_on_open X G V (t i)) ≫ q.over V =
      e.hom ≫ D.map g ≫ c.hom := by
  dsimp only
  apply (H.over V).freeHomEquiv.injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
  apply sections_ext_top X H V
  rw [tuple_over_eval]
  change q.val.app (Opposite.op V) (G.val.map (𝟙 _) (t i)) = _
  rw [G.val.map_id]
  exact ht i

set_option backward.isDefEq.respectTransparency false in
-- Unfold restriction functors while synthesizing the pullback instance.
/-- The pullback of a finite tuple along a cokernel projection admits a local
finite-free epimorphism.

Source: Stacks Project, Modules, Lemma 01BY, cokernel paragraph.
(blueprint: lem-weil-pbc-cokernel-tuple-pullback-local-free-cover)

Proof: The image of `f` is finite type as an epimorphic image of `F`. Around `x`,
lift the finitely many sections of `g` through the cokernel projection, then
intersect their neighbourhoods with a neighbourhood on which the image of `f`
has finitely many generators. Restrict the lifts and generators to that common
neighbourhood `V`. The pullback consists of pairs `(a,b)` such that the image of
`b` in the cokernel equals the given tuple evaluated on `a`. It is generated by
pairs consisting of each free basis vector and its chosen lift, together with
pairs `(0,s)` for the chosen image generators `s`. Indeed, subtract the linear
combination of the lifted basis vectors from any pair; its first component is
zero and its second lies in the image of `f`, hence is locally generated by the
`s`. This proves local surjectivity of the map from the finite free sheaf on
these two finite lists, hence it is epi. Enumerate the union as `ULift (Fin m)`.
The empty tuple only uses the image generators; empty `U` has no point `x`.
No coherence or global surjectivity on sections is used. -/
theorem cokernel_tuple_pullback_local_free_cover (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G)
    (hF : F.IsFiniteType) (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      (cokernel f).over U) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ ∃ (m : ℕ)
      (p : SheafOfModules.free (R := (moduleRings X).over V)
        (ULift.{u} (Fin m)) ⟶
          pullback ((SheafOfModules.overMap (moduleRings X) (homOfLE hVU)).map g)
            ((SheafOfModules.overMap (moduleRings X) (homOfLE hVU)).map
              ((cokernel.π f).over U))), Epi p := by
  classical
  -- Reuse the sheafification instances throughout the restrictions and free constructions.
  have hsheaf (V : Opens X) :
      HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u} :=
    inferInstance
  have hbijective (V : Opens X) :
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  -- Use generators of F directly; their images generate the kernel of the projection.
  obtain ⟨σ, hσ⟩ := hF.exists_localGeneratorsData
  obtain ⟨W, _, ⟨j, ⟨hj⟩⟩, hxW⟩ := σ.coversTop ⊤ x (by trivial)
  have hxj : x ∈ σ.X j := hj.le hxW
  have := hσ.isFiniteType j
  let T := U ⊓ σ.X j
  let gT := (SheafOfModules.mapFreeIso
    (SheafOfModules.overMap (moduleRings X) (homOfLE (show T ≤ U from inf_le_left)))
    (ULift.{u} (Fin n))
    (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE inf_le_left)).symm).hom ≫
    (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left)).map g ≫
    ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE inf_le_left)).app
      (cokernel f)).hom
  obtain ⟨V, hVT, hxV, t, ht⟩ := finite_sections_lift X (cokernel.π f) T
    (fun i ↦ (((cokernel f).over T).freeHomEquiv gT i).val
      (Opposite.op (Over.mk (𝟙 T)))) x ⟨hx, hxj⟩
  have hVU : V ≤ U := hVT.trans inf_le_left
  let D := SheafOfModules.overMap (moduleRings X) (homOfLE hVU)
  let cF := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app F
  let cG := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app G
  let cH := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).app (cokernel f)
  let e := SheafOfModules.mapFreeIso D (ULift.{u} (Fin n))
    (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE hVU)).symm
  let l₀ : SheafOfModules.free (R := (moduleRings X).over V) (ULift.{u} (Fin n)) ⟶
      G.over V := (G.over V).freeHomEquiv.symm (fun i ↦ section_on_open X G V (t i))
  have hl₀ : l₀ ≫ (cokernel.π f).over V = e.hom ≫ D.map g ≫ cH.hom := by
    apply free_tuple_lift_of_sections X G (cokernel f) (cokernel.π f) hVU g t
    intro i
    rw [ht i, tuple_over_eval]
    exact ((cokernel f).val.map_comp_apply
      (homOfLE inf_le_left).op (homOfLE hVT).op _).symm.trans
      ((cokernel f).val.congr_map_apply (Subsingleton.elim _ _) _)
  let l := l₀ ≫ cG.inv
  let fV := D.map (f.over U)
  let q := D.map ((cokernel.π f).over U)
  have hfV : fV ≫ q = 0 := by
    change D.map (f.over U) ≫ D.map ((cokernel.π f).over U) = 0
    rw [← D.map_comp, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, D.map_zero]
  -- Restrict the exact cokernel sequence, then pull it back along the tuple.
  have he : (ShortComplex.mk fV q hfV).Exact :=
    (ShortComplex.cokernelSequence_exact f).map_of_epi_of_preservesCokernel
      (SheafOfModules.overFunctor (moduleRings X) U ⋙ D) inferInstance inferInstance
  have hl : e.hom ≫ D.map g = l ≫ q := by
    apply (cancel_mono cH.hom).mp
    have hn : q ≫ cH.hom = cG.hom ≫ (cokernel.π f).over V :=
      (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE hVU)).hom.naturality
        (cokernel.π f)
    change e.hom ≫ D.map g ≫ cH.hom = (l₀ ≫ cG.inv) ≫ q ≫ cH.hom
    rw [Category.assoc, hn, cG.inv_hom_id_assoc]
    exact hl₀.symm
  let a := generators_over X F (σ.generators j) (hVT.trans inf_le_right)
  have : a.IsFiniteType := generators_over_finite X F (σ.generators j) _
  let pF := a.π ≫ cF.inv
  let p := coprod.desc (pF ≫ pullback.lift 0 fV (by simp [hfV]))
    (pullback.lift e.hom l hl)
  have : Epi pF := by dsimp [pF]; infer_instance
  have : Epi p := epi_pullback_generators fV q hfV he (D.map g) pF e l hl
  obtain ⟨m, p', hp'⟩ := finite_free_cover_of_finite_coprod a.I (ULift.{u} (Fin n)) p
  exact ⟨V, hVU, hxV, m, p', hp'⟩

end AlgebraicGeometry.RingedSpace
