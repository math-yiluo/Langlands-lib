/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Finite type is preserved by module pullback

Source: Stacks Project, Modules, Lemma 01B6 (lemma-pullback-finite-type),
(blueprint: lem-weil-pbc-module-pullback-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a morphism of schemes, the pullback of a finite type module is finite type.

Source: Stacks Project, Modules, Lemma 01B6 (lemma-pullback-finite-type),
(blueprint: lem-weil-pbc-module-pullback-finite-type).

The hypothesis `[G.IsFiniteType]` renders that every point of the target has an open
neighbourhood on which a finite direct sum of the structure sheaf surjects onto `G`.
The conclusion says the same for `tensorPullback f G`; the local proof takes the inverse
image of the neighbourhood and uses the same finite number of summands. The second
conjunct records this explicitly for every surjection on an open `V`: `(Opens.map f.base).obj V`
is `f⁻¹ V`, and `free (ULift (Fin n))` is the direct sum of `n` structure sheaves.

Proof, following the four steps of the node:
1. For an open `V` of `Y`, put `U = f⁻¹ V` and let `f' : U → V` be the restricted
   morphism. The over-site equivalences, restriction-pullback and composition isomorphisms
   identify pullback of `G.over V` along `f'` with `(pullback f G).over U`.
   Uniqueness of left adjoints compares Mathlib pullback with `tensorPullback`.
2. The functor between over-site module categories preserves colimits and epimorphisms.
   Pullback of the unit sheaf is the unit sheaf, so `mapFreeIso` identifies the free
   sheaves of the same rank. Composing these isomorphisms with the image of any epi
   `φ` gives the epi on `U` required by the second conjunct, including rank zero.
3. Choose finite local generators data for `G`. Identify each finite generating index
   type with `ULift (Fin n)` and apply the local epi construction of step 2. The
   resulting epis give finite generating sections on the inverse-image opens.
4. The inverse-image opens cover: for `x ∈ W`, a covering open around `f(x)` pulls
   back to one containing `x`; intersect it with `W` to verify the covering-sieve
   condition. Apply `IsFiniteType.mk` to these finite local generators data.
The explicit local-lifting criterion is not needed: generating sections are defined
using categorical epimorphisms.
-/
theorem tensorPullback_isFiniteType (X Y : Scheme.{u}) (f : X ⟶ Y) (G : Y.Modules)
    [G.IsFiniteType] :
    ((tensorPullback f).obj G).IsFiniteType ∧
      ∀ (V : Y.Opens) (n : ℕ)
        (φ : SheafOfModules.free (R := Y.ringCatSheaf.over V) (ULift.{u} (Fin n)) ⟶
          G.over V),
        Epi φ →
          ∃ ψ : SheafOfModules.free
            (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj V))
            (ULift.{u} (Fin n)) ⟶
              ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj V),
            Epi ψ := by
  classical
  -- These instances are shared by the free modules and local generators below.
  have : ∀ V : Y.Opens, HasSheafify ((Opens.grothendieckTopology Y).over V)
      AddCommGrpCat.{u} := inferInstance
  have : ∀ V : Y.Opens,
      ((Opens.grothendieckTopology Y).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have : ∀ U : X.Opens, HasSheafify ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u} := inferInstance
  have : ∀ U : X.Opens,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have hlocal : ∀ (V : Y.Opens) (n : ℕ)
      (φ : SheafOfModules.free (R := Y.ringCatSheaf.over V) (ULift.{u} (Fin n)) ⟶
        G.over V), Epi φ → ∃ ψ : SheafOfModules.free
          (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj V))
          (ULift.{u} (Fin n)) ⟶
            ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj V),
        Epi ψ := by
    intro V n φ hφ
    have := hφ
    let U : X.Opens := (TopologicalSpace.Opens.map f.base).obj V
    let f' := f ∣_ V
    let F := (overEquiv V).functor ⋙ pullback f' ⋙ (overEquiv U).inverse
    have hF : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} F := by
      dsimp [F]
      infer_instance
    let ε : (pullback f').obj (SheafOfModules.unit V.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf := by
      have : IsIso (SheafOfModules.pullbackObjUnitToUnit f'.toRingCatSheafHom) :=
        inferInstance
      exact asIso (SheafOfModules.pullbackObjUnitToUnit f'.toRingCatSheafHom)
    let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
        F.obj (SheafOfModules.unit (Y.ringCatSheaf.over V)) :=
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
        (overEquiv U).inverse.mapIso
          (ε.symm ≪≫ (pullback f').mapIso
            (V.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm)
    let k : ((pullback f).obj G).restrict U.ι ≅
        (pullback f').obj (G.restrict V.ι) :=
      (restrictFunctorIsoPullback U.ι).app _ ≪≫ (pullbackComp U.ι f).app G ≪≫
        (pullbackCongr (morphismRestrict_ι f V).symm).app G ≪≫
        ((pullbackComp f' V.ι).symm).app G ≪≫
        (pullback f').mapIso ((restrictFunctorIsoPullback V.ι).app G).symm
    obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction f
    let c := adj.leftAdjointUniq (pullbackPushforwardAdjunction f)
    let e : F.obj (G.over V) ≅ ((tensorPullback f).obj G).over U :=
      (overEquiv U).inverse.mapIso
        ((pullback f').mapIso ((overFunctorEquiv V).app G) ≪≫ k.symm ≪≫
          (restrictFunctor U.ι).mapIso (c.app G).symm ≪≫
          ((overFunctorEquiv U).app ((tensorPullback f).obj G)).symm) ≪≫
        ((overEquiv U).unitIso.app _).symm
    refine ⟨(SheafOfModules.mapFreeIso F (ULift.{u} (Fin n)) η).hom ≫ F.map φ ≫ e.hom, ?_⟩
    infer_instance
  refine ⟨?_, hlocal⟩
  -- Assemble finite local generators over the inverse-image cover.
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  have := hq
  have hgen (i : q.I) : (q.generators i).IsFiniteType := hq.isFiniteType i
  have hex (i : q.I) : ∃ (n : ℕ)
      (ψ : SheafOfModules.free
        (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj (q.X i)))
        (ULift.{u} (Fin n)) ⟶
          ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj (q.X i))),
        Epi ψ := by
    let inst : Fintype (q.generators i).I := Fintype.ofFinite _
    let n := Fintype.card (q.generators i).I
    let φ : SheafOfModules.free
        (R := Y.ringCatSheaf.over (q.X i)) (ULift.{u} (Fin n)) ⟶ G.over (q.X i) :=
      (SheafOfModules.freeFunctor.mapIso
        (Equiv.toIso (Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm))).hom ≫
          (q.generators i).π
    have hφ : Epi φ := by
      dsimp [φ]
      infer_instance
    exact ⟨n, hlocal (q.X i) n φ hφ⟩
  choose n ψ hψ using hex
  let p : ((tensorPullback f).obj G).LocalGeneratorsData :=
    { I := q.I
      X := fun i ↦ (TopologicalSpace.Opens.map f.base).obj (q.X i)
      coversTop := fun W x hx ↦ by
        obtain ⟨V, a, ⟨i, ⟨b⟩⟩, hv⟩ := q.coversTop ⊤ (f.base x) (by trivial)
        let T := W ⊓ (TopologicalSpace.Opens.map f.base).obj V
        refine ⟨T, homOfLE inf_le_left, ⟨i, ⟨homOfLE ?_⟩⟩, ?_⟩
        · exact le_trans inf_le_right ((TopologicalSpace.Opens.map f.base).map b).le
        · exact ⟨hx, hv⟩
      generators := fun i ↦
        { I := ULift.{u} (Fin (n i))
          s := SheafOfModules.freeHomEquiv _ (ψ i)
          epi := by
            rw [Equiv.symm_apply_apply]
            exact hψ i } }
  have hp : p.IsFiniteType := by
    constructor
    intro i
    constructor
    exact inferInstanceAs (Finite (ULift.{u} (Fin (n i))))
  exact SheafOfModules.IsFiniteType.mk (M := (tensorPullback f).obj G) ⟨p, hp⟩


end AlgebraicGeometry.Scheme.Modules
