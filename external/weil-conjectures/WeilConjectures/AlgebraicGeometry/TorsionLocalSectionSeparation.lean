/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExtZero
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The map to H and the normalized formal quotient maps jointly separate local sections.
Source: Stacks Project, Tag 0889(1), omitted uniqueness verification, made explicit
by the Artin--Rees argument of `coherentMap_torsion_completion_ext_zero`.
(blueprint: lem-weil-pbc-torsion-local-section-separation).

Proof: Fix i and a positive annihilation bound for the kernel of ai. Artin--Rees
provides n such that ker(ai) maps monomorphically to Fi/J^(n+1)Fi. Evaluate this
monomorphism on any open of Ui; evaluation preserves kernels and monomorphisms.
Transfer through li and overFunctorEquiv. If x and y have the same b-image, x-y
lies in this kernel. By hqi, equality of their q-images at op n says its image
in the quotient is zero, since beta is invertible. Monomorphy gives x-y=0.
The open on Ui corresponding to W is arbitrary; no affineness assumption is used.
When J=0 the first quotient detects sections. When J=1 the torsion kernel is
zero and b detects sections. Empty opens have only the zero section.
-/
theorem torsion_local_section_separation
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (ι : Type u) (U : ι → X.Opens)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (hbound : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel (ai i).hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel (ai i).hom)))
    (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (hbi : (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom))
    (hqi : (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n))
    (i : ι) (W : X.Opens) (hi : W ≤ U i)
    (x y : (Li i).val.obj (op (Over.mk (homOfLE hi))))
    (hb : (bi i).val.app (op (Over.mk (homOfLE hi))) x =
      (bi i).val.app (op (Over.mk (homOfLE hi))) y)
    (hq : ∀ n : ℕᵒᵖ, (qi i n).val.app (op (Over.mk (homOfLE hi))) x =
      (qi i n).val.app (op (Over.mk (homOfLE hi))) y) : x = y := by
  have : IsLocallyNoetherian (U i).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U i).ι
  have : NoetherianSpace X := inferInstance
  have : NoetherianSpace (U i) :=
    NoetherianSpace.set (α := X) (U i : Set X)
  have : CompactSpace (U i) := NoetherianSpace.compactSpace (U i)
  have : IsNoetherian (U i).toScheme := ⟨⟩
  obtain ⟨s, hs, hk, hc⟩ := hbound i
  obtain ⟨n, hn⟩ := coherentMap_torsion_completion_ext_zero (J.comap (U i).ι)
    (Fi i) (Hlocal i) (ai i) ⟨s, hs, hk⟩
  let E := (Scheme.Modules.overEquiv (U i)).functor
  have : E.PreservesZeroMorphisms := inferInstance
  have : IsIso (li i).hom := (li i).isIso_hom
  have : IsIso ((βi i).inv.app (op n)) := ((βi i).app (op n)).isIso_inv
  let p := formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Fi i).obj
  have : HasBinaryBiproduct (H.obj.over (U i)) ((N.obj.obj (op n)).over (U i)) :=
    inferInstance
  let c := biprod.lift (bi i) (qi i (op n))
  have : Mono c := by
    apply Preadditive.mono_of_cancel_zero
    intro P d hd
    have hdb : d ≫ bi i = 0 := by
      have he := congrArg (fun z => z ≫ biprod.fst) hd
      simpa [c, Category.assoc] using he
    have hdq : d ≫ qi i (op n) = 0 := by
      have he := congrArg (fun z => z ≫ biprod.snd) hd
      simpa [c, Category.assoc] using he
    let v := E.map d ≫ (li i).hom
    have hva : v ≫ (ai i).hom = 0 := by
      dsimp [v]
      rw [Category.assoc, ← hbi i, ← Category.assoc, ← Category.assoc,
        ← E.map_comp, hdb, E.map_zero, zero_comp, zero_comp]
    have hvp : v ≫ p = 0 := by
      apply (cancel_mono ((βi i).inv.app (op n))).mp
      rw [zero_comp]
      dsimp [v, p]
      rw [Category.assoc, Category.assoc, ← hqi i (op n), ← Category.assoc,
        ← E.map_comp, hdq, E.map_zero, zero_comp]
    let l := kernel.lift (ai i).hom v hva
    have : Mono (kernel.ι (ai i).hom ≫ p) := hn
    have hl : l = 0 := by
      apply (cancel_mono (kernel.ι (ai i).hom ≫ p)).mp
      rw [zero_comp, ← Category.assoc, kernel.lift_ι]
      exact hvp
    have hv : v = 0 := by
      rw [← kernel.lift_ι (ai i).hom v hva, ← show l = kernel.lift _ v hva from rfl,
        hl, zero_comp]
    apply E.map_injective
    rw [E.map_zero]
    apply (cancel_mono (li i).hom).mp
    simpa [v] using hv
  let ev := SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (U i))
    (op (Over.mk (homOfLE hi)))
  have : Mono (ev.map c) := inferInstance
  apply ((ModuleCat.mono_iff_injective (ev.map c)).mp inferInstance)
  have hb' : ev.map c ≫ ev.map biprod.fst = ev.map (bi i) := by
    rw [← ev.map_comp]
    simp [c]
  have hq' : ev.map c ≫ ev.map biprod.snd = ev.map (qi i (op n)) := by
    rw [← ev.map_comp]
    simp [c]
  have hbx : ev.map biprod.fst (ev.map c x) = ev.map biprod.fst (ev.map c y) :=
    (ConcreteCategory.congr_hom hb' x).trans
      (hb.trans (ConcreteCategory.congr_hom hb' y).symm)
  have hqx : ev.map biprod.snd (ev.map c x) = ev.map biprod.snd (ev.map c y) :=
    (ConcreteCategory.congr_hom hq' x).trans
      ((hq (op n)).trans (ConcreteCategory.congr_hom hq' y).symm)
  have ht : ev.map (biprod.fst (X := H.obj.over (U i))) ≫ ev.map biprod.inl +
      ev.map (biprod.snd (Y := (N.obj.obj (op n)).over (U i))) ≫
        ev.map biprod.inr = 𝟙 _ := by
    change ev.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) = ev.map (𝟙 _)
    exact congrArg (fun z => ev.map z) (biprod.total (X := H.obj.over (U i))
      (Y := (N.obj.obj (op n)).over (U i)))
  have hx := ConcreteCategory.congr_hom ht (ev.map c x)
  have hy := ConcreteCategory.congr_hom ht (ev.map c y)
  change ev.map biprod.inl (ev.map biprod.fst (ev.map c x)) +
    ev.map biprod.inr (ev.map biprod.snd (ev.map c x)) = ev.map c x at hx
  change ev.map biprod.inl (ev.map biprod.fst (ev.map c y)) +
    ev.map biprod.inr (ev.map biprod.snd (ev.map c y)) = ev.map c y at hy
  rw [← hx, ← hy, hbx, hqx]

end AlgebraicGeometry
