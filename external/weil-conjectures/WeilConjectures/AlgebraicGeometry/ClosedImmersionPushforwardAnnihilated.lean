/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherent modules annihilated by a closed subscheme's ideal

Source: Stacks Project, Morphisms, Lemma 01QY, and Modules, Lemmas 08KS,
01BG, and 01B6 (blueprint: lem-weil-pbc-closed-immersion-pushforward-annihilated).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward from a closed subscheme preserves quasi-coherence and is annihilated by
its ideal. A quasi-coherent module annihilated by that ideal has quasi-coherent pullback
and invertible canonical unit, and finite type passes to that pullback.
Here `i.ker.idealOfOpens V` is the ideal on every open, not only affine opens.
Source: Stacks Project, Morphisms, Lemma 01QY, and Modules, Lemmas 08KS, 01BG, and 01B6
(blueprint: lem-weil-pbc-closed-immersion-pushforward-annihilated).
Proof:
1. A closed immersion is affine. Apply `affinePushforward_baseChange` to the identity
base-change square for quasi-coherence of the pushforward.
2. Ideal membership makes the section zero under the subscheme inclusion; the image
factorization makes it zero under `i.app V`. Restriction of scalars gives annihilation.
3. Uniqueness of left adjoints identifies tensor pullback with Mathlib pullback, whose
quasi-coherence instance is already proved.
4. The annihilation hypothesis makes ideal multiplication `I ⊗ F ⟶ F` zero: use the
sheafification adjunction and tensor induction to check this on pure tensors of sections.
5. `closedImmersion_unit_quotient` gives an epimorphic unit with kernel the image of
this multiplication. That image inclusion is zero, so the kernel universal property
makes the unit mono. In the abelian module category it is therefore an isomorphism.
6. Compare the adjunction used by the quotient lemma with the adjunction in this
statement via `unit_leftAdjointUniq_hom_app`; invertibility transfers to the stated unit.
7. Apply the finite-type conjunct of `tensorPullback_isFiniteType`. -/
theorem closedImmersion_pushforward_annihilated
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (∀ (G : Z.Modules) [G.IsQuasicoherent],
      ((pushforward i).obj G).IsQuasicoherent ∧
        ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
          ∀ s : Γ((pushforward i).obj G, V), a • s = 0) ∧
      ∀ (F : X.Modules) [F.IsQuasicoherent],
        (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
          ∀ s : Γ(F, V), a • s = 0) →
          ((tensorPullback i).obj F).IsQuasicoherent ∧
            IsIso ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F) ∧
              (F.IsFiniteType → ((tensorPullback i).obj F).IsFiniteType) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  open CategoryTheory.Limits MonoidalCategory Opposite in
  open scoped TensorProduct in
    constructor
    · intro G _
      constructor
      · exact (affinePushforward_baseChange i i (𝟙 X) (𝟙 Z) .of_id_fst G).1
      · intro V a ha s
        change G.val.obj (.op (i ⁻¹ᵁ V)) at s
        change (i.app V).hom a • s = (0 : G.val.obj (.op (i ⁻¹ᵁ V)))
        have hz : (i.app V).hom a = 0 := by
          have hz := (Scheme.IdealSheafData.mem_idealOfOpens_iff i.ker).mp ha
          rw [← i.toImage_imageι, Scheme.Hom.comp_app]
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hz, map_zero]
        rw [hz, zero_smul]
    · intro F _ hF
      refine ⟨?_, ?_, ?_⟩
      · let e : tensorPullback i ≅ pullback i :=
          (Classical.choose (exists_tensorPullbackAdjunction i)).leftAdjointUniq
            (pullbackPushforwardAdjunction i)
        exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso (e.app F).symm
          (inferInstance : ((pullback i).obj F).IsQuasicoherent)
      · -- The unit/quotient lemma packages the stalk calculation from the source proof.
        let μ : i.ker.toModules ⊗ F ⟶ F := i.ker.toModulesι ▷ F ≫ (λ_ F).hom
        have hμ : μ = 0 := by
          let adj := sheafificationAdjunction X
          apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification i.ker.toModules F).inv).mp
          apply (adj.homEquiv (i.ker.toModules.val ⊗ F.val) F).injective
          rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
          apply PresheafOfModules.hom_ext
          intro U
          ext t
          change μ.val.app U
            ((SheafOfModules.tensorObjIsoSheafification i.ker.toModules F).inv.val.app U
              (((adj.unit.app (i.ker.toModules.val ⊗ F.val)).app U) t)) = _
          induction t using TensorProduct.inductionOn with
          | add t s ht hs => simp only [map_add, ht, hs]
          | tmul a s =>
            change μ.app U.unop (tmulSection a s) = 0
            dsimp only [μ]
            rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
            erw [leftUnitor_hom_app_tmulSection']
            exact hF U.unop (i.ker.toModulesι.app U.unop a)
              ((i.ker.range_toModulesι_app_eq_idealOfOpens U.unop).subset ⟨a, rfl⟩) s
        obtain ⟨_, hη', _⟩ := closedImmersion_unit_quotient i
        let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
        have hη := hη' F
        have : Epi (adj.unit.app F) := hη.1
        obtain ⟨w, ⟨hk⟩⟩ := hη.2.1
        have hι : image.ι μ = 0 := by
          apply (cancel_epi (factorThruImage μ)).mp
          simp only [image.fac, comp_zero, hμ]
        have : Mono (adj.unit.app F) := by
          rw [Preadditive.mono_iff_cancel_zero]
          intro T g hg
          obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk g hg
          change l ≫ image.ι μ = g at hl
          exact hl.symm.trans ((congrArg (fun k ↦ l ≫ k) hι).trans (comp_zero))
        have : IsIso (adj.unit.app F) := isIso_of_mono_of_epi _
        let adj' := Classical.choose (exists_tensorPullbackAdjunction i)
        rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' F]
        infer_instance
      · intro hfin
        let : F.IsFiniteType := hfin
        exact (tensorPullback_isFiniteType Z X i F).1

end AlgebraicGeometry.Scheme.Modules
