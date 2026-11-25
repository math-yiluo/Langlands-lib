/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Injective sheaves have surjective restriction maps

Source: Stacks Project, Cohomology, Lemma 01EA
(blueprint: lem-sc-ringed-space-injective-restriction-surjective).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

noncomputable section
namespace AlgebraicGeometry

/-- Injective sheaves of modules have surjective restriction maps on sections.
Source: Stacks Project, Cohomology, Lemma 01EA
(blueprint: lem-sc-ringed-space-injective-restriction-surjective).
Proof: let `j_!O_U` be the module sheafification of the presheaf equal to `O_X` on opens
inside `U` and `0` elsewhere (def-weil-presheaf-modules-sheafification); its universal
property gives `Hom(j_!O_U, F) ≅ F(U)`, `ψ ↦ ψ(1)`, and likewise for `U'`. The map
`α : j'_!O_{U'} ⟶ j_!O_U` induced by the identity on opens inside `U'` is injective on every
stalk, hence a monomorphism. As `I` is injective, precomposition with `α` is surjective, and
under the bijections it is the restriction `I(U) → I(U')`. For the second clause, given
`c ∈ I(V ⊓ W)` lift it to `a ∈ I(V)` along `V ⊓ W ≤ V` and take `b = 0`; then
`(a, b) ↦ c`.
-/
theorem injective_restriction_surjective (X : RingedSpace.{u})
    {U' U : Opens X} (hU : U' ≤ U)
    (I : SheafOfModules.{u} (moduleRings X))
    [Injective I] :
    Function.Surjective (fun s : I.val.obj (Opposite.op U) =>
      (I.val.map (homOfLE hU).op).hom s) ∧
      ∀ (V W : Opens X), Function.Surjective
        (fun p : I.val.obj (Opposite.op V) × I.val.obj (Opposite.op W) =>
          (show I.val.obj (Opposite.op (V ⊓ W)) from
            (I.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op).hom p.1) -
          (show I.val.obj (Opposite.op (V ⊓ W)) from
            (I.val.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op).hom p.2)) := by
  let R := moduleRings X
  -- On the opens poset, the free Yoneda module is rank one inside V and zero outside.
  let P := yoneda ⋙ PresheafOfModules.free R.obj
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let A := P ⋙ S
  let e (V : Opens X) :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv (P.obj V) I).trans
      PresheafOfModules.freeYonedaEquiv
  have hn (V' V : Opens X) (h : V' ≤ V) (f : A.obj V ⟶ I) :
      e V' (A.map (homOfLE h) ≫ f) =
        (I.val.map (homOfLE h).op).hom (e V f) := by
    dsimp [e, A, P, Equiv.trans_apply]
    erw [Adjunction.homEquiv_naturality_left]
    change yonedaEquiv (PresheafOfModules.freeHomEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map (homOfLE h)) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ I f)) = _
    erw [← PresheafOfModules.freeAdjunction_homEquiv,
      Adjunction.homEquiv_naturality_left]
    exact (yonedaEquiv_naturality _ (homOfLE h)).symm
  have hs (V' V : Opens X) (h : V' ≤ V) :
      Function.Surjective (fun s : I.val.obj (Opposite.op V) ↦
        (I.val.map (homOfLE h).op).hom s) := by
    intro s
    -- Sectionwise injectivity and left exact sheafification avoid the stalk argument.
    have hm : Mono (P.map (homOfLE h)) := by
      apply PresheafOfModules.mono_of_injective
      intro T
      change Function.Injective (Finsupp.mapDomain _)
      apply Finsupp.mapDomain_injective
      intro a b _
      change T.unop ⟶ V' at a b
      exact Subsingleton.elim a b
    have : Mono (A.map (homOfLE h)) := by
      dsimp [A]
      infer_instance
    obtain ⟨f, hf⟩ := Injective.factors ((e V').symm s) (A.map (homOfLE h))
    refine ⟨e V f, ?_⟩
    exact (hn V' V h f).symm.trans
      (congrArg (e V') hf |>.trans ((e V').apply_symm_apply s))
  refine ⟨hs U' U hU, ?_⟩
  intro V W c
  obtain ⟨a, ha⟩ := hs (V ⊓ W) V inf_le_left c
  refine ⟨(a, 0), ?_⟩
  simpa using ha

end AlgebraicGeometry
