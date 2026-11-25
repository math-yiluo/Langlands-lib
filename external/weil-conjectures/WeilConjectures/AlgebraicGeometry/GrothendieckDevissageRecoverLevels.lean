/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsion
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExt
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageCompletedComparison

/-! # Recovering the original levels after second-ideal algebraization

Source: Stacks Project, Tag 088A, final paragraph
(blueprint: lem-weil-pbc-devissage-recover-levels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem torsionTriple_comparison_iso
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (F G H : CoherentModules X) (a : F ⟶ H) (b : G ⟶ H)
    (η : (completion X K).obj F ≅ (completion X K).obj G)
    (hη : η.hom ≫ (completion X K).map b = (completion X K).map a)
    (ha : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel a.hom)))
    (hb : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel b.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel b.hom)))
    (hformal : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (((completion X K).map b).hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (((completion X K).map b).hom.app (op e))))) :
    ∃ φ : F ≅ G, φ.hom ≫ b = a ∧ (completion X K).map φ.hom = η.hom := by
  obtain ⟨L, c, ε, _, _, huniq⟩ := grothendieckExistenceEasy_torsionTriple K H
    ((completion X K).obj G) ((completion X K).map b) hformal
  have hη' : (completion X K).map b = η.inv ≫ (completion X K).map a := by
    rw [← hη, Iso.inv_hom_id_assoc]
  obtain ⟨γ, hγ, _⟩ := huniq F a η.symm hη' ha
  obtain ⟨ζ, hζ, _⟩ := huniq G b (Iso.refl _) (by simp) hb
  refine ⟨γ.symm ≪≫ ζ, ?_, ?_⟩
  · change γ.inv ≫ ζ.hom ≫ b = a
    rw [hζ.1, ← hγ.1, Iso.inv_hom_id_assoc]
  · change (completion X K).map (γ.inv ≫ ζ.hom) = η.hom
    rw [Functor.map_comp]
    apply (cancel_epi ((completion X K).map γ.hom)).1
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, (completion X K).map_id,
      Category.id_comp]
    apply (cancel_epi ε.hom).1
    rw [← Category.assoc, hγ.2]
    simpa using hζ.2

set_option backward.isDefEq.respectTransparency false in
/-- Reduction of a torsion-controlled K-algebraization recovers the original I-levels.
Here sigma is an isomorphism of doubly indexed diagrams, theta is the canonical quotient
interchange, and the comparison square relates the maps to H. No completion equivalence
on a thickening is assumed at this stage: that work is encoded in the supplied diagram.

Source: Stacks Project, Tag 088A, final paragraph, and Tag 0889, part (1), uniqueness
(blueprint: lem-weil-pbc-devissage-recover-levels).

Proof:
Fix a positive I-level n. Evaluation of sigma identifies the K-completion of M_n with
the I^n-quotient of N. Reduce beta modulo I^n and commute the two quotient operations,
using their universal cokernel descriptions. The canonical theta and the comparison
square identify the resulting completion map with the completion of alpha_n.
Thus F/I^n F, the reduction of a, and this comparison form an algebraization triple
for alpha_n completed along K. Reduction of the torsion-controlled map a has kernel
and cokernel killed by K^(2s), by the reduction lemma in Remark 0888. The given bound
on alpha_n makes M_n with alpha_n another torsion-controlled triple for the same map.
Uniqueness in the torsion-controlled version of Tag 0889 gives the desired level
isomorphism. For a transition from a later I-level to an earlier one, both composites
have the same comparison to H and the same K-completion. Their difference lands in
the power-torsion kernel of alpha at the target level. Exactness of completion on
finite affine modules and stabilization of that torsion kernel detect the difference,
so the composites agree. Hence the level isomorphisms are natural in n.
The torsion conditions are on the actual coherent maps; completion alone would not
control components away from V(K). All levels remain positive. The quotient comparison,
coherent reduction bound and map-detection step are separate named intermediate theorems.
-/
theorem grothendieckDevissage_recoverLevels
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (H : CoherentModules X)
    (α : M ⟶ (completion X I).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n)))))
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅ (M.obj ⋙ formalCompletionFunctor K).flip)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (hθ : ∀ e n : ℕ,
      formalModuleQuotientπ K (e + 1) H.obj ≫
        formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
        (θ.hom.app (op e)).app (op n) =
      formalModuleQuotientπ I (n + 1) H.obj ≫
        formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj))
    (hsquare : ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
        formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
      formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
        (θ.hom.app (op e)).app (op n))
    (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X K).obj F)
    (hβ : δ = β.hom ≫ (completion X K).map a)
    (ha : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel a.hom))) :
    ∃ φ : ∀ n : ℕᵒᵖ, ((completion X I).obj F).obj.obj n ≅ M.obj.obj n,
      ∀ (n m : ℕᵒᵖ) (f : n ⟶ m),
        ((completion X I).obj F).obj.map f ≫ (φ m).hom =
          (φ n).hom ≫ M.obj.map f := by
  classical
  let Fn (n : ℕᵒᵖ) : CoherentModules X :=
    ⟨((completion X I).obj F).obj.obj n, ((completion X I).obj F).property.1 n.unop⟩
  let Mn (n : ℕᵒᵖ) : CoherentModules X := ⟨M.obj.obj n, M.property.1 n.unop⟩
  let Hn (n : ℕᵒᵖ) : CoherentModules X :=
    ⟨((completion X I).obj H).obj.obj n, ((completion X I).obj H).property.1 n.unop⟩
  let an (n : ℕᵒᵖ) : Fn n ⟶ Hn n :=
    ObjectProperty.homMk (((completion X I).map a).hom.app n)
  let bn (n : ℕᵒᵖ) : Mn n ⟶ Hn n := ObjectProperty.homMk (α.hom.app n)
  obtain ⟨Ξ, hΞ⟩ := grothendieckDevissage_completedComparison I K M H α
    N δ σ θ hθ hsquare F a β hβ
  obtain ⟨s, hs, haker, hacoker⟩ := ha
  obtain ⟨t, ht, hα⟩ := htorsion
  have han (n : ℕᵒᵖ) : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel (an n).hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (an n).hom)) := by
    exact ⟨2 * s, by omega,
      coherentMap_reduction_torsion I K F H a s hs haker hacoker n.unop⟩
  have hbn (n : ℕᵒᵖ) : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel (bn n).hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (bn n).hom)) := ⟨t, ht, hα n.unop⟩
  have hex (n : ℕᵒᵖ) : ∃ φ : Fn n ≅ Mn n,
      φ.hom ≫ bn n = an n ∧
        (completion X K).map φ.hom =
          (ObjectProperty.isoMk (IsCoherentFormalModule K) (Ξ.app n)).hom := by
    apply torsionTriple_comparison_iso K (Fn n) (Mn n) (Hn n) (an n) (bn n)
      (ObjectProperty.isoMk (IsCoherentFormalModule K) (Ξ.app n))
    · apply ObjectProperty.hom_ext
      exact hΞ n
    · exact han n
    · exact hbn n
    · exact ⟨2 * t, by omega, coherentMap_reduction_torsion K K (Mn n) (Hn n)
        (bn n) t ht (hα n.unop).1 (hα n.unop).2⟩
  choose φ hφ using hex
  refine ⟨fun n ↦ (ObjectProperty.ι _).mapIso (φ n), ?_⟩
  intro n m f
  let p : Fn n ⟶ Fn m := ObjectProperty.homMk (((completion X I).obj F).obj.map f)
  let q : Mn n ⟶ Mn m := ObjectProperty.homMk (M.obj.map f)
  have heq : p ≫ (φ m).hom = (φ n).hom ≫ q := by
    apply coherentMap_torsion_completion_ext K (Fn n) (Mn m) (Hn m) (bn m)
      ⟨t, ht, (hα m.unop).1⟩
    · apply ObjectProperty.hom_ext
      change ((completion X I).obj F).obj.map f ≫ (φ m).hom.hom ≫ α.hom.app m =
        (φ n).hom.hom ≫ M.obj.map f ≫ α.hom.app m
      have hm := congrArg (fun z ↦ z.hom) (hφ m).1
      have hn := congrArg (fun z ↦ z.hom) (hφ n).1
      change (φ m).hom.hom ≫ α.hom.app m =
        ((completion X I).map a).hom.app m at hm
      change (φ n).hom.hom ≫ α.hom.app n =
        ((completion X I).map a).hom.app n at hn
      rw [hm, α.hom.naturality, ← Category.assoc, hn]
      exact ((completion X I).map a).hom.naturality f
    · rw [Functor.map_comp, Functor.map_comp, (hφ m).2, (hφ n).2]
      apply ObjectProperty.hom_ext
      exact Ξ.hom.naturality f
  exact congrArg (fun z ↦ z.hom) heq

end AlgebraicGeometry
