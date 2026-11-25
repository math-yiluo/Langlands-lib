/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Localization of Hom into successive module direct images

Source: Stacks Project, Cohomology, Tags 079W, 0D5S, and 0D5T.
(blueprint: lem-pc-ringed-space-kflat-direct-image-hom-localization).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-- Localization computes maps from a K-flat complex into the successive direct
image of a K-injective complex, without requiring that direct image be K-injective.
Source: Stacks Project, Cohomology, lemma-adjoint (079W),
lemma-derived-pullback-composition (0D5S), and
lemma-derived-pushforward-composition (0D5T).
(blueprint: lem-pc-ringed-space-kflat-direct-image-hom-localization).

Proof: denote successive tensor pullback by P and its right adjoint by F.
A derived map QK to QFI is a roof K ←s K' →a FI in the homotopy category.
Resolve K' by a K-flat K'' and precompose both roof arrows. Now s has K-flat
endpoints. Pullback preserves K-flatness and computes its derived functor there,
so Q(Ps) is invertible. Adjunction sends a to b : P K'' → I. The derived map
inv(Q(Ps)) ≫ Qb comes from a unique homotopy class c : PK → I, since I is
K-injective. Faithfulness into I gives Ps ≫ c = b. Naturality of the underived
adjunction gives s ≫ adjunct(c) = a, so the original roof is Q(adjunct(c)).
This proves surjectivity. For injectivity, if Qu = Qv, the right calculus of
fractions gives a quasi-isomorphism s : K' → K with s ≫ u = s ≫ v. Resolve K'
by a K-flat K'' again. Naturality of adjunction gives Ps ≫ adjunct⁻¹(u) =
Ps ≫ adjunct⁻¹(v). Q(Ps) is invertible, so these adjuncts have equal localized
maps; K-injective faithfulness gives equality already in the homotopy category.
The underived adjunction is a bijection, hence u = v. Identity and zero complexes
satisfy the same argument; no flatness or boundedness of f or g is used. -/
theorem moduleDirectImage_kFlat_hom_localization_bijective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ) (hK : K.IsKFlatTensor) :
    Function.Bijective (DerivedCategory.Qh.map :
      (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ⟶
        ((moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) → _) := by
  obtain ⟨G, adj, L, adj', α, hα, hη⟩ := exists_pasted_tensorPullback_adjunction f g
  let Q := DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z))
  let QX := DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X))
  let q := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings Z)) (.up ℤ)
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Z)) (.up ℤ)
  let K₀ := q.obj K
  let I₀ := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  have hres : ∀ T : HomotopyCategory (SheafOfModules.{u} (moduleRings Z)) (.up ℤ),
      ∃ (A : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ),
        A.IsKFlatTensor ∧ ∃ z : q.obj A ⟶ T, IsIso (Q.map z) := by
    intro T
    obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
    obtain ⟨A, z, hA, _, hz, _⟩ := CochainComplex.exists_isKFlatResolution T
    let : QuasiIso z := hz
    refine ⟨A, hA, q.map z, Localization.inverts Q W _ ?_⟩
    dsimp [W, q]
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hz
  have hinv : ∀ (A B : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ),
      A.IsKFlatTensor → B.IsKFlatTensor → ∀ s : q.obj A ⟶ q.obj B,
        IsIso (Q.map s) → IsIso (QX.map (G.map s)) := by
    intro A B hA hB s hs
    let := hs
    let : IsIso (α.app (q.obj A)) := hα A hA
    let : IsIso (α.app (q.obj B)) := hα B hB
    have hn := α.naturality s
    dsimp at hn
    have : IsIso (α.app (q.obj A) ≫ QX.map (G.map s)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (α.app (q.obj A)) (QX.map (G.map s))
  constructor
  · intro a b hab
    obtain ⟨T, s, hs, heq⟩ := (W.map_eq_iff_precomp Q a b).mp hab
    obtain ⟨A, hA, z, hz⟩ := hres T
    let := hz
    let : IsIso (Q.map s) := Localization.inverts Q W s hs
    let t := z ≫ s
    have ht : IsIso (Q.map t) := by dsimp [t]; rw [Functor.map_comp]; infer_instance
    let : IsIso (QX.map (G.map t)) := hinv A K hA hK t ht
    have heq' : t ≫ a = t ≫ b := by dsimp [t]; rw [Category.assoc, heq, Category.assoc]
    apply (adj.homEquiv K₀ I₀).symm.injective
    apply (CochainComplex.IsKInjective.Qh_map_bijective (G.obj K₀) I).injective
    apply (cancel_epi (QX.map (G.map t))).mp
    rw [← QX.map_comp, ← QX.map_comp,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm, heq']
  · intro a
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q W a
    obtain ⟨T, s, hs, b, rfl⟩ := φ.cases
    let : IsIso (Q.map s) := Localization.inverts Q W s hs
    obtain ⟨A, hA, z, hz⟩ := hres T
    let := hz
    let t := z ≫ s
    let b' := z ≫ b
    have ht : IsIso (Q.map t) := by dsimp [t]; rw [Functor.map_comp]; infer_instance
    let := ht
    let : IsIso (QX.map (G.map t)) := hinv A K hA hK t ht
    let c := (adj.homEquiv (q.obj A) I₀).symm b'
    obtain ⟨d, hd⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (G.obj K₀) I).surjective
      (inv (QX.map (G.map t)) ≫ QX.map c)
    have htd : G.map t ≫ d = c := by
      apply (CochainComplex.IsKInjective.Qh_map_bijective (G.obj (q.obj A)) I).injective
      rw [Functor.map_comp, hd, IsIso.hom_inv_id_assoc]
    have hta : t ≫ (adj.homEquiv K₀ I₀) d = b' := by
      rw [← adj.homEquiv_naturality_left, htd]
      exact (adj.homEquiv (q.obj A) I₀).apply_symm_apply b'
    refine ⟨(adj.homEquiv K₀ I₀) d, ?_⟩
    apply (cancel_epi (Q.map t)).mp
    rw [← Q.map_comp, hta]
    rw [hφ]
    dsimp [t, b', MorphismProperty.RightFraction.map]
    simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.RingedSpace
