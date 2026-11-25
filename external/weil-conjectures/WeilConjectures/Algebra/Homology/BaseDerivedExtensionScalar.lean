/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Scalar compatibility from a resolution counit

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-scalar).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

omit [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)] in
private theorem extendScalars_smul_id
    (M : ModuleCat.{max uR uB v} R) (r : R) :
    (extendScalars (algebraMap R B)).map (r • 𝟙 M) =
      algebraMap R B r • 𝟙 ((extendScalars (algebraMap R B)).obj M) := by
  apply ExtendScalars.hom_ext
  intro m
  simp only [ExtendScalars.map_tmul]
  let : Algebra R B := (algebraMap R B).toAlgebra
  change (1 : B) ⊗ₜ[R] (r • m) =
    (algebraMap R B r) • ((1 : B) ⊗ₜ[R] m)
  rw [TensorProduct.tmul_smul]
  rfl

private theorem homologyMap_smul_id
    {B : Type uB} [CommRing B] (E : CochainComplex (ModuleCat.{v} B) ℤ) (i : ℤ) (b : B) :
    HomologicalComplex.homologyMap (b • 𝟙 E) i = b • 𝟙 (E.homology i) := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor _ _ i).map (b • 𝟙 E) =
    b • 𝟙 (E.sc i) from rfl]
  simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Several localization and homology factorization functors occur in the scalar transport.
/-- Source: Stacks Project, Tag 06Y6, lemma-derived-base-change.
(blueprint: lem-pc-base-derived-extension-scalar).

Proof: First compute the scalar identity for ordinary extension of a complex P.
On a pure tensor b tensor p, extension of r times identity sends it to b tensor
(r times p), which equals (algebraMap R B r times b) tensor p. Tensor induction
proves equality of maps in each degree. The natural factorization isomorphisms
for homology through the homotopy quotient and derived localization transport
this equality to homology of Qh of ordinary extension. If the counit at P is
invertible, its naturality for r times identity, followed by homology, transports
the equality to H(L(Qh(P))). For arbitrary E choose P and s from hres.
The quasi-isomorphism s becomes invertible under Qh, L and homology. The equality
s composed with r times identity of E = r times identity of P composed with s
follows from R-linearity of s. Apply the composite functor, substitute the scalar
identity on P and cancel the image of s. Composition in ModuleCat B is B-linear,
so this gives precisely the asserted equality. Neither additivity nor a universal
property of L is needed. The proof works for r = 0 or 1, zero complexes and zero
coefficient rings, and does not assume that tensoring s itself is a quasi-isomorphism. -/
theorem baseDerivedExtension_scalar
    [(extendScalars.{_, _, max uR uB v} (algebraMap R B)).Additive]
    (L : DerivedCategory (ModuleCat.{max uR uB v} R) ⥤
      DerivedCategory (ModuleCat.{max uR uB v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hres : ∀ E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ,
      ∃ (P : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (s : P ⟶ E),
        QuasiIso s ∧ IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P))) :
    ∀ (i : ℤ) (E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (r : R),
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).map
        (L.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map (r • 𝟙 E)))) =
      algebraMap R B r • 𝟙
        ((DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).obj
          (L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj E))))  := by
  intro i E r
  let q := HomotopyCategory.quotient (ModuleCat.{max uR uB v} R) (.up ℤ)
  let qb := HomotopyCategory.quotient (ModuleCat.{max uR uB v} B) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i
  let F := extendScalars.{_, _, max uR uB v} (algebraMap R B)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let K := q ⋙ DerivedCategory.Qh ⋙ L ⋙ H
  have hord (P : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) :
      H.map (DerivedCategory.Qh.map (Fh.map (q.map (r • 𝟙 P)))) =
        algebraMap R B r • 𝟙 (H.obj (DerivedCategory.Qh.obj (Fh.obj (q.obj P)))) := by
    have hterm : Fc.map (r • 𝟙 P) = algebraMap R B r • 𝟙 (Fc.obj P) := by
      apply HomologicalComplex.Hom.ext
      funext j
      exact extendScalars_smul_id R B (P.X j) r
    change H.map (DerivedCategory.Qh.map (qb.map (Fc.map (r • 𝟙 P)))) =
      algebraMap R B r • 𝟙 (H.obj (DerivedCategory.Qh.obj (qb.obj (Fc.obj P))))
    let e := (DerivedCategory.homologyFunctorFactorsh
      (ModuleCat.{max uR uB v} B) i).app (qb.obj (Fc.obj P)) ≪≫
      (HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{max uR uB v} B) (.up ℤ) i).app (Fc.obj P)
    apply (cancel_mono e.hom).1
    have hn := (DerivedCategory.homologyFunctorFactorsh
      (ModuleCat.{max uR uB v} B) i).hom.naturality (qb.map (Fc.map (r • 𝟙 P)))
    have hn' := (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{max uR uB v} B) (.up ℤ) i).hom.naturality (Fc.map (r • 𝟙 P))
    change H.map (DerivedCategory.Qh.map (qb.map (Fc.map (r • 𝟙 P)))) ≫
      ((DerivedCategory.homologyFunctorFactorsh _ i).hom.app (qb.obj (Fc.obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) i).hom.app (Fc.obj P)) = _
    dsimp only [Functor.comp_map] at hn hn'
    rw [← Category.assoc, hn, Category.assoc, hn']
    change _ ≫ _ ≫ HomologicalComplex.homologyMap (Fc.map (r • 𝟙 P)) i = _
    rw [hterm, homologyMap_smul_id]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
    rfl
  have hmodel (P : CochainComplex (ModuleCat.{max uR uB v} R) ℤ)
      (hp : IsIso (ε.app (q.obj P))) :
      K.map (r • 𝟙 P) = algebraMap R B r • 𝟙 (K.obj P) := by
    let := hp
    apply (cancel_mono (H.map (ε.app (q.obj P)))).1
    have hn := congrArg (fun f ↦ H.map f) (ε.naturality (q.map (r • 𝟙 P)))
    change H.map (L.map (DerivedCategory.Qh.map (q.map (r • 𝟙 P)))) ≫
      H.map (ε.app (q.obj P)) = _
    simp only [Functor.comp_map, H.map_comp] at hn
    rw [hn, hord]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
    change algebraMap R B r • (H.map (ε.app (q.obj P)) ≫ 𝟙 _) = _
    rw [Category.comp_id]
  obtain ⟨P, s, hs, hp⟩ := hres E
  let := hs
  have hqs : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  let := hqs
  have hKs : IsIso (K.map s) := by
    change IsIso (H.map (L.map (DerivedCategory.Qh.map (q.map s))))
    infer_instance
  let := hKs
  change K.map (r • 𝟙 E) = algebraMap R B r • 𝟙 (K.obj E)
  apply (cancel_epi (K.map s)).1
  rw [← K.map_comp]
  have hcomm : s ≫ (r • 𝟙 E) = (r • 𝟙 P) ≫ s := by
    simp
  rw [hcomm, K.map_comp, hmodel P hp]
  simp

end ModuleCat
