/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomComplexGlobalCochains

/-!
# K-injectivity of the sheaf Hom complex

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.8 (Tag 0A96),
`sites-cohomology-lemma-RHom-from-K-flat-into-K-injective`
(blueprint: lem-pur-hom-kflat-into-kinjective).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 256 in
/-- The sheaf Hom complex from a K-flat complex into a K-injective complex is K-injective.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.8 (Tag 0A96)
(blueprint: lem-pur-hom-kflat-into-kinjective).

Proof: let `K` be any acyclic complex of sheaves of modules. K-flatness of `L`
(`def-pc-kflat-complex`) makes `Tot(K ⊗ L)` acyclic. The tensor-Hom isomorphism
`lem-sc-derived-hom-tensor-total` identifies `Hom(K, Hom(L, I))` with
`Hom(Tot(K ⊗ L), I)` as sheaf complexes. The proved global-cochain
comparison `lem-pur-hom-complex-global-cochains` turns a chain map into a
closed degree-zero global section. Transport it through the tensor-Hom
isomorphism. K-injectivity of `I` (`def-pur-kinjective-complex`) expresses the
resulting cocycle as the differential of a degree-minus-one cochain. Transport
that cochain back and use the comparison's differential compatibility to obtain
a homotopy to zero. Since `K` was arbitrary, the Hom complex is K-injective. -/
theorem isKInjective_homComplex_of_isKFlat
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    (L I : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hL : L.IsKFlatTensor) [I.IsKInjective] :
    (CategoryTheory.homComplex L I).IsKInjective := by
  classical
  let := SheafOfModules.monoidalCategory R
  refine ⟨fun {K} f hK ↦ ?_⟩
  let T := mapBifunctor K L (MonoidalCategory.curriedTensor _)
  have hT : T.Acyclic := hL K hK
  obtain ⟨e, _⟩ := homComplex_tensorTotal_iso R
  let t := e K L I
  obtain ⟨a, ha⟩ := homComplex_global_cochains R K (homComplex (R := R) L I)
  obtain ⟨b, hb⟩ := homComplex_global_cochains R T I
  let z := (a 0).symm (HomComplex.Cochain.ofHom f)
  have hz : z ≫ (homComplex (R := R) K (homComplex (R := R) L I)).d 0 1 = 0 := by
    apply (a 1).injective
    rw [ha 0 1 (by omega), map_zero]
    simp [z]
  have ht : HomComplex.δ 0 1 (b 0 (z ≫ t.hom.f 0)) = 0 := by
    rw [← hb 0 1 (by omega)]
    rw [Category.assoc, t.hom.comm 0 1, ← Category.assoc, hz,
      CategoryTheory.Limits.zero_comp, map_zero]
  let c : HomComplex.Cocycle T I 0 := HomComplex.Cocycle.mk _ 1 (by omega) ht
  obtain ⟨α, hα⟩ := IsKInjective.eq_δ_of_cocycle c hT (-1) (by omega)
  let s := (b (-1)).symm α ≫ t.inv.f (-1)
  have hs : s ≫ (homComplex (R := R) K (homComplex (R := R) L I)).d (-1) 0 = z := by
    apply (cancel_mono (t.hom.f 0)).mp
    rw [Category.assoc, ← t.hom.comm (-1) 0, ← Category.assoc]
    have hs' : s ≫ t.hom.f (-1) = (b (-1)).symm α := by
      dsimp only [s]
      rw [Category.assoc, ← HomologicalComplex.comp_f, t.inv_hom_id]
      exact Category.comp_id _
    rw [hs']
    apply (b 0).injective
    rw [hb (-1) 0 (by omega)]
    simpa [c] using hα
  refine ⟨(HomComplex.Cochain.equivHomotopy f 0).symm ⟨a (-1) s, ?_⟩⟩
  rw [HomComplex.Cochain.ofHom_zero, add_zero, ← ha (-1) 0 (by omega), hs]
  simp [z]

end CochainComplex
