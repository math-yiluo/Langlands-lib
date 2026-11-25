/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# A contractible affine extension usable over any base scheme

Source: Stacks Project, Tags 0983, 098H and 0990, as proved in
`WeilConjectures.RingTheory.ProEtale.WContractible` and
`WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every ring admits a singleton pro-etale affine cover whose source is weakly contractible
on every small pro-etale site to which its structural map belongs.

Source: Stacks Project, Tags 0983, 098H and 0990; the already proved source-library theorems
`exists_isWContractibleRing` and `Scheme.ProEt.isWeaklyContractible_of_iso`.
(auxiliary; not a blueprint node).

Proof: choose a faithfully flat ind-etale w-contractible extension D of A in the same
universe, using exists_isWContractibleRing. Ind-etaleness makes its spectrum map weakly
etale. Faithful flatness makes the map surjective, and a map between affine schemes is
quasi-compact, so its singleton is a pro-etale cover. For every weakly etale map Spec D to
X, isWeaklyContractible_of_iso applied to the identity of Spec D gives weak contractibility
on the full small site of X. A sheaf epimorphism is locally surjective, so evaluation at
this object is surjective. The extension theorem includes the zero ring; no nonempty or
nontrivial hypothesis is used. -/
theorem exists_affine_contractible_extension (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (φ : A →+* D),
      Presieve.singleton (Spec.map (CommRingCat.ofHom φ)) ∈
        proetalePrecoverage (Spec (CommRingCat.of A)) ∧
      (∀ (X : Scheme.{u}) (g : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale g]
        (F G : Sheaf (topology X) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op (ProEt.mk g)))) := by
  obtain ⟨D, hD, hAlg, hind, hff, hw⟩ := exists_isWContractibleRing A
  let φ : A →+* D := algebraMap A D
  have hwp : WeaklyEtale (Spec.map (CommRingCat.ofHom φ)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 hind)
  have hsp : Surjective (Spec.map (CommRingCat.ofHom φ)) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom φ)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 hff)).2
  refine ⟨D, hD, φ, Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) hwp, ?_⟩
  intro X g hg F G e he
  have hV : (topology X).IsWeaklyContractible.{u + 1} (ProEt.mk g) :=
    isWeaklyContractible_of_iso (R := CommRingCat.of D) (Iso.refl _)
  exact hV e ((Sheaf.isLocallySurjective_iff_epi e).2 he)

end AlgebraicGeometry.Scheme.ProEt
