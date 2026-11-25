/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement

/-! # Two nonvanishing loci represented in a common tensor degree

Source: Stacks Project, Properties, proof of Lemma 01PY and Lemma 01PT.
(blueprint: lem-weil-pbc-nonvanishing-common-degree)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

private theorem nonvanishingLocus_app_one {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (a : MonoidalCategory.tensorUnit X.Modules ⟶ M) :
    nonvanishingLocus M (a.app ⊤ (unitSectionsEquiv ⊤ 1)) =
      ((Hom.zeroLocus a).support.compl : Set X) := by
  have h : homOfGlobalSection M (a.app ⊤ (unitSectionsEquiv ⊤ 1)) = a := by
    refine (SheafOfModules.unitHomEquiv M).injective (Subtype.ext (funext fun U ↦ ?_))
    change Hom.app (homOfGlobalSection M (a.app ⊤ (unitSectionsEquiv ⊤ 1)))
      U.unop (1 : Γ(X, U.unop)) = Hom.app a U.unop (1 : Γ(X, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (Hom.app a U.unop)
      (map_one (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom :)
  rw [nonvanishingLocus_eq_compl_support_zeroLocus, h]

private theorem nonvanishingLocus_power_transport {X : Scheme.{u}} {N M : X.Modules}
    [N.IsInvertible] [M.IsInvertible] (s : Γ(N, ⊤)) (k : ℕ) (hk : 0 < k)
    (e : N.tensorPow k ≅ M) :
    nonvanishingLocus M
      ((tensorPowSection (homOfGlobalSection N s) k ≫ e.hom).app ⊤
        (unitSectionsEquiv ⊤ 1)) = nonvanishingLocus N s := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible (N.tensorPow k)
  rw [nonvanishingLocus_app_one, nonvanishingLocus_eq_compl_support_zeroLocus]
  have he := Hom.zeroLocus_eq_of_arrowIso
    (tensorPowSection (homOfGlobalSection N s) k)
    (tensorPowSection (homOfGlobalSection N s) k ≫ e.hom)
    (Arrow.isoMk (Iso.refl _) e (by simp))
  rw [← he, compl_support_zeroLocus_tensorPowSection N _ hk]

/-- Two sections of positive tensor powers can be replaced by sections of one invertible
module without changing either nonvanishing locus.

Source: Stacks Project, Properties, proof of Lemma 01PY, second paragraph, and Lemma 01PT.
(blueprint: lem-weil-pbc-nonvanishing-common-degree)

Proof: put `M = L.tensorPow (p * q)`. Tensor powers of an invertible module are invertible.
Take the q-fold tensor power of s and the p-fold tensor power of t, and transport them
along the canonical tensor-power multiplication isomorphisms (and p*q = q*p).
At each point the fibres of all these modules are one-dimensional vector spaces over
the residue field. A positive tensor power of a vector in a one-dimensional vector
space is nonzero exactly when that vector is nonzero: choose a basis and use that a
positive power of a field element is zero exactly when that element is zero.
The tensor-germ and fibre comparison maps identify the values of these sections with
those tensor powers. The fibre maps of the canonical isomorphisms are isomorphisms,
so they preserve nonzero values. This proves both asserted equalities of loci.
-/
theorem exists_common_degree_nonvanishing {X : Scheme.{u}} (L : X.Modules)
    [L.IsInvertible] (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (s : (L.tensorPow p).val.presheaf.obj (Opposite.op ⊤))
    (t : (L.tensorPow q).val.presheaf.obj (Opposite.op ⊤)) :
    ∃ M : X.Modules, M.IsInvertible ∧
      ∃ s' t' : M.val.presheaf.obj (Opposite.op ⊤),
        nonvanishingLocus M s' = nonvanishingLocus (L.tensorPow p) s ∧
        nonvanishingLocus M t' = nonvanishingLocus (L.tensorPow q) t := by
  let M := L.tensorPow (p * q)
  let e : (L.tensorPow p).tensorPow q ≅ M := (L.tensorPowMulIso p q).symm
  let f : (L.tensorPow q).tensorPow p ≅ M :=
    (L.tensorPowMulIso q p).symm ≪≫ eqToIso (congrArg L.tensorPow (Nat.mul_comm q p))
  refine ⟨M, inferInstance,
    (tensorPowSection (homOfGlobalSection (L.tensorPow p) s) q ≫ e.hom).app ⊤
      (unitSectionsEquiv ⊤ 1),
    (tensorPowSection (homOfGlobalSection (L.tensorPow q) t) p ≫ f.hom).app ⊤
      (unitSectionsEquiv ⊤ 1), ?_, ?_⟩
  · exact nonvanishingLocus_power_transport s q hq e
  · exact nonvanishingLocus_power_transport t p hp f

end AlgebraicGeometry.Scheme.Modules
