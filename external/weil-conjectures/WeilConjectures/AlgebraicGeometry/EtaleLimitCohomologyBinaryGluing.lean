/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyStageContinuity
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import WeilConjectures.AlgebraicGeometry.EtaleLimitBinaryEventualZero
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Two-open gluing of continuity

Source: Stacks Project, Tags 09YQ (theorem-colimit) and 0A50 (lemma-mayer-vietoris).
(blueprint: lem-weil-pbc-etale-limit-cohomology-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Continuity glues across a union of two quasi-compact opens.

Source: Stacks Project, Tags 09YQ (theorem-colimit) and 0A50 (lemma-mayer-vietoris);
step 2 of lem-weil-pbc-etale-limit-cohomology-qcqs-gluing.
(blueprint: lem-weil-pbc-etale-limit-cohomology-binary-gluing).

Proof:
1. For a system with a stage isomorphic to U union V, pass to the cofinal tail
   above that stage and transport U and V through the specified isomorphism.
   Restrict the scheme cone and every stage sheaf to inverse images of the opens.
   The restricted scheme cones are limits and the maps remain affine. The opens
   are quasi-compact, and quasi-separatedness is inherited from the stage.
   Inverse image preserves the supplied sheaf colimit. Inverse-image composition
   and cohomology pullback functoriality identify all comparison legs. Apply the
   three hypotheses to these restricted systems, in all degrees.
2. Mayer-Vietoris and its naturality in sheaves and scheme pullback supply a map
   between the colimit of the stage exact sequences and the sequence on the limit.
   Filtered abelian-group colimits preserve exactness and finite products. For
   positive p use the segment H^(p-1)(U)+H^(p-1)(V), H^(p-1)(U intersection V),
   H^p(U union V), H^p(U)+H^p(V), H^p(U intersection V). The four outer comparison
   maps are isomorphisms by the hypotheses, so the five lemma gives the middle one.
   In degree zero use the initial zero terms; no negative cohomology is invoked.
3. Transport the colimit universal property along the resulting isomorphism and
   the supplied eB. Naturality makes its legs precisely hB. Reflect the resulting
   colimit back along the final tail inclusion.

Edge cases: empty U or V give the identity comparison on the other open. Both
empty give zero groups. U=V uses the diagonal and difference maps. No separatedness
of the ambient scheme is required; the stages of each quantified system are qcqs.
-/
theorem etale_limit_cohomology_binary_gluing
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hCU : EtaleCohomologyStageContinuity U.toScheme)
    (hCV : EtaleCohomologyStageContinuity V.toScheme)
    (hCI : EtaleCohomologyStageContinuity (U ⊓ V).toScheme) :
    EtaleCohomologyStageContinuity (U ⊔ V).toScheme := by
  refine ⟨?_⟩
  intro I _ _ _ D c hc iCompact iQS iAffine F φ hid hcomp G eG hG L hL p H eH hH B eB hB
    i₀ hi
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hlift := etale_limit_cohomology_class_descent D c hc F φ hid hcomp
    G eG hG L hL p H eH hH B eB hB
  have hzero := etale_limit_binary_eventual_zero X U V hU hV hCU hCV hCI
    D c hc F φ hid hcomp G eG hG L hL p H eH hH B eB hB i₀ hi
  have hbij : Function.Bijective (colimit.desc H B) := by
    constructor
    · apply (injective_iff_map_eq_zero (colimit.desc H B).hom).2
      intro z hz
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep H z
      have hx : (B.ι.app i).hom x = 0 := by
        change (colimit.ι H i ≫ colimit.desc H B) x = 0 at hz
        rwa [colimit.ι_desc] at hz
      obtain ⟨j, f, hf⟩ := hzero i x hx
      calc
        colimit.ι H i x = colimit.ι H j (H.map f x) :=
          (colimit.w_apply H f x).symm
        _ = 0 := by rw [hf]; exact map_zero (colimit.ι H j).hom
    · intro y
      obtain ⟨i, x, hx⟩ := hlift y
      refine ⟨colimit.ι H i x, ?_⟩
      change (colimit.ι H i ≫ colimit.desc H B) x = y
      rw [colimit.ι_desc]
      exact hx
  have : IsIso (colimit.desc H B) :=
    (ConcreteCategory.isIso_iff_bijective (colimit.desc H B)).2 hbij
  exact ⟨(colimit.isColimit H).ofIsoColimit
    (Cocone.ext (asIso (colimit.desc H B)) (by intro i; simp))⟩

end AlgebraicGeometry.Etale
