/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.SymmetricProjTautologicalCharts
open Scheme.Modules CategoryTheory.MonoidalCategory
/-- A local coefficient factorization implies the degree-two cross relation.
This is the sheaf-separatedness and scalar-commutation step, independent of
Proj charts and therefore strictly simpler than the parent theorem. -/
theorem cross_tensor_of_local_coefficients_public {S T : Scheme.{u}} (f : T ⟶ S)
    (E : S.Modules) {P Q : T.Modules}
    (q : (tensorPullback f).obj E ⟶ P) (q' : (tensorPullback f).obj E ⟶ Q)
    (hlocal : ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U.1)
      (x : T), x ∈ W →
      ∃ (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
        (a : Γ(P, Z)) (b : Γ(Q, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
        ∀ t : Γ(E, U.1),
          let s := ((tensorPullback f).obj E).presheaf.map (homOfLE (hZW.trans h)).op
            (tensorPullbackSection f E U.1 t)
          q.app Z s = c t • a ∧ q'.app Z s = c t • b) :
    ∀ (U : S.affineOpens) (W : T.affineOpens) (h : W.1 ≤ f ⁻¹ᵁ U.1)
      (m n : Γ(E, U.1)),
      let m' := ((tensorPullback f).obj E).presheaf.map (homOfLE h).op
        (tensorPullbackSection f E U.1 m)
      let n' := ((tensorPullback f).obj E).presheaf.map (homOfLE h).op
        (tensorPullbackSection f E U.1 n)
      tmulSection (q.app W.1 m') (q'.app W.1 n') =
        tmulSection (q.app W.1 n') (q'.app W.1 m') := by
  intro U W h m n
  apply (P ⊗ Q).isSheaf.section_ext
  intro x hx
  obtain ⟨Z, hZW, hxZ, a, b, c, H⟩ := hlocal U W.1 h x hx
  refine ⟨Z, hZW, hxZ, ?_⟩
  simp only [tmulSection_map, ← Hom.app_presheaf_map, presheaf_map_map_apply]
  let s (t : Γ(E, U.1)) := ((tensorPullback f).obj E).presheaf.map
    (homOfLE (hZW.trans h)).op (tensorPullbackSection f E U.1 t)
  change tmulSection (q.app Z (s m)) (q'.app Z (s n)) =
    tmulSection (q.app Z (s n)) (q'.app Z (s m))
  rw [(H m).1, (H n).1, (H m).2, (H n).2,
    smul_tmulSection, smul_tmulSection, tmulSection_smul, tmulSection_smul]
  exact smul_comm _ _ _
end AlgebraicGeometry.SymmetricProjTautologicalCharts
