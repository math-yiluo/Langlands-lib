import Langlands.LinearAlgebra.RootDatumIsogenyChambers

/-! # Compatible bases for root-datum isogenies -/

noncomputable section

universe u v u' v'

namespace Langlands.LinearAlgebra.RootDatumIsogeny

variable {p : ℕ} {J : Type v} {X Y : Type u}
    {J' : Type v'} {X' Y' : Type u'}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Finite J] [Finite J']
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X'] [Module.Finite ℤ Y']
    {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
    [P.IsReduced] [Q.IsReduced]

/-- A pair of bases whose positive systems and simple roots correspond
under the actual index equivalence of the root-datum isogeny. -/
structure CompatibleBases (f : RootDatumIsogeny p P Q) where
  source : P.Base
  target : Q.Base
  isPos_iff : ∀ i, source.IsPos i ↔ target.IsPos (f.indexEquiv i)
  simple_iff : ∀ i, i ∈ source.support ↔ f.indexEquiv i ∈ target.support

/-- Choose a regular integral coweight of the codomain datum and use its
pullback to construct compatible bases, including central lattice
directions without a semisimplicity hypothesis. -/
def compatibleBases (f : RootDatumIsogeny p P Q) : CompatibleBases f := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : Fintype J' := Fintype.ofFinite J'
  let v := (RootDatumCoweightFace.exists_regular_refinement Q 0).choose
  have hv : ∀ i, Q.root' i v ≠ 0 :=
    (RootDatumCoweightFace.exists_regular_refinement Q 0).choose_spec.1
  have hfv (i : J) : P.root' i (f.coweightMap v) ≠ 0 := by
    change P.toLinearMap (P.root i) (f.coweightMap v) ≠ 0
    rw [← f.pairing_apply, f.root_weightMap]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast (f.rootFactor_pos i).ne')
      (hv (f.indexEquiv i))
  let b := (RootDatumCoweightFace.exists_base_support P (f.coweightMap v) hfv).choose
  have hb := (RootDatumCoweightFace.exists_base_support P (f.coweightMap v) hfv).choose_spec
  let b' := (RootDatumCoweightFace.exists_base_support Q v hv).choose
  have hb' := (RootDatumCoweightFace.exists_base_support Q v hv).choose_spec
  have hbpos (i : J) (hi : i ∈ b.support) :
      0 < P.toLinearMap (P.root i) (f.coweightMap v) := by
    have hmem : i ∈ IsAddIndecomposable.baseOf P.root
        ((P.flip.toLinearMap (f.coweightMap v)) : X →+ ℤ) := by
      rw [← hb]
      exact hi
    exact hmem.1
  have hbpos' (i : J') (hi : i ∈ b'.support) :
      0 < Q.toLinearMap (Q.root i) v := by
    have hmem : i ∈ IsAddIndecomposable.baseOf Q.root
        ((Q.flip.toLinearMap v) : X' →+ ℤ) := by
      rw [← hb']
      exact hi
    exact hmem.1
  have hsign := isPos_iff_functional_pos (P := P)
    b (P.flip.toLinearMap (f.coweightMap v)) hfv hbpos
  have hsign' := isPos_iff_functional_pos (P := Q) b' (Q.flip.toLinearMap v) hv hbpos'
  exact {
    source := b
    target := b'
    isPos_iff := fun i =>
      (hsign i).trans ((f.root_pos_coweightMap_iff v i).trans (hsign' _).symm)
    simple_iff := f.mem_support_iff_of_coweight_signs v b b' hsign hsign' }

namespace CompatibleBases

variable {f : RootDatumIsogeny p P Q} (D : CompatibleBases f)

/-- The index equivalence restricts to an equivalence of the actual
simple-root index types of the two compatible bases. -/
def simpleIndexEquiv :
    {i : J // i ∈ D.source.support} ≃ {j : J' // j ∈ D.target.support} where
  toFun i := ⟨f.indexEquiv i, (D.simple_iff i).mp i.property⟩
  invFun j := ⟨f.indexEquiv.symm j,
    (D.simple_iff _).mpr (by simpa only [Equiv.apply_symm_apply] using j.property)⟩
  left_inv i := Subtype.ext (f.indexEquiv.symm_apply_apply i)
  right_inv j := Subtype.ext (f.indexEquiv.apply_symm_apply j)

/-- The same correspondence restricts to all positive-root indices. -/
def positiveIndexEquiv :
    {i : J // D.source.IsPos i} ≃ {j : J' // D.target.IsPos j} where
  toFun i := ⟨f.indexEquiv i, (D.isPos_iff i).mp i.property⟩
  invFun j := ⟨f.indexEquiv.symm j,
    (D.isPos_iff _).mpr (by simpa only [Equiv.apply_symm_apply] using j.property)⟩
  left_inv i := Subtype.ext (f.indexEquiv.symm_apply_apply i)
  right_inv j := Subtype.ext (f.indexEquiv.apply_symm_apply j)

end CompatibleBases
end Langlands.LinearAlgebra.RootDatumIsogeny
