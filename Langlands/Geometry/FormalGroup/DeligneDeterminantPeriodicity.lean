import Langlands.Geometry.FormalGroup.DeligneFrameDeterminant
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Sheaves.Sheafify

/-! # Cyclic degree and Deligne's normalized determinant lattices -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
variable {X : TopCat.{u}} (d : ℕ) [NeZero d] (π : O)

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_sheafifyMap_scalar
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} F) (a : F) (x : X) :
    let J := Opens.grothendieckTopology X
    let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
    T.map (sheafifyMap J (algebraMap F (End P) a)) =
      ModuleCat.ofHom (LinearMap.lsmul F (T.obj (sheafify J P)) a) := by
  dsimp only
  let J := Opens.grothendieckTopology X
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  let j := toSheafify J P
  have hp : T.map (algebraMap F (End P) a) =
      ModuleCat.ofHom (LinearMap.lsmul F (T.obj P) a) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ]
    ext s
    exact (TopCat.Presheaf.germ P U x hx).hom.map_smul a s
  let _ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u} F) P
  have hn := congrArg T.map (toSheafify_naturality J (algebraMap F (End P) a))
  rw [T.map_comp, T.map_comp, hp] at hn
  apply (cancel_epi (T.map j)).mp
  rw [← hn]
  ext s
  exact (T.map j).hom.map_smul a s

set_option backward.isDefEq.respectTransparency false in
/-- The d-th power on the actual rational stalk is multiplication by pi. -/
theorem rationalPiStalkAut_pow_hom (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) (x : X) :
    ((rationalPiStalkAut F X d π M hπ x) ^ d).hom =
      ModuleCat.ofHom (LinearMap.lsmul F (rationalLatticeStalk F X d π M x) (algebraMap O F π)) := by
  let J := Opens.grothendieckTopology X
  let T := (presheafToSheaf J (ModuleCat.{u} F)) ⋙
    (sheafToPresheaf J (ModuleCat.{u} F)) ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  let P := (rationalPresheafFunctor F X).obj (latticeScalarSheaf d π X M)
  let a := rationalPiPresheaf F X d π M
  let b := rationalPiStalkAut F X d π M hπ x
  have hb : b.hom = T.map a := by
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
      (rationalPiAut F X d π M hπ).hom.hom = _
    rw [rationalPiAut_hom]
    rfl
  calc
    (b ^ d).hom = (Aut.toEnd (rationalLatticeStalk F X d π M x) b) ^ d :=
      (Aut.toEnd _).map_pow b d
    _ = T.map (a ^ d) := by
      have hba : Aut.toEnd (rationalLatticeStalk F X d π M x) b = (T.mapEnd (X := P)) a := hb
      rw [hba, ← (T.mapEnd (X := P)).map_pow a d]
      rfl
    _ = _ := by
      rw [show a ^ d = algebraMap F (End P) (algebraMap O F π)
        from rationalPiPresheaf_relation F X d π M]
      exact stalk_sheafifyMap_scalar F P (algebraMap O F π) x

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorStalkLattice_scale (k : ℕ) {V : ModuleCat.{u} F}
    (a : F) (L : Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V)) :
    exteriorStalkLattice F k V (scaleStalkLattice F a V L) =
      scaleStalkLattice F (a ^ k) _ (exteriorStalkLattice F k V L) := by
  let g : V ⟶ V := ModuleCat.ofHom (LinearMap.lsmul F V a)
  have hg : exteriorStalkMap F k g =
      ModuleCat.ofHom (LinearMap.lsmul F (⋀[F]^k V) (a ^ k)) := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.map k g.hom (exteriorPower.ιMulti F k v) =
      a ^ k • exteriorPower.ιMulti F k v
    rw [exteriorPower.map_apply_ιMulti]
    change exteriorPower.ιMulti F k (fun i => a • v i) = _
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (exteriorPower.ιMulti F k (M := V)).map_smul_univ (fun _ => a) v
  change exteriorStalkLattice F k V
    (L.map (((ModuleCat.restrictScalars (algebraMap O F)).map g).hom)) = _
  rw [← exteriorStalkLattice_map F k g L, hg]
  rfl

namespace FramedLatticePiSheaf

variable {d π} (M : FramedLatticePiSheaf d π X F)

set_option backward.isDefEq.respectTransparency false in
/-- Advancing one complete cycle scales the translated actual frame lattice by pi. -/
theorem translatedFrameStalkLattice_add_period
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    M.translatedFrameStalkLattice F hπ (n + (d : ℤ)) x =
      scaleStalkLattice F (algebraMap O F π) _ (M.translatedFrameStalkLattice F hπ n x) := by
  let b := rationalPiStalkAut F X d π M.lattice.sheaf hπ x
  let R := ModuleCat.restrictScalars (algebraMap O F)
  have hb : (b ^ (n + (d : ℤ))).hom = (b ^ n).hom ≫ (b ^ d).hom := by
    rw [add_comm n (d : ℤ), zpow_add, zpow_natCast]
    rfl
  have hv : (b ^ d).hom = ModuleCat.ofHom
      (LinearMap.lsmul F (rationalLatticeStalk F X d π M.lattice.sheaf x) (algebraMap O F π)) :=
    rationalPiStalkAut_pow_hom F d π M.lattice.sheaf hπ x
  change (M.frameStalkLattice F x).map (R.map ((b ^ (n + (d : ℤ))).hom)).hom =
    ((M.frameStalkLattice F x).map (R.map (b ^ n).hom).hom).map
      (R.map (ModuleCat.ofHom (LinearMap.lsmul F
        (rationalLatticeStalk F X d π M.lattice.sheaf x) (algebraMap O F π)))).hom
  rw [hb, hv, R.map_comp, ModuleCat.hom_comp, Submodule.map_comp]

/-- The normalized determinant lattice is periodic in the integer index with period d. -/
theorem normalizedFrameDeterminant_periodic (hπ : algebraMap O F π ≠ 0) (x : X) :
    Function.Periodic (fun n => M.normalizedFrameDeterminant F hπ n x) (d : ℤ) := by
  intro n
  change M.normalizedFrameDeterminant F hπ (n + (d : ℤ)) x =
    M.normalizedFrameDeterminant F hπ n x
  unfold normalizedFrameDeterminant
  rw [M.translatedFrameStalkLattice_add_period F hπ n x, exteriorStalkLattice_scale,
    scaleStalkLattice_mul]
  have hs : (algebraMap O F π) ^ (-(n + (d : ℤ))) * (algebraMap O F π) ^ d =
      (algebraMap O F π) ^ (-n) := by
    rw [← zpow_natCast, ← zpow_add₀ hπ]
    congr 1
    omega
  rw [hs]

/-- The normalized frame determinant evaluated on the canonical representative of the cyclic degree. -/
def normalizedFrameDeterminantAtDegree
    (hπ : algebraMap O F π ≠ 0) (i : ZMod d) (x : X) :=
  M.normalizedFrameDeterminant F hπ (i.val : ℤ) x

/-- The integer formula agrees with the canonical representative at every positive or negative index. -/
theorem normalizedFrameDeterminant_eq_atDegree
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    M.normalizedFrameDeterminant F hπ n x =
      M.normalizedFrameDeterminantAtDegree F hπ (n : ZMod d) x := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff d n (n : ZMod d)).mp rfl
  let i : ZMod d := (n : ZMod d)
  change M.normalizedFrameDeterminant F hπ n x =
    M.normalizedFrameDeterminant F hπ (i.val : ℤ) x
  rw [show n = (i.val : ℤ) + (d : ℤ) * k from hk, mul_comm (d : ℤ) k]
  exact ((M.normalizedFrameDeterminant_periodic F hπ x).int_mul k) (i.val : ℤ)

end FramedLatticePiSheaf

namespace SheafPreDatum

open _root_.AlgebraicGeometry

variable {d π F} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)} (D : SheafPreDatum d π F φ)

/-- Deligne's all-integer determinant condition is equivalent to checking one index per degree. -/
theorem determinantNormalized_iff_atDegree (hπ : algebraMap O F π ≠ 0) :
    D.DeterminantNormalized hπ ↔
      ∀ (i : ZMod d) (x : S), x ∈ D.tangent.graded.piZeroLocus i →
        D.componentDeterminant i x = D.eta.normalizedFrameDeterminantAtDegree F hπ i x := by
  constructor
  · intro h i x hx
    have hi : ((i.val : ℤ) : ZMod d) = i := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hh := h (i.val : ℤ) x (hi.symm ▸ hx)
    rw [hi] at hh
    exact hh
  · intro h n x hx
    rw [D.eta.normalizedFrameDeterminant_eq_atDegree F hπ n x]
    exact h (n : ZMod d) x hx

end SheafPreDatum

end Langlands.DeligneFormalSpace
