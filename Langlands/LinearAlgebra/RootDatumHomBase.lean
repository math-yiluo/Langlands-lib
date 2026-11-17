import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! # Transporting bases along injective morphisms of root data -/

noncomputable section

namespace Langlands.RootDatumHomBase

open Set Function
open scoped Classical

variable {J J' M M' N N' : Type*}
  [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
  {P : RootDatum J M N} {Q : RootDatum J' M' N'}

private theorem map_closure_roots (f : RootPairing.Hom P Q) (s : Finset J) :
    (AddSubmonoid.closure (P.root '' (s : Set J))).map f.weightMap.toAddMonoidHom =
      AddSubmonoid.closure (Q.root '' ((s.image f.indexEquiv : Finset J') : Set J')) := by
  classical
  rw [AddMonoidHom.map_mclosure]
  congr 1
  simp only [LinearMap.toAddMonoidHom_coe]
  rw [← Set.image_comp, f.root_weightMap, Set.image_comp, Finset.coe_image]

private theorem map_closure_coroots (f : RootPairing.Hom P Q) (s : Finset J) :
    (AddSubmonoid.closure (Q.coroot '' ((s.image f.indexEquiv : Finset J') : Set J'))).map
      f.coweightMap.toAddMonoidHom = AddSubmonoid.closure (P.coroot '' (s : Set J)) := by
  classical
  rw [AddMonoidHom.map_mclosure]
  congr 1
  simp only [LinearMap.toAddMonoidHom_coe]
  rw [← Set.image_comp, f.coroot_coweightMap, Set.image_comp, Finset.coe_image,
    ← Set.image_comp]
  simp only [Set.image_image, Function.comp_def, Equiv.symm_apply_apply]

/-- Transport a base along the root-index bijection of a root-datum morphism
whose weight and coweight maps are injective. Full lattice surjectivity is
unnecessary. -/
def mapBase (f : RootPairing.Hom P Q)
    (hw : Injective f.weightMap) (hc : Injective f.coweightMap) (B : P.Base) : Q.Base where
  support := by classical exact B.support.image f.indexEquiv
  linearIndepOn_root := by
    classical
    have hroot : Q.root ∘ f.indexEquiv = f.weightMap ∘ P.root := f.root_weightMap.symm
    simp only [Finset.coe_image, ← linearIndepOn_equiv, hroot]
    exact B.linearIndepOn_root.map_injOn _ hw.injOn
  linearIndepOn_coroot := by
    classical
    simp only [Finset.coe_image, ← linearIndepOn_equiv]
    apply LinearIndepOn.of_comp f.coweightMap
    have heq : f.coweightMap ∘ (Q.coroot ∘ f.indexEquiv) = P.coroot := by
      funext i
      rw [Function.comp_apply, Function.comp_apply,
        RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
    rw [heq]
    exact B.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    classical
    rcases B.root_mem_or_neg_mem (f.indexEquiv.symm i) with h | h
    · left
      have hm := AddSubmonoid.mem_map_of_mem f.weightMap.toAddMonoidHom h
      rw [map_closure_roots] at hm
      simpa only [LinearMap.toAddMonoidHom_coe, RootPairing.Hom.root_weightMap_apply,
        Equiv.apply_symm_apply] using hm
    · right
      have hm := AddSubmonoid.mem_map_of_mem f.weightMap.toAddMonoidHom h
      rw [map_closure_roots] at hm
      simpa only [LinearMap.toAddMonoidHom_coe, map_neg,
        RootPairing.Hom.root_weightMap_apply, Equiv.apply_symm_apply] using hm
  coroot_mem_or_neg_mem i := by
    classical
    rcases B.coroot_mem_or_neg_mem (f.indexEquiv.symm i) with h | h
    · left
      apply (AddSubmonoid.mem_map_iff_mem (f := f.coweightMap.toAddMonoidHom) hc).mp
      rw [map_closure_coroots]
      simpa only [LinearMap.toAddMonoidHom_coe,
        RootPairing.Hom.coroot_coweightMap_apply] using h
    · right
      apply (AddSubmonoid.mem_map_iff_mem (f := f.coweightMap.toAddMonoidHom) hc).mp
      rw [map_closure_coroots]
      simpa only [LinearMap.toAddMonoidHom_coe, map_neg,
        RootPairing.Hom.coroot_coweightMap_apply] using h

@[simp] theorem support_mapBase (f : RootPairing.Hom P Q)
    (hw : Injective f.weightMap) (hc : Injective f.coweightMap) (B : P.Base) :
    (mapBase f hw hc B).support = B.support.image f.indexEquiv := rfl

/-- The exact simple-vertex equivalence induced by the morphism. -/
def vertices (f : RootPairing.Hom P Q)
    (hw : Injective f.weightMap) (hc : Injective f.coweightMap) (B : P.Base) :
    B.support ≃ (mapBase f hw hc B).support := by
  classical
  exact (f.indexEquiv.imageFinset B.support).trans
    (Finset.equivOfEq (support_mapBase f hw hc B).symm)

@[simp] theorem vertices_val (f : RootPairing.Hom P Q)
    (hw : Injective f.weightMap) (hc : Injective f.coweightMap) (B : P.Base)
    (i : B.support) : (vertices f hw hc B i).val = f.indexEquiv i.val := rfl

/-- Every ordered integral Cartan entry is unchanged. -/
theorem cartan_eq (f : RootPairing.Hom P Q)
    (hw : Injective f.weightMap) (hc : Injective f.coweightMap) (B : P.Base)
    (i j : B.support) :
    Q.pairing (vertices f hw hc B i).val (vertices f hw hc B j).val = P.pairing i.val j.val :=
  f.pairing

end Langlands.RootDatumHomBase
