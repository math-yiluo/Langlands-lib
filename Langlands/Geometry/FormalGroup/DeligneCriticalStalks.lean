import Langlands.Geometry.FormalGroup.DeligneHomogeneousPi
import Langlands.Geometry.FormalGroup.DeligneRationalInjective
import Langlands.Geometry.ModuleConstantSheaf
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The integral stalks at a critical point of Deligne's datum -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.ModuleSheaf

open CategoryTheory TopologicalSpace

variable {O : Type u} [CommRing O] {X : TopCat.{u}}

/-- Distinct constant vectors have distinct germs in the associated constant sheaf. -/
theorem constantSheafGerm_injective (V : ModuleCat.{u} O) (x : X) :
    Function.Injective (constantSheafGerm V x) := by
  let P := (Functor.const (Opens X)ᵒᵖ).obj V
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  let j := toSheafify (Opens.grothendieckTopology X) P
  let _ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u} O) P
  intro s t h
  have hg : TopCat.Presheaf.Γgerm P x s = TopCat.Presheaf.Γgerm P x t := by
    apply (ConcreteCategory.bijective_of_isIso (T.map j)).injective
    change T.map j (TopCat.Presheaf.germ P ⊤ x (Set.mem_univ x) s) =
      T.map j (TopCat.Presheaf.germ P ⊤ x (Set.mem_univ x) t)
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact h
  obtain ⟨_, _, _, _, he⟩ := TopCat.Presheaf.germ_eq P x
    (Set.mem_univ x) (Set.mem_univ x) s t hg
  exact he

/-- Constant-vector germs identify the given coefficient module with the actual stalk. -/
def constantSheafGermEquiv (V : ModuleCat.{u} O) (x : X) :
    V ≃ₗ[O] (TopCat.Presheaf.stalk (C := ModuleCat.{u} O)
      (((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj V).obj) x) :=
  LinearEquiv.ofBijective (constantSheafGerm V x).hom
    ⟨constantSheafGerm_injective V x, constantSheafGerm_surjective V x⟩

end Langlands.ModuleSheaf

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F]

namespace LatticePiSheaf

variable {X : TopCat.{u}} (M : LatticePiSheaf d π X)

private theorem piBetween_degree (i j : ZMod d) : i + ((j - i).val : ZMod d) = j := by
  rw [ZMod.natCast_zmod_val, add_comm i, sub_add_cancel]

/-- The homogeneous Pi path with exponent the least nonnegative residue of j-i. -/
def piBetween (i j : ZMod d) : M.component i ⟶ M.component j :=
  M.piIterate i (j - i).val ≫ eqToHom (congrArg M.component (piBetween_degree i j))

/-- Scalar extension makes this actual homogeneous path an isomorphism. -/
theorem isIso_rationalPiBetween (hπ : algebraMap O F π ≠ 0) (i j : ZMod d) :
    IsIso ((rationalSheafFunctor F X).map (M.piBetween i j)) := by
  rw [piBetween, Functor.map_comp, ← M.rationalPiIterateIso_hom F hπ]
  infer_instance

/-- The integral-to-rational map into the same homogeneous stalk is injective. -/
theorem componentIntegralRationalStalkMap_injective
    (hOF : Function.Injective (algebraMap O F)) (i : ZMod d) (x : X) :
    Function.Injective (integralRationalStalkMap F X (M.component i) x) := by
  have h := M.componentRationalStalkMap_injective F hOF i x
  rw [componentRationalStalkMap, integralRationalStalkMap_naturality] at h
  intro m n he
  apply h
  simp only [ConcreteCategory.comp_apply, he]

/-- The homogeneous path induces an injective map on actual integral stalks. -/
theorem piBetween_stalk_injective (hOF : Function.Injective (algebraMap O F))
    (hπ : algebraMap O F π ≠ 0) (i j : ZMod d) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
      (M.piBetween i j).hom) := by
  let _ := M.isIso_rationalPiBetween hπ i j
  let Q := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x ⋙
    ModuleCat.restrictScalars (algebraMap O F)
  have he : Function.Injective (Q.map ((rationalSheafFunctor F X).map (M.piBetween i j))) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  have hc : Function.Injective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
        (M.piBetween i j).hom ≫ integralRationalStalkMap F X (M.component j) x) := by
    rw [integralRationalStalkMap_naturality]
    exact he.comp (M.componentIntegralRationalStalkMap_injective hOF i x)
  intro m n h
  apply hc
  simp only [ConcreteCategory.comp_apply, h]

end LatticePiSheaf

namespace SheafPreDatum

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)} (D : SheafPreDatum d π F φ)

/-- Constancy on the actual critical locus trivializes the original integral stalk. -/
def criticalLatticeStalkEquiv (h : D.ConstantOnPiZeroLoci)
    (i : ZMod d) (x : S) (hx : x ∈ D.tangent.graded.piZeroLocus i) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} O)
      (D.eta.lattice.component i).obj x ≃ₗ[O] (Fin d → O) :=
  let y : D.piZeroSpace i := ⟨x, hx⟩
  let T := sheafToPresheaf (Opens.grothendieckTopology (D.piZeroSpace i)) (ModuleCat.{u} O) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) y
  ((inverseImageStalkIso (D.piZeroInclusion i) (D.eta.lattice.component i) y) ≪≫
    T.mapIso (h i).some).toLinearEquiv.trans
      (ModuleSheaf.constantSheafGermEquiv (ModuleCat.of O (Fin d → O)) y).symm

/-- A critical degree at a point determines the rank of every integral lattice stalk there. -/
def latticeStalkEquiv [IsDomain O] [IsPrincipalIdealRing O]
    (hOF : Function.Injective (algebraMap O F)) (hπ : algebraMap O F π ≠ 0)
    (h : D.ConstantOnPiZeroLoci) (i j : ZMod d) (x : S)
    (hx : x ∈ D.tangent.graded.piZeroLocus i) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} O)
      (D.eta.lattice.component j).obj x ≃ₗ[O] (Fin d → O) := by
  let e := D.criticalLatticeStalkEquiv h i x hx
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) (X := S) x
  let M := D.eta.lattice
  let f := e.toLinearMap.comp (T.map (M.piBetween j i).hom).hom
  let g := (T.map (M.piBetween i j).hom).hom.comp e.symm.toLinearMap
  have hf : Function.Injective f :=
    e.injective.comp (M.piBetween_stalk_injective hOF hπ j i x)
  have hg : Function.Injective g :=
    (M.piBetween_stalk_injective hOF hπ i j x).comp e.symm.injective
  let _ := Module.Finite.of_injective f hf
  have hrank : Module.finrank O (T.obj (M.component j).obj) = d :=
    calc
      _ = Module.finrank O (Fin d → O) :=
        le_antisymm (LinearMap.finrank_le_finrank_of_injective hf)
          (LinearMap.finrank_le_finrank_of_injective hg)
      _ = d := (Module.finrank_pi O).trans (Fintype.card_fin d)
  let er := LinearEquiv.ofInjective f hf
  obtain ⟨n, br⟩ := f.range.basisOfPid (Pi.basisFun O (Fin d))
  let b := br.map er.symm
  have hn : n = d := by
    rw [← Fintype.card_fin n, ← Module.finrank_eq_card_basis b]
    exact hrank
  exact (b.reindex (finCongr hn)).equivFun

end SheafPreDatum

end Langlands.DeligneFormalSpace
