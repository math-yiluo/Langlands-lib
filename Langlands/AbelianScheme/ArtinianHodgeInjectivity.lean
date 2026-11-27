import Langlands.AbelianScheme.ArtinianHodgeExactStatement
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Injectivity of the degree-one closed-form class map -/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_apply inter_le_comp)

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (U : Scheme.AffineOpenCover.{u} X)

lemma inter_single (σ : Fin 1 → U.I₀) : inter (coverOpens U) σ = coverOpens U (σ 0) := by
  refine le_antisymm (inter_le_apply _ 0) (le_iInf fun a => ?_)
  rw [Subsingleton.elim a 0]

/-- The degree-zero cocycles of a sheaf on an affine open cover are the restrictions of
its global sections. -/
lemma existsUnique_global_of_cechD_zero (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (hP : TopCat.Presheaf.IsSheaf P) (c : Cochains U P 0) (hc : cechD U P 0 c = 0) :
    ∃! s : P.obj (op ⊤), ∀ σ, P.map (homOfLE le_top).op s = c σ := by
  let V (σ : Fin 1 → U.I₀) := inter (coverOpens U) σ
  have hcover : ⊤ ≤ iSup V := by
    rw [← U.openCover.iSup_opensRange]
    refine iSup_le fun i => le_iSup_of_le (fun _ => i) ?_
    rw [show V (fun _ => i) = coverOpens U i from inter_single U _]
    rfl
  have hcompat : TopCat.Presheaf.IsCompatible P V c := by
    intro σ ρ
    let τ : Fin 2 → U.I₀ := ![σ 0, ρ 0]
    have he₀ : τ ∘ (0 : Fin 2).succAbove = ρ := by
      funext a
      rw [Subsingleton.elim a 0]
      rfl
    have he₁ : τ ∘ (1 : Fin 2).succAbove = σ := by
      funext a
      rw [Subsingleton.elim a 0]
      rfl
    have hW : V σ ⊓ V ρ ≤ inter (coverOpens U) τ := by
      refine le_iInf fun j => ?_
      fin_cases j
      · exact inf_le_left.trans (inter_le_apply _ 0)
      · exact inf_le_right.trans (inter_le_apply _ 0)
    have hres (j : Fin 2) (ν) (hν : τ ∘ j.succAbove = ν) (h : V σ ⊓ V ρ ≤ V ν) :
        P.map (homOfLE hW).op
          (P.map (homOfLE (inter_le_comp (U := coverOpens U) τ j.succAbove)).op
            (c (τ ∘ j.succAbove))) = P.map (homOfLE h).op (c ν) := by
      subst ν
      rw [← ConcreteCategory.comp_apply, ← P.map_comp]
      rfl
    have hv : cechD U P 0 c τ = 0 := congrFun hc τ
    have hh := congrArg (fun x : P.obj (op (inter (coverOpens U) τ)) =>
      P.map (homOfLE hW).op x) hv
    rw [cechD_apply, Fin.sum_univ_two] at hh
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
      ← sub_eq_add_neg, map_sub, map_zero] at hh
    rw [hres 0 ρ he₀ inf_le_right, hres 1 σ he₁ inf_le_left] at hh
    exact (sub_eq_zero.mp hh).symm
  exact TopCat.Sheaf.existsUnique_gluing' ⟨P, hP⟩ V ⊤
    (fun _ => homOfLE le_top) hcover c hcompat

/-- Restrict a global section to every open of a cover. -/
def globalCochain (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) : P.obj (op ⊤) →ₗ[R] Cochains U P 0 :=
  LinearMap.pi fun _ => (P.map (homOfLE le_top).op).hom

/-- The Čech differential of a global section vanishes by the composition law
of restriction. -/
lemma cechD_globalCochain (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (s : P.obj (op ⊤)) :
    cechD U P 0 (globalCochain U P s) = 0 := by
  funext τ
  rw [cechD_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    ← sub_eq_add_neg, Pi.zero_apply, sub_eq_zero]
  change P.map _ (P.map _ s) = P.map _ (P.map _ s)
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

variable (f : X ⟶ Spec (CommRingCat.of R))

private lemma functions_isSheaf : TopCat.Presheaf.IsSheaf (functions f) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget (ModuleCat.{u} R)) _).mpr
  change TopCat.Presheaf.IsSheaf (X.presheaf ⋙ forget CommRingCat)
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget CommRingCat) _).mp X.sheaf.property

/-- For a compatible family of functions, the common scalar is determined uniquely
when the structural map is an isomorphism on global sections. -/
lemma existsUnique_scalar_of_cechD_zero [IsIso f.appTop]
    (c : C0 f U) (hc : cechD U (functions f) 0 c = 0) :
    ∃! r : R, ∀ σ, c σ = algebraMap R ((sectionAlgebras f).obj
      (op (inter (coverOpens U) σ))) r := by
  obtain ⟨s, hs, hu⟩ :=
    existsUnique_global_of_cechD_zero U (functions f) (functions_isSheaf f) c hc
  change Γ(X, ⊤) at s
  let e := ((Scheme.ΓSpecIso (CommRingCat.of R)).symm ≪≫ (asIso f.appTop)).commRingCatIsoToRingEquiv
  have hm (r : R) (σ : Fin 1 → U.I₀) :
      (functions f).map (homOfLE le_top).op (e r) =
        algebraMap R ((sectionAlgebras f).obj (op (inter (coverOpens U) σ))) r := rfl
  refine ⟨e.symm s, ?_, ?_⟩
  · intro σ
    exact (hs σ).symm.trans (by rw [← hm, e.apply_symm_apply])
  · intro r hr
    apply e.injective
    rw [e.apply_symm_apply]
    apply hu
    intro σ
    rw [hm, ← hr]

/-- When the structural map on global functions is an isomorphism, a compatible
function cochain has zero relative differential. -/
lemma cochainMap_exteriorD0_eq_zero_of_cechD_eq_zero [IsIso f.appTop]
    (c : C0 f U) (hc : cechD U (functions f) 0 c = 0) :
    cochainMap U (exteriorD0 f) 0 c = 0 := by
  obtain ⟨r, hr, _⟩ := existsUnique_scalar_of_cechD_zero U f c hc
  funext σ
  let A := (sectionAlgebras f).obj (op (inter (coverOpens U) σ))
  change RelativeForms.dZero R A (c σ) = 0
  rw [hr σ]
  exact (KaehlerDifferential.D R A).map_algebraMap r

/-- If all global functions come from the base, the classes of compatible closed forms
inject into degree-one Čech–de Rham cohomology on the supplied cover. -/
theorem closedFormClass_injective_of_isIso_appTop [Smooth f] [IsSeparated f] [Finite U.I₀]
    [IsIso f.appTop] : Function.Injective (closedFormClass f U) := by
  apply (closedFormClass f U).ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro b hb
  change closedFormClass f U b = 0 at hb
  obtain ⟨h, hh⟩ := (Submodule.Quotient.mk_eq_zero _).mp hb
  have hd : D0 f U h = (0, b.val) := congrArg Subtype.val hh
  have hc : cechD U (functions f) 0 h = 0 := congrArg Prod.fst hd
  have hform : cochainMap U (exteriorD0 f) 0 h = b.val := congrArg Prod.snd hd
  apply (Submodule.mem_bot _).mpr
  exact Subtype.ext (hform.symm.trans (cochainMap_exteriorD0_eq_zero_of_cechD_eq_zero U f h hc))

end Langlands.AlgebraicGeometry.AffineCechDeRham

namespace Langlands.AbelianScheme

/-- The closed-form class map for an abelian scheme over an affine base is injective. -/
theorem closedFormClass_injective {R : Type u} [CommRing R]
    (B : AbelianScheme (Spec (CommRingCat.of R)))
    (U : Scheme.AffineOpenCover.{u} B.X.left) [Finite U.I₀] :
    Function.Injective (closedFormClass B.X.hom U) := by
  have : IsIso B.X.hom.appTop := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    _ _ _ inferInstance inferInstance inferInstance ⊤
  exact closedFormClass_injective_of_isIso_appTop U B.X.hom

end Langlands.AbelianScheme
