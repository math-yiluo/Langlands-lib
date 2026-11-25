/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-! # Finite free evaluation over the direct-image algebra

Source: Stacks Project, Morphisms, Tag 01SB; Properties, Tag 01PB;
Cohomology of Schemes, Tag 0897, proof
(blueprint: lem-weil-pbc-affine-pushforward-free-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "PUSH" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

private theorem epi_restrictScalars_iff
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R ⟶ S) {M N : SheafOfModules.{u} S} (φ : M ⟶ N) :
    Epi ((SheafOfModules.restrictScalars α).map φ) ↔ Epi φ := by
  constructor
  · intro h
    have h' : Epi ((SheafOfModules.toSheaf R).map
        ((SheafOfModules.restrictScalars α).map φ)) := Functor.map_epi _ _
    exact (SheafOfModules.toSheaf S).epi_of_epi_map h'
  · intro h
    have h' : Epi ((SheafOfModules.toSheaf S).map φ) := Functor.map_epi _ _
    exact (SheafOfModules.toSheaf R).epi_of_epi_map h'

private noncomputable def scalarOver (V : X.Opens) :=
  SheafOfModules.restrictScalars
    (((Over.forget V).sheafPushforwardContinuous RingCat
      ((Opens.grothendieckTopology X).over V) (Opens.grothendieckTopology X)).map
        f.toRingCatSheafHom) ⋙ (overEquiv V).functor

private theorem scalarOver_isQuasicoherent [IsAffineHom f]
    (F : U.Modules) [F.IsQuasicoherent] (V : X.Opens) :
    ((scalarOver f V).obj (((PUSH).obj F).over V)).IsQuasicoherent := by
  have := isQuasicoherent_pushforward_of_isAffineHom f F
  have := isQuasicoherent_restrictFunctor V.ι ((pushforward f).obj F)
  exact (SheafOfModules.isQuasicoherent.{u} (V : Scheme).ringCatSheaf).prop_of_iso
    ((overFunctorEquiv V).app ((pushforward f).obj F)).symm inferInstance

private theorem scalarOver_epi_iff (V : X.Opens)
    {M N : SheafOfModules.{u} ((AR).over V)} (φ : M ⟶ N) :
    Epi ((scalarOver f V).map φ) ↔ Epi φ := by
  exact (Functor.epi_map_iff_epi (overEquiv V).functor _).trans
    (epi_restrictScalars_iff _ φ)

private theorem scalarOver_surjective_app_top_iff (V : X.Opens)
    {M N : SheafOfModules.{u} ((AR).over V)} (φ : M ⟶ N) :
    Function.Surjective (((scalarOver f V).map φ).app ⊤) ↔
      Function.Surjective (φ.val.app (.op (Over.mk (𝟙 V)))) := by
  change Function.Surjective (φ.val.app (.op _)) ↔ _
  have htop : (Opens.overEquivalence V).symm.functor.obj ⊤ = Over.mk (𝟙 V) := by
    refine CostructuredArrow.obj_ext _ _ ?_ (by apply Subsingleton.elim)
    ext x
    simp [Opens.overEquivalence]
  rw [htop]

private theorem epi_iff_surjective_app_top {Y : Scheme.{u}} [IsAffine Y]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    Epi φ ↔ Function.Surjective (φ.app ⊤) := by
  constructor
  · intro h
    have hi := (quasiCoherent_cokernel_image φ).2.2.2.2.2.2.2.2 ⟨⊤, isAffineOpen_top _⟩
    have : IsIso (CategoryTheory.Abelian.image.ι φ) := inferInstance
    intro y
    have hyr : y ∈ Set.range ((CategoryTheory.Abelian.image.ι φ).app ⊤) := by
      exact ⟨(inv ((CategoryTheory.Abelian.image.ι φ).app ⊤)) y, by simp⟩
    rw [hi.1] at hyr
    exact hyr
  · intro h
    exact epi_of_surjective_app φ (fun _ : Unit ↦ ⊤)
      (fun _ ↦ isAffineOpen_top _) (by simp) (fun _ ↦ h)

/-- A finite free evaluation map into the algebra-valued direct image is epi on an
   affine open exactly when its map on sections over that open is surjective.
   Source: Stacks Project, Morphisms, Tag 01SB; Schemes, Tag 01IC
   (blueprint: lem-weil-pbc-affine-pushforward-free-evaluation).

Proof: Set W = f⁻¹ V and B = O_U(W). Both W and V are affine. The finite free
A|V-module is the direct image of O_W^I: finite coproducts are finite products,
and pushforward preserves products, compatibly with their basis sections.
The given sections define a map O_W^I → F|W. By the affine tilde-Gamma
correspondence, its image on W is the module image of B^I → F(W).
If the direct-image evaluation is epi, every section on V lifts locally.
Pulling the covering back to W puts its corresponding section in the sheaf
image on W, hence in the module image by the affine-sections image formula.
Conversely, surjectivity of B^I → F(W) makes O_W^I → F|W epi. On every affine
V' contained in V, W' = f⁻¹ V' is affine. Exactness of affine sections makes
O_U(W')^I → F(W') surjective. Thus the direct-image evaluation is surjective
on sections on an affine basis of V, so it is locally surjective and epi.
This uses only quasi-coherence of F and imposes no finite-type condition. -/
theorem affine_pushforward_free_evaluation [IsAffineHom f]
    (F : U.Modules) (hF : F.IsQuasicoherent) (V : X.Opens) (hV : IsAffineOpen V)
    (I : Type u) [Finite I]
    (s : I → (((PUSH).obj F).over V).sections) :
    Epi ((((PUSH).obj F).over V).freeHomEquiv.symm s) ↔
      Function.Surjective
        (((((PUSH).obj F).over V).freeHomEquiv.symm s).val.app (.op (Over.mk (𝟙 V)))) := by
  let T := scalarOver f V
  let φ := ((((PUSH).obj F).over V).freeHomEquiv.symm s)
  let ψ := T.map φ
  have : IsAffine (V : Scheme) := hV
  have : F.IsQuasicoherent := hF
  have htarget : (T.obj (((PUSH).obj F).over V)).IsQuasicoherent :=
    scalarOver_isQuasicoherent f F V
  have hsource : (T.obj (SheafOfModules.free (R := (AR).over V) I)).IsQuasicoherent := by
    have : T.Additive := by
      constructor
      intro M N a b
      ext W m
      rfl
    have hunit : (T.obj (SheafOfModules.unit ((AR).over V))).IsQuasicoherent := by
      have := SheafOfModules.isQuasicoherent_unit (R := U.ringCatSheaf)
      exact scalarOver_isQuasicoherent f (SheafOfModules.unit U.ringCatSheaf) V
    have := isQuasicoherent_sigma
      (fun _ : I ↦ T.obj (SheafOfModules.unit ((AR).over V)))
    exact (SheafOfModules.isQuasicoherent.{u} (V : Scheme).ringCatSheaf).prop_of_iso
      (CategoryTheory.Limits.PreservesCoproduct.iso T
        (fun _ : I ↦ SheafOfModules.unit ((AR).over V))).symm inferInstance
  exact (scalarOver_epi_iff f V φ).symm.trans
    ((epi_iff_surjective_app_top ψ).trans (scalarOver_surjective_app_top_iff f V φ))

end AlgebraicGeometry.Scheme.Modules
