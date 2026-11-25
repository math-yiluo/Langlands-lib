/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.FlatModelOpcyclesFlat
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_opcycles_zero {X : Scheme.{u}}
    (Q : CochainComplex X.Modules ℤ)
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) :
    (Q.opcycles 0).IsFinitePresentation := by
  obtain ⟨m, ⟨em⟩⟩ := hfree (-1)
  obtain ⟨n, ⟨en⟩⟩ := hfree 0
  let f := em.inv ≫ Q.d (-1) 0 ≫ en.hom
  let g := en.inv ≫ Q.pOpcycles 0
  have hfg : f ≫ g = 0 := by simp [f, g]
  have hg : IsColimit (CokernelCofork.ofπ g hfg) :=
    IsCokernel.ofIso (Q.d (-1) 0) (Q.opcyclesIsCokernel (-1) 0 (by simp))
      (CokernelCofork.ofπ g hfg) em en (Iso.refl _) (by simp [f]) (by simp [g])
  let P := SheafOfModules.presentationOfIsCokernelFree f g hfg hg
  have : P.IsFinite := by
    exact ⟨⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩,
      ⟨inferInstanceAs (Finite (ULift.{u} (Fin m)))⟩⟩
  exact P.isFinitePresentation

private theorem finiteLocallyFree_of_flat_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] (hflat : M.IsFlatOver (𝟙 X)) :
    M.IsFiniteLocallyFree := by
  refine isFiniteLocallyFree_of_isAffineOpen M fun W hW ↦ ⟨
    finitePresentation_sections_of_isFinitePresentation M hW, ?_⟩
  have h := hflat ⟨W, hW⟩ ⟨W, hW⟩ (by simp)
  have hid : (𝟙 X : X ⟶ X).appLE W W (by simp) = 𝟙 Γ(X, W) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, homOfLE_refl,
      op_id, Category.id_comp]
    exact X.presheaf.map_id _
  change @Module.Flat Γ(X, W) Γ(M, W) _ _
    (Module.compHom Γ(M, W) ((𝟙 X : X ⟶ X).appLE W W (by simp)).hom) at h
  rw [hid] at h
  exact h

/-- The degree-zero cokernel of the canonical quotient truncation is finite free near t.
Source: Stacks Project, Tags 0653 and 00NX.
Proof: choose an affine neighbourhood of t inside U. The cokernel of Q.d (-1) 0
is quasi-coherent and finitely presented, because both terms are finite free.
At every stalk, the bounded flat complex C has Tor amplitude [0,d]. The bounded-above
free complex Q is K-flat, so its quasi-isomorphism to C gives it the same Tor amplitude.
Tag 0653 makes the degree-zero cokernel flat at each stalk. Over the chosen affine,
the corresponding finitely presented flat module is finite projective. Tag 00NX gives
an open neighbourhood of t on which it is finite free. Restriction is exact, so this
restricted cokernel is the cokernel of the restricted differential. The degree-zero
term of Mathlib's truncGE 0 is canonically isomorphic to that cokernel; transport the
finite-free isomorphism along it. Only the open neighbourhood and rank are existential;
the complex itself is the explicit canonical truncation, not an arbitrary witness.
(blueprint: lem-pc-flat-model-finite-free-truncation-zero). -/
theorem exists_local_finiteFree_truncation_zero {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U), t ∈ V ∧ ∃ r : ℕ,
      Nonempty ((CochainComplex.truncGE
        (((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj Q) 0).X 0 ≅
          SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  have : (Q.opcycles 0).IsFinitePresentation := finitePresentation_opcycles_zero Q hQfree
  have : (Q.opcycles 0).IsFiniteLocallyFree :=
    finiteLocallyFree_of_flat_finitePresentation _
      (isFlatOver_opcycles_zero_of_quasiIso C Q d hCge hCle hCflat hQle hQfree e he)
  obtain ⟨W, κ, hκ, hW, ⟨eW⟩⟩ :=
    exists_restrict_iso_free_of_isFiniteLocallyFree (Q.opcycles 0) ⟨t, ht⟩
  classical
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  let r := Fintype.card κ
  let V := U.ι ''ᵁ W
  let hVU : V ≤ U := U.ι_image_le W
  let j := (U.ι.isoImage W).inv
  let f := T.homOfLE hVU
  have hj : j ≫ W.ι = f := U.isoImage_ι_inv_ι W
  have htV : t ∈ V := ⟨⟨t, ht⟩, hW, rfl⟩
  let efree : (pullback f).obj (Q.opcycles 0) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (pullbackCongr hj.symm).app _ ≪≫ (pullbackComp j W.ι).symm.app _ ≪≫
      (pullback j).mapIso (((restrictFunctorIsoPullback W.ι).app _).symm ≪≫ eW) ≪≫
      pullbackFreeIso j κ ≪≫
      SheafOfModules.freeFunctor.mapIso
        (Equiv.toIso ((Fintype.equivFin κ).trans Equiv.ulift.symm))
  let F := pullback f
  let QV := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let e₁ : QV.opcycles 0 ≅ cokernel (QV.d (-1) 0) :=
    (QV.opcyclesIsCokernel (-1) 0 (by simp)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let e₂ : cokernel (Q.d (-1) 0) ≅ Q.opcycles 0 :=
    (colimit.isColimit _).coconePointUniqueUpToIso
      (Q.opcyclesIsCokernel (-1) 0 (by simp))
  refine ⟨V, hVU, htV, r, ⟨?_⟩⟩
  exact CochainComplex.truncGEXIsoOpcycles QV 0 ≪≫ e₁ ≪≫
    (PreservesCokernel.iso F (Q.d (-1) 0)).symm ≪≫ F.mapIso e₂ ≪≫ efree

end AlgebraicGeometry.Scheme.Modules
