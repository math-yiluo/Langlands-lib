/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Affine pullback as sheafified scalar extension

Source: Stacks Project, Tags 01IB and 01I9, and steps 1--2 of
lem-pc-affine-universal-tensor-exact.
(blueprint: lem-pc-affine-tensor-pullback-complex-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a quasi-coherent complex on an affine scheme back to Spec B agrees with
sheafifying its global-sections complex after ordinary scalar extension.
Source: Stacks Project, Tags 01IB and 01I9, and steps 1--2 of
lem-pc-affine-universal-tensor-exact.
(blueprint: lem-pc-affine-tensor-pullback-complex-comparison).

Proof: Restrict C along the canonical inverse Spec A -> S. The source
sectionsRestrictFromSpecLinearEquiv identifies the global sections of this
restriction with evaluation of C at top. Naturality is Hom.app_presheaf_map.
The affine counit fromTildeGamma is an isomorphism on each quasi-coherent term
of the restriction; its naturality assembles a complex isomorphism using
isoOfComponents. Pull this presentation back along Spec B -> Spec A and apply
the source tildePullbackIso, lifted to complexes by mapHomologicalComplexCompIso.
Replace restriction by pullback via restrictFunctorIsoPullback, then compose
pullbacks using pullbackComp and fromSpec_top. These natural isomorphisms commute
with every differential and give exactly the stated comparison.
No homology, boundedness, or flatness assumption is involved. For B zero, C zero,
or S empty the same construction still gives an isomorphism. -/
theorem affine_tensor_pullback_complex_comparison (S : Scheme.{u}) [IsAffine S]
    (C : CochainComplex S.Modules ℤ)
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B]
    [(tilde.functor (CommRingCat.of B)).Additive] :
    Nonempty (
      ((tilde.functor (CommRingCat.of B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) B)).mapHomologicalComplex
          (.up ℤ)).obj
          (((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
            S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex (.up ℤ)).obj C)) ≅
      (((Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫
          S.isoSpec.inv)).mapHomologicalComplex (.up ℤ)).obj C)) := by
  let A := Γ(S, ⊤)
  let h := isAffineOpen_top S
  let F := restrictFunctor h.fromSpec
  let E := moduleSpecΓFunctor (R := CommRingCat.of A)
  let V : S.Modules ⥤ ModuleCat.{u} A :=
    SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)
  let : E.IsRightAdjoint := (tilde.adjunction (R := CommRingCat.of A)).isRightAdjoint
  let := CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts E
  let : E.Additive := Functor.additive_of_preservesBinaryBiproducts E
  let T := tilde.functor (CommRingCat.of A)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
  let := CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let eΓ : F ⋙ E ≅ V := NatIso.ofComponents
    (fun M ↦ (sectionsRestrictFromSpecLinearEquiv M h).toModuleIso) (by
      intro M N f
      ext x
      change (sectionsRestrictFromSpecLinearEquiv N h)
        (((restrictFunctor h.fromSpec).map f).app ⊤ x) =
        f.app ⊤ (sectionsRestrictFromSpecLinearEquiv M h x)
      simp only [sectionsRestrictFromSpecLinearEquiv, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk]
      exact (Hom.app_presheaf_map f _ _).symm)
  let : V.Additive := Functor.additive_of_iso eΓ
  let Q := (F.mapHomologicalComplex (.up ℤ)).obj C
  let eP := (Functor.mapHomologicalComplexCompIso eΓ (.up ℤ)).app C
  have hQ (n : ℤ) : (Q.X n).IsQuasicoherent := by
    have := hqc n
    change ((C.X n).restrict h.fromSpec).IsQuasicoherent
    infer_instance
  let eC : (T.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj Q) ≅ Q :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ by
        have := hQ n
        exact asIso (Q.X n).fromTildeΓ)
      (by
        intro i j hij
        exact (fromTildeΓNatTrans.naturality (Q.d i j)).symm)
  let eFC := (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback h.fromSpec)
    (.up ℤ)).app C
  let φ := CommRingCat.ofHom (algebraMap A B)
  let L := ModuleCat.extendScalars φ.hom
  let : L.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj φ.hom).isLeftAdjoint
  let := CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  let : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  let G := pullback (Spec.map φ)
  let eBC := (Functor.mapHomologicalComplexCompIso (tildePullbackIso φ) (.up ℤ)).app
    ((V.mapHomologicalComplex (.up ℤ)).obj C)
  let ecomp := (Functor.mapHomologicalComplexCompIso
    (pullbackComp (Spec.map φ) h.fromSpec) (.up ℤ)).app C
  have hb : Spec.map φ ≫ h.fromSpec = Spec.map φ ≫ S.isoSpec.inv := by
    rw [IsAffineOpen.fromSpec_top]
  let ebase := (NatIso.mapHomologicalComplex (pullbackCongr hb) (.up ℤ)).app C
  exact ⟨eBC.symm ≪≫ (G.mapHomologicalComplex (.up ℤ)).mapIso
    ((T.mapHomologicalComplex (.up ℤ)).mapIso eP.symm ≪≫ eC ≪≫ eFC) ≪≫
      ecomp ≪≫ ebase⟩

end AlgebraicGeometry.Scheme.Modules
