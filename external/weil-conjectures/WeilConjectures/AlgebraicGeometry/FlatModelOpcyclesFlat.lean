/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleStalkFlat
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Flatness of degree-zero opcycles of a free model

Source: Stacks Project, Tag 0653, applied on stalks; Tags 01U4 and 00HT
for the affine-local flatness comparisons
(blueprint: lem-pc-flat-model-opcycles-flat-zero).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem module_opcycles_flat {R : Type u} [CommRing R]
    (C Q : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n, Module.Flat R (C.X n))
    (hQle : Q.IsStrictlyLE d) (hQflat : ∀ n, Module.Flat R (Q.X n))
    (e : Q ⟶ C) (he : QuasiIso e) : Module.Flat R (Q.opcycles 0) := by
  have := hCge
  have := hCle
  have := hQle
  have := he
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have hfC (n : ℤ) : ObjectProperty.flat (C.X n) :=
    (ModuleCat.flat_iff_flat _).2 (hCflat n)
  have hfQ (n : ℤ) : ObjectProperty.flat (Q.X n) :=
    (ModuleCat.flat_iff_flat _).2 (hQflat n)
  have htor := DerivedCategory.torAmplitudeIn_Q_obj_of_flat C 0 d hfC
  have hK := CochainComplex.kFlat_of_isStrictlyLE_of_flat Q d hfQ
  let E := asIso (DerivedCategory.Q.map e)
  have hex (N : ModuleCat.{u} R) :
      (((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj Q).ExactAt
        (0 - 1) := by
    have := (htor N).1
    have : (DerivedCategory.Q.obj
        (((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj Q)).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso
        ((MonoidalCategory.whiskerRightIso E _).symm ≪≫
          DerivedCategory.QObjTensorSingleFunctorObjIso Q hK N) 0
    rw [DerivedCategory.isGE_Q_obj_iff] at this
    exact CochainComplex.exactAt_of_isGE _ 0 _ (by decide)
  exact (ModuleCat.flat_iff_flat _).1
    (ObjectProperty.flat_opcycles_of_exactAt Q 0 (hfQ _) (hfQ _) hex)

set_option backward.isDefEq.respectTransparency false in
private theorem free_stalk_flat (X : Scheme.{u}) (I : Type u) (x : X) :
    Module.Flat (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let := SheafOfModules.monoidalClosed (R := X.sheaf)
  have := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have hf : ObjectProperty.flat (SheafOfModules.free (R := X.ringCatSheaf) I) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact RingedSpace.flat_stalk_of_isFlat X.toRingedSpace _ hf.tensorRight x

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_preserves_homology (X : Scheme.{u}) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact ((RingedSpace.module_stalk_exact X.toRingedSpace S.f).2.2.2.2
    S.X₃ S.f S.g S.zero).mp hS x

set_option backward.isDefEq.respectTransparency false in
private theorem affine_sections_flat_of_flat_stalks {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] (U : X.affineOpens)
    (hf : ∀ x : X, Module.Flat (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G)) :
    Module.Flat Γ(X, U.1) Γ(G, U.1) := by
  classical
  let A := Γ(X, U.1)
  let xp (P : Ideal A) [P.IsMaximal] : U.1 :=
    U.2.isoSpec.inv ⟨P, inferInstance⟩
  let L (P : Ideal A) [P.IsMaximal] := X.presheaf.stalk (xp P).1
  let (P : Ideal A) [P.IsMaximal] : Algebra A (L P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (xp P)
  have hloc (P : Ideal A) [P.IsMaximal] : IsLocalization P.primeCompl (L P) := by
    have h : U.2.primeIdealOf (xp P) = ⟨P, inferInstance⟩ := by
      change U.2.isoSpec.hom (U.2.isoSpec.inv ⟨P, inferInstance⟩) = _
      rw [← Scheme.Hom.comp_apply, U.2.isoSpec.inv_hom_id]
      rfl
    have := U.2.isLocalization_stalk (xp P)
    simpa only [h] using this
  let T (P : Ideal A) [P.IsMaximal] := TensorProduct A (L P) Γ(G, U.1)
  have hlocal : ∀ (P : Ideal A) [P.IsMaximal],
      IsLocalizedModule.AtPrime P (TensorProduct.mk A (L P) Γ(G, U.1) 1) := by
    intro P _
    have := hloc P
    infer_instance
  apply @Module.flat_of_isLocalized_maximal A A _ _ _ Γ(G, U.1) _ _ _ _ T
    _ _ _ _ (fun P _ ↦ TensorProduct.mk A (L P) Γ(G, U.1) 1) hlocal
  intro P hP
  have := hloc P
  have hid : ((𝟙 X : X ⟶ X).appLE U.1 U.1 (le_rfl)).hom =
      RingHom.id Γ(X, U.1) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U.1))
  have hmod : Module.compHom Γ(G, U.1)
      ((𝟙 X : X ⟶ X).appLE U.1 U.1 (le_rfl)).hom =
      (inferInstance : Module Γ(X, U.1) Γ(G, U.1)) := by
    rw [hid]
    rfl
  have he := AlgebraicGeometry.affine_sections_stalk_tensor_presentation G U
    (xp P).1 (xp P).2
  rw [hmod] at he
  obtain ⟨e⟩ := he
  have := hf (xp P).1
  have : Module.Flat (L P) (T P) := Module.Flat.of_linearEquiv e
  have : Module.Flat A (L P) := IsLocalization.flat (L P) P.primeCompl
  exact Module.Flat.trans A (L P) (T P)

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 0653 (the last cokernel of a flat complex).
Proof: fix a point and an affine neighbourhood with coordinate ring A. For
smaller affine neighbourhoods the hypothesis makes every term of C flat over A.
Their filtered colimit is the stalk, which is flat over A. The stalk ring is a
localization of A, so flatness over A equals flatness over the stalk ring.
Take stalks of e: stalks preserve exact sequences and hence quasi-isomorphisms.
The stalk complex of Q has finite free terms. Its upper bound, and both bounds
of C, remain valid because stalks send zero objects to zero objects. The
bounded-above free complex and the bounded flat complex are
K-flat. Thus tensoring either with any module over the local ring computes derived
tensor, and their tensor complexes have the same homology. The flat complex is
strictly nonnegative, so that homology vanishes in degree -1. Apply
`Module.Flat.opcycles_of_exactAt` at zero to the stalk complex of Q. Stalks commute
with the cokernel defining opcycles, so every stalk of the opcycles is flat.
The opcycles are quasi-coherent, since the two terms defining their cokernel are
finite free. On an affine open they correspond to a module whose localizations
at every prime are flat; the local criterion makes that module flat. For an
inclusion of affine opens W in V, quasi-coherence identifies sections on W with
extension of scalars from V. They are flat over the ring of W, which is flat over
the ring of V because W to V is an open immersion. Transitivity gives flatness
over the ring of V, proving the affine-pair condition `IsFlatOver` for the identity.
There is no assertion of finite freeness here, and no neighbourhood is chosen.
(blueprint: lem-pc-flat-model-opcycles-flat-zero). -/
theorem isFlatOver_opcycles_zero_of_quasiIso {X : Scheme.{u}}
    (C Q : CochainComplex X.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 X))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) :
    (Q.opcycles 0).IsFlatOver (𝟙 X) := by
  classical
  have hqc (n : ℤ) : (Q.X n).IsQuasicoherent := by
    obtain ⟨r, ⟨i⟩⟩ := hQfree n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso i.symm
      (SheafOfModules.isQuasicoherent_free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
  have : (Q.X (-1)).IsQuasicoherent := hqc (-1)
  have : (Q.X 0).IsQuasicoherent := hqc 0
  have hqcO : (Q.opcycles 0).IsQuasicoherent := by
    let i : Q.opcycles 0 ≅ cokernel (Q.d (-1) 0) :=
      (Q.opcyclesIsCokernel (i := (-1)) (j := 0) (by simp)).coconePointUniqueUpToIso
        (colimit.isColimit _)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso i.symm
      (isQuasicoherent_cokernel _)
  have hs (x : X) : Module.Flat (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (Q.opcycles 0)) := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    have : S.PreservesZeroMorphisms := inferInstance
    have : S.PreservesHomology := stalk_preserves_homology X x
    let Cx := (S.mapHomologicalComplex (.up ℤ)).obj C
    let Qx := (S.mapHomologicalComplex (.up ℤ)).obj Q
    have hCxf (n : ℤ) : Module.Flat (X.presheaf.stalk x) (Cx.X n) :=
      AlgebraicGeometry.flat_stalk_of_affineFlatOver_identity _ (hCflat n) x
    have hQxf (n : ℤ) : Module.Flat (X.presheaf.stalk x) (Qx.X n) := by
      obtain ⟨r, ⟨i⟩⟩ := hQfree n
      have := free_stalk_flat X (ULift.{u} (Fin r)) x
      exact Module.Flat.of_linearEquiv (S.mapIso i).toLinearEquiv
    have := hCge
    have := hCle
    have := hQle
    have := he
    have hf := module_opcycles_flat Cx Qx d (by infer_instance) (by infer_instance)
      hCxf (by infer_instance) hQxf ((S.mapHomologicalComplex (.up ℤ)).map e)
      (by infer_instance)
    let i : Qx.opcycles 0 ≅ S.obj (Q.opcycles 0) :=
      (Q.sc 0).mapOpcyclesIso S
    exact Module.Flat.of_linearEquiv i.toLinearEquiv.symm
  have : (Q.opcycles 0).IsQuasicoherent := hqcO
  intro V U hUV
  let f := ((𝟙 X : X ⟶ X).appLE V.1 U.1 hUV).hom
  let := f.toAlgebra
  have : Module.Flat Γ(X, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat (𝟙 X) inferInstance V U hUV
  have := affine_sections_flat_of_flat_stalks (Q.opcycles 0) U hs
  let : Module Γ(X, V.1) Γ(Q.opcycles 0, U.1) := Module.compHom _ f
  have : IsScalarTower Γ(X, V.1) Γ(X, U.1) Γ(Q.opcycles 0, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(X, V.1) Γ(X, U.1) Γ(Q.opcycles 0, U.1)

end AlgebraicGeometry.Scheme.Modules
