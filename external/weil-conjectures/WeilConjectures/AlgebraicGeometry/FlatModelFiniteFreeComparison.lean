/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

private theorem flat_of_finiteFree {Y : Scheme.{u}}
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (h : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian Y.ringCatSheaf
  obtain ⟨r, ⟨e⟩⟩ := h
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hf).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

private noncomputable def tensorOrdinaryIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullback g ≅ pullback g :=
  (Classical.choice (nonempty_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

private theorem kFlat_of_iso {Y : Scheme.{u}}
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (e : K ≅ L) (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) :
    CochainComplex.IsKFlatTensor (R := Y.sheaf) L := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  intro F hF i
  exact (hK F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

private theorem kFlat_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : CochainComplex Y.Modules ℤ) (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) :
    CochainComplex.IsKFlatTensor (R := X.sheaf)
      (((pullback g).mapHomologicalComplex (.up ℤ)).obj K) := by
  have : (tensorPullback g).Additive :=
    (Classical.choice (nonempty_tensorPullbackAdjunction g)).left_adjoint_additive
  have hk := CochainComplex.isKFlat_pullback g.base X.sheaf Y.sheaf ⟨g.c⟩ K hK
  apply kFlat_of_iso ((NatIso.mapHomologicalComplex (tensorOrdinaryIso g) (.up ℤ)).app K)
  convert hk using 1
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

private theorem quasiIso_pullback_of_kFlat {X Y : Scheme.{u}} (g : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ} (s : K ⟶ L)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hL : CochainComplex.IsKFlatTensor (R := Y.sheaf) L) (hs : QuasiIso s) :
    QuasiIso (((pullback g).mapHomologicalComplex (.up ℤ)).map s) := by
  have : (tensorPullback g).Additive :=
    (Classical.choice (nonempty_tensorPullbackAdjunction g)).left_adjoint_additive
  have hq := tensorPullback_quasiIso_of_isKFlat g s hK hL hs
  let ec := NatIso.mapHomologicalComplex (tensorOrdinaryIso g) (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (ec.app K) (ec.app L) (ec.hom.naturality s).symm)).mp hq


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 1024 in

/-- Pullback homology comparison for a local finite-free replacement.
Source: Stacks Project, Tags 06YD and 06YJ, as used in
`lem-pc-flat-model-finite-free-shortening`.
Proof: assume the displayed quasi-isomorphism from P to the restriction of C.
The bounded flat representatives compute derived pullback termwise; the
quasi-isomorphism is preserved, and taking homology gives the displayed
isomorphism for every scheme map and degree.
(blueprint: lem-pc-flat-model-finite-free-shortening-comparison).
Proof: The construction argument supplies the stated local data and its induced
quasi-isomorphism. Pulling it back along any scheme map preserves it for these
finite-free and flat complexes; taking homology gives the displayed isomorphism.
-/
theorem local_finiteFree_homology_comparison {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T)
    (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ)
    (hstruct : t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (P.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))))
    (eP : P ⟶ ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj C)
    (heP : QuasiIso eP) :
    ∀ {T' : Scheme.{u}} (g : T' ⟶ V.toScheme) (q : ℕ),
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
        (((Modules.pullback (g ≫ T.homOfLE hVU)).mapHomologicalComplex _).obj C).homology q) := by
  have _ := hCge
  have _ := hQle
  have _ := hQfree
  have _ := he
  have : C.IsStrictlyLE (d : ℤ) := hCle
  have : P.IsStrictlyLE (d : ℤ) := hstruct.2.2.1
  have hC : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf) C :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace U.toScheme.toRingedSpace C
      ⟨d, fun n hn ↦ C.isZero_of_isStrictlyLE d n hn⟩
      (fun n ↦ isFlat_of_affineFlatOver_identity (C.X n) (hCflat n))
  have hP : CochainComplex.IsKFlatTensor (R := V.toScheme.sheaf) P :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace V.toScheme.toRingedSpace P
      ⟨d, fun n hn ↦ P.isZero_of_isStrictlyLE d n hn⟩
      (fun n ↦ flat_of_finiteFree (P.X n) (hstruct.2.2.2 n))
  have hrest := kFlat_pullback (T.homOfLE hVU) C hC
  intro T' g q
  have := quasiIso_pullback_of_kFlat g eP hP hrest heP
  let ec := (Functor.mapHomologicalComplexCompIso
    (pullbackComp g (T.homOfLE hVU)) (.up ℤ)).app C
  exact ⟨asIso (HomologicalComplex.homologyMap
      (((pullback g).mapHomologicalComplex (.up ℤ)).map eP) (q : ℤ)) ≪≫
    HomologicalComplex.homologyMapIso ec (q : ℤ)⟩

end AlgebraicGeometry.Scheme.Modules
