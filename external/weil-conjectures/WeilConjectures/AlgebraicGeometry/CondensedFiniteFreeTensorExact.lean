/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits

/-! # Exactness of tensoring by a pro-etale locally finite free module -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {R : C} [MonObj R] [IsCommMonObj R]
attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

private theorem tensor_finiteFree_preservesFiniteLimits {M : Mod C R} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ Mod.regular R) :
    PreservesFiniteLimits (Mod.tensorLeft M) := by
  let H := Functor.const (Discrete (Fin n)) ⋙
    (lim : (Discrete (Fin n) ⥤ Mod C R) ⥤ Mod C R)
  let L := Functor.const (Discrete (Fin n)) ⋙
    (colim : (Discrete (Fin n) ⥤ Mod C R) ⥤ Mod C R)
  let d : Mod.ihom M ≅ H :=
    (Mod.ihomMapIso e).symm ≪≫ Mod.ihomFreePowerIso n
  let adj : L ⊣ H := (constLimAdj).comp (colimConstAdj)
  let t : Mod.tensorLeft M ≅ L :=
    (Mod.ihomAdjunction M).leftAdjointUniq (adj.ofNatIsoRight d.symm)
  have : PreservesFiniteLimits
      (colim : (Discrete (Fin n) ⥤ Mod C R) ⥤ Mod C R) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  have : PreservesFiniteLimits L := inferInstance
  exact preservesFiniteLimits_of_natIso t.symm

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale
attribute [local instance] Sheaf.symmetricCategory

private noncomputable def pullTensorIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    let F := (upperStar Ab.{u + 1} g).mapMod R
    Mod.tensorLeft P ⋙ F ≅ F ⋙ Mod.tensorLeft (F.obj P) := by
  let G := upperStar Ab.{u + 1} g
  let φ := 𝟙 (G.obj R)
  let F := Mod.mapModComap (G := G) φ
  let F' := G.mapMod R
  let c : F ≅ F' := NatIso.ofComponents
    (fun M ↦ Mod.isoMk (Iso.refl _) (by simp [F, F', φ, Mod.act]))
    (fun f ↦ by ext : 1; rfl)
  have : PreservesColimitsOfShape WalkingParallelPair F := by
    dsimp [F, Mod.mapModComap]
    infer_instance
  let d := Mod.tensorLeftCompMapModComapIso φ
    (fun M N ↦ Functor.LaxBraided.braided (F := G) M N) P
  exact Functor.isoWhiskerLeft _ c.symm ≪≫ d ≪≫
    Functor.isoWhiskerRight c _ ≪≫
      Functor.isoWhiskerLeft F' (Mod.tensorLeftMapIso (c.app P))

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Limits
universe x y
private theorem isIso_map_lift_of_preserves
    {A B C : Type*} [Category A] [Category B] [Category C]
    {J : Type x} [Category.{y} J] (D : J ⥤ A) (H : A ⥤ B) (F : B ⥤ C)
    [HasLimit D] [HasLimit (D ⋙ H)]
    [PreservesLimit D (H ⋙ F)] [PreservesLimit (D ⋙ H) F] :
    IsIso (F.map (limit.lift _ (H.mapCone (limit.cone D)))) := by
  let hc : IsLimit (F.mapCone (H.mapCone (limit.cone D))) :=
    (isLimitOfPreserves (H ⋙ F) (limit.isLimit D)).ofIsoLimit
      (Functor.mapConeMapCone (limit.cone D)).symm
  let hd := isLimitOfPreserves F (limit.isLimit (D ⋙ H))
  let e := hc.conePointUniqueUpToIso hd
  have he : F.map (limit.lift _ (H.mapCone (limit.cone D))) = e.hom := by
    apply hd.hom_ext
    intro s
    change F.map (limit.lift _ (H.mapCone (limit.cone D))) ≫
      F.map (limit.π (D ⋙ H) s) = _
    rw [← F.map_comp, limit.lift_π]
    exact (hd.fac (F.mapCone (H.mapCone (limit.cone D))) s).symm
  rw [he]
  infer_instance
end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
attribute [local instance] Mod.isGrothendieckAbelian

/-- Tensoring with a module trivialized as finite free by a pro-etale cover is left
exact.  It is already right exact because it is left adjoint to internal Hom.
Source: Stacks Project, Tag 08JJ; Hemo--Richarz--Scholbach, Lemma 5.3(2).
(auxiliary; not a blueprint node)

Proof: on a trivializing cover, internal Hom is the finite-power functor.  The
finite-copower functor is its left adjoint and is also a finite-power functor;
uniqueness of left adjoints identifies tensor with that exact functor.  Pullback
commutes with module tensor, as follows from its coequalizer construction, and
preserves finite limits.  Thus every pullback of the limit comparison is invertible.
The restrictions along a cover jointly reflect isomorphisms, so the comparison
itself is invertible.  This argument includes rank zero and the empty scheme. -/
theorem condensed_locally_free_tensor_preservesFiniteLimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : IsLocallyFree R P) :
    PreservesFiniteLimits (Mod.tensorLeft P) := by
  obtain ⟨C, hC⟩ := hP
  have (s : C.I₀) : WeaklyEtale (C.f s) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
  refine ⟨fun {J} _ _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  have h : IsIso (limit.lift _ ((Mod.tensorLeft P).mapCone (limit.cone D))) := by
    apply isIso_mapMod_of_cover C R
    intro s
    let F := (upperStar Ab.{u + 1} (C.f s)).mapMod R
    have : PreservesFiniteLimits F := by
      refine ⟨fun J _ _ ↦ ?_⟩
      let forgetY :
          Mod (Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
              ((upperStar Ab.{u + 1} (C.f s)).obj R) ⥤
            Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1} := Mod.forget _
      have : PreservesLimitsOfShape J (F ⋙ forgetY) :=
        inferInstanceAs (PreservesLimitsOfShape J
          (Mod.forget R ⋙ upperStar Ab.{u + 1} (C.f s)))
      exact preservesLimitsOfShape_of_reflects_of_preserves F forgetY
    obtain ⟨n, ⟨e⟩⟩ := hC s
    have : PreservesFiniteLimits (Mod.tensorLeft (F.obj P)) :=
      Mod.tensor_finiteFree_preservesFiniteLimits e
    have : PreservesLimit D (Mod.tensorLeft P ⋙ F) :=
      preservesLimit_of_natIso D (pullTensorIso (C.f s) R P).symm
    exact isIso_map_lift_of_preserves D (Mod.tensorLeft P) F
  obtain ⟨hc⟩ := (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.2 h
  exact preservesLimit_of_preserves_limit_cone (limit.isLimit D) hc

end AlgebraicGeometry.ProEtale
