import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardGenericBasisStatement
import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardStructureProof
import Langlands.AlgebraicGeometry.Modules.AffinePullbackQuasicoherent
import Mathlib.RingTheory.Localization.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Generic trivialization of the actual finite-flat pushforward -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

open AffineVanishing Langlands.Cohomology

private def affineChartSectionsEquiv {Y : Scheme.{u}} (M : Y.Modules)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    (moduleSpecΓFunctor (R := Γ(Y, U))).obj (M.restrict hU.fromSpec) ≃ₗ[Γ(Y, U)]
      Γ(M, U) := by
  let h := image_fromSpec_top hU
  let e := M.restrictAppIso hU.fromSpec ⊤ ≪≫
    M.presheaf.mapIso (eqToIso h.symm).op
  let l : (moduleSpecΓFunctor (R := Γ(Y, U))).obj (M.restrict hU.fromSpec) →ₗ[Γ(Y, U)]
      Γ(M, U) := {
    toFun := fun m => Cech.res h.ge ((M.restrictAppIso hU.fromSpec ⊤).hom m)
    map_add' := by intro a b; simp
    map_smul' := by
      intro r m
      rw [restrictAppIso_hom_smul, res_smul, rres_rres, rres_self]
      rfl
  }
  exact LinearEquiv.ofBijective l (ConcreteCategory.bijective_of_isIso e.hom)

private lemma exists_free_tensor_away {R M : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r)
      (Localization.Away r ⊗[R] M) ∧
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] M) =
        Module.finrank R M := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨r, hr, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) (TensorProduct.mk R (FractionRing R) M 1) (FractionRing R)
  let e := LocalizedModule.equivTensorProduct (.powers r) M
  let : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, Module.Free.of_equiv e, ?_⟩
  exact e.finrank_eq.symm.trans
    (hrank.trans (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq)

/-- The generic free chart has the actual native rank. -/
theorem finiteFlatPushforwardGenericBasis :
    FiniteFlatPushforwardGenericBasisStatement.{u} := by
  intro X Y f hf hflat hY hN x
  let : IsFinite f := hf
  let : Flat f := hflat
  let : IsIntegral Y := hY
  let : IsLocallyNoetherian Y := hN
  let P := (Scheme.Modules.pushforward f).obj (Langlands.Scheme.Modules.structureSheaf X)
  obtain ⟨hP, hfinite, hrank⟩ := finiteFlatPushforwardStructure X Y f hf hflat
  let : P.IsQuasicoherent := hP
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Y.Opens) from trivial)
  let A := Γ(Y, U)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : IsDomain A := IsIntegral.component_integral U
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let M := P.restrict hU.fromSpec
  let N := (moduleSpecΓFunctor (R := A)).obj M
  let e := affineChartSectionsEquiv P hU
  let : Module.Finite A Γ(P, U) := (hfinite ⟨U, hU⟩).1
  let : Module.Finite A N := Module.Finite.equiv e.symm
  have hrankN : Module.finrank A N = f.finrank x :=
    e.finrank_eq.trans (hrank hY ⟨U, hU⟩ x hxU)
  obtain ⟨r, hr, hfree, hdim⟩ := exists_free_tensor_away (R := A) (M := N)
  let Ar := Localization.Away r
  let : IsDomain Ar := Localization.Away.isDomain hr
  let : Module.Free Ar (Ar ⊗[A] N) := hfree
  let φ : A ⟶ CommRingCat.of Ar := CommRingCat.ofHom (algebraMap A Ar)
  let a := Spec.map φ
  let g := a ≫ hU.fromSpec
  let b : Module.Basis (ULift.{u} (Fin (f.finrank x))) Ar (Ar ⊗[A] N) :=
    (Module.finBasisOfFinrankEq Ar (Ar ⊗[A] N)
    (hdim.trans hrankN)).reindex (Equiv.ulift.symm)
  let E : P.restrict g ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of Ar)).ringCatSheaf)
        (ULift.{u} (Fin (f.finrank x))) :=
    (Scheme.Modules.restrictFunctorComp a hU.fromSpec).app P ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫
      Langlands.Scheme.Modules.affinePullbackTildeIso φ M ≪≫
      (tilde.functor (CommRingCat.of Ar)).mapIso
        (Langlands.Scheme.Modules.extendScalarsAlgebraIso A (CommRingCat.of Ar) N) ≪≫
      (tilde.functor (CommRingCat.of Ar)).mapIso b.repr.toModuleIso ≪≫
      tildeFinsupp (ULift.{u} (Fin (f.finrank x)))
  let V := g.opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange g
  have hnonempty : Set.Nonempty (V : Set Y) := by
    obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Ar)))
    exact ⟨g p, ⟨p, rfl⟩⟩
  have hrange : Set.range g = Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let i := IsOpenImmersion.isoOfRangeEq g V.ι hrange
  refine ⟨⟨V, hV⟩, hnonempty, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorCongr
      (IsOpenImmersion.isoOfRangeEq_inv_fac g V.ι hrange).symm).app P ≪≫
    (Scheme.Modules.restrictFunctorComp i.inv g).app P ≪≫
    (Scheme.Modules.restrictFunctor i.inv).mapIso E ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback i.inv).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso i.inv.toRingCatSheafHom
      (ULift.{u} (Fin (f.finrank x)))

end Langlands.AlgebraicGeometry.Modules
