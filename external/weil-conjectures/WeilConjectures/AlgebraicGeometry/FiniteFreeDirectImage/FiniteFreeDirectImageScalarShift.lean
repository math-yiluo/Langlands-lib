/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Counit-compatible shifts of normalized scalar models

Source: Stacks Project, Tags 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- The normalized scalar adjunction gives the universal counit's shift structure.
Source: Stacks Project, Tags 06YY and 07A6.
(blueprint: lem-sp-finite-free-scalar-shift).

Proof: the inverse mate of the exact restriction factorization commutes with shifts,
since the ordinary and derived scalar adjunctions do. The unit normalization
identifies that inverse mate with the universal counit on flat-term K-flat
complexes. Resolve any complex by one of these; naturality and invertibility of
the localized resolution extend the equality to all complexes. Thus the universal
counit commutes with shifts. Exact restriction induces a triangulated functor.
The left adjoint of this triangulated functor, with the specified compatible shift,
is triangulated as well. -/
theorem finiteFreeDirectImageScalarShift {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (s.presentation a).derived.IsTriangulated ∧
      NatTrans.CommShift (s.presentation a).counit ℤ := by
  let p := s.presentation a
  let ah := (s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)
  let ad := s.adjunction a
  let : ad.CommShift ℤ := ad.commShift_of_rightAdjoint ℤ
  let : ah.CommShift ℤ := Adjunction.CommShift.mk' ah (A := ℤ) inferInstance
  let β := (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.inv
  let τ := ((mateEquiv ah ad).symm (TwoSquare.mk _ _ _ _ β))
  have hτshift : NatTrans.CommShift τ ℤ := by
    dsimp only [τ, mateEquiv, Equiv.symm, Equiv.coe_fn_mk, TwoSquare.mk]
    infer_instance
  have hflat (P : CochainComplex (proEtaleRingModules X R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology X) (R := R) P)
      (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := ProEt.topology X) (R := R) (P.X i)) :
      τ.app ((HomotopyCategory.quotient _ _).obj P) =
        p.counit.app ((HomotopyCategory.quotient _ _).obj P) := by
    apply (ad.homEquiv _ _).injective
    have hm := unit_mateEquiv_symm ah ad (TwoSquare.mk _ _ _ _ β)
      ((HomotopyCategory.quotient _ _).obj P)
    change DerivedCategory.Qh.map (ah.unit.app _) ≫ β.app _ =
      ad.unit.app _ ≫ (proEtaleRingRestrictScalars a).mapDerivedCategory.map (τ.app _) at hm
    dsimp only [Functor.id_obj] at hm
    have hn := s.adjunction_unit a P hP hf
    apply (cancel_mono ((proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
      ((p.ordinary.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))).mp
    simp only [Adjunction.homEquiv_unit]
    rw [← hm]
    dsimp only [p, ah, ad]
    simp only [β, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hn.symm
  have heq : τ = p.counit := by
    ext H
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    obtain ⟨K, f, hK, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (J := ProEt.topology X) (R := R) P
    have hflatK : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := ProEt.topology X) (R := R) (K.X i) := by
      intro i
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (K.X i)).symm (hf i)
    let q := HomotopyCategory.quotient (proEtaleRingModules X R) (.up ℤ)
    have hi : IsIso (DerivedCategory.Qh.map (q.map f)) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ)) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hq)
    apply (cancel_epi (p.derived.map (DerivedCategory.Qh.map (q.map f)))).mp
    rw [← CategoryTheory.Functor.comp_map, τ.naturality, p.counit.naturality, hflat K hK hflatK]
  have hc : NatTrans.CommShift p.counit ℤ := heq ▸ hτshift
  exact ⟨(s.adjunction a).isTriangulated_leftAdjoint, hc⟩

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
