/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeChain
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientFlatSequence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The strict quotient augmentation is a quasi-isomorphism on K-flat complexes

Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YS and 06YY.
(blueprint: lem-cbc-regular-quotient-cone-quasi-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
  (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
    ringMap φ = 0)
  (hexact : (ShortComplex.mk
    ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
    (ringMap φ) ht).ShortExact)
  (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
  (adj : d.E ⊣ restriction φ)
  (hsections : ∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U),
    (eqToHom (d.obj_eq M)).val.app U ((adj.unit.app M).val.app U x) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory

include hexact hsections in
/-- The normalized zero-shifted-component augmentation computes the quotient on all K-flats.

Source: Stacks Project, Tags 06YP, 06YS and 06YY
(blueprint: lem-cbc-regular-quotient-cone-quasi-iso).

Proof: For a complex with flat terms, tensor the coefficient-ring short exact sequence
in each degree. The normalized tensor comparisons identify it with multiplication by t
followed by the termwise coefficient unit. Thus its cone augmentation is the standard
quasi-isomorphism associated to a short exact sequence of complexes. For arbitrary
K-flat P choose a flat-term K-flat resolution F → P. Scalar cones preserve every
quasi-isomorphism; ordinary extension preserves those between K-flat complexes, and
restriction is exact. Naturality of the strict augmentation makes its two composites
with these maps equal. Three of the maps are quasi-isomorphisms, so the fourth is too. -/
theorem chainAugmentation_quasiIso
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    QuasiIso ((chainAugmentation t _ (coefficientUnit φ d.E adj)
      (coefficientUnit_zero t φ d.E adj ht)).app P) := by
  classical
  let T := d.E.mapHomologicalComplex (.up ℤ) ⋙
    (restriction φ).mapHomologicalComplex (.up ℤ)
  let ρ := coefficientUnit φ d.E adj
  let a := chainAugmentation t T ρ (coefficientUnit_zero t φ d.E adj ht)
  have hflat (K : CochainComplex (Modules R) ℤ)
      (hK : ∀ n : ℤ, exactFunctor _ _ (tensorRight (K.X n))) :
      QuasiIso (a.app K) := by
    let seq := ShortComplex.mk ((complexScalar R t).app K) (ρ.app K)
      (coefficientUnit_zero t φ d.E adj ht K)
    have hseq : seq.ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro n
      let η := adj.unit.app (K.X n) ≫
        (restriction φ).map (eqToHom (d.obj_eq (K.X n)))
      have hz : (scalar R t).app (K.X n) ≫ η = 0 := by
        dsimp only [η]
        rw [← Category.assoc]
        have he := congrArg (fun f ↦ f.f n) (coefficientUnit_zero t φ d.E adj ht K)
        change (scalar R t).app (K.X n) ≫ adj.unit.app (K.X n) = 0 at he
        rw [he, zero_comp]
      have hs := coefficient_shortExact_of_flat φ t ht hexact (K.X n) (hK n) η
        (hsections (K.X n)) hz
      let e : (ShortComplex.mk ((scalar R t).app (K.X n)) η hz) ≅
          seq.map (HomologicalComplex.eval (Modules R) (.up ℤ) n) :=
        ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          ((restriction φ).mapIso (eqToIso (d.obj_eq (K.X n)))).symm
          (by rfl) (by simp [η, seq, ρ, coefficientUnit])
      exact ShortComplex.shortExact_of_iso e hs
    have he : a.app K = CochainComplex.mappingCone.descShortComplex seq := by rfl
    rw [he]
    exact CochainComplex.mappingCone.quasiIso_descShortComplex hseq
  obtain ⟨K, p, hK, hterms, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  have := hflat K hterms
  have := cone_quasiIso t p hp
  have := d.preserves p hK hP hp
  have hT : QuasiIso (T.map p) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ (restriction φ)
  have hcomp : QuasiIso ((cone R t).map p ≫ a.app P) := by
    rw [a.naturality p]
    infer_instance
  exact quasiIso_of_comp_left ((cone R t).map p) (a.app P)

end SheafOfModules.RegularQuotientCone
