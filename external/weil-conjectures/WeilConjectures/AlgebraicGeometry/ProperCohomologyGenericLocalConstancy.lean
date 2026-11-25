/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import WeilConjectures.CategoryTheory.Etale.EtaleLisseFiltrationDevissage
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekNaturalSES
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteEtaleFiltration
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLineLisseFiniteComplement
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.Compactification.CompactificationCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Compactification.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekRelativeMayerVietoris
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleEtaleModuleQcqsAffineLocal
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
import WeilConjectures.AlgebraicGeometry.SmoothAffineCurveConstantShriekConstructible
import WeilConjectures.AlgebraicGeometry.Lisse.LisseOpenRelativeLineConstructibility
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.PID
import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-!
# Proper generic local constancy

The private helpers adapt the proofs of finite-ring compact-support constructibility
from LisseOpenRelativeLineConstructibility, EtaleAffineLineShriekFiniteTypeDenseOpen,
EtaleAffineLineShriekSheafConstructible, and EtaleCompactificationConstructibility.
They use the all-characteristic smooth-curve input (Stacks 0GKX) for finite fields.
-/

@[expose] public section

set_option autoImplicit false

universe u' u


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

namespace AlgebraicGeometry.Etale.C4Lisse

set_option backward.isDefEq.respectTransparency true

section StableInstances

attribute [local instance 2000] etaleSheafModuleAbelian

attribute [local instance 2000] etaleSheafModuleHasDerivedCategory

-- Stalk calculation adapted from Bin Wu, FiniteEtaleModuleTraceData.
private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
  have := h
  exact Scheme.IsConstructibleSheaf.of_iso e⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).ContainsZero :=
  ⟨0, isZero_zero _, Scheme.IsConstructibleSheaf.of_isZero (isZero_zero _)⟩

private instance (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderKernels := ⟨by
  rintro _ ⟨f, k, hk, hX, hY⟩
  have := hX
  have := hY
  have := Scheme.IsConstructibleSheaf.kernel f
  exact Scheme.IsConstructibleSheaf.of_iso (F := kernel f)
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk)⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderCokernels := ⟨by
  rintro _ ⟨f, k, hk, hX, hY⟩
  have := hX
  have := hY
  have := Scheme.IsConstructibleSheaf.cokernel f
  exact Scheme.IsConstructibleSheaf.of_iso (F := cokernel f)
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk)⟩

private instance (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ by
  have := h₁
  have := h₃
  exact Scheme.IsConstructibleSheaf.of_shortExact h⟩

private noncomputable instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).CommShift ℤ := by
  unfold shriekFunctor
  infer_instance

private instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).Additive := by
  unfold shriekFunctor
  infer_instance

private instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).IsTriangulated := by
  unfold shriekFunctor
  infer_instance


private theorem shriek_comp
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cgf : Compactification (f ≫ g)) :
    Nonempty
      (shriekFunctor (ModuleCat.{u + 1} Λ) cf ⋙
        shriekFunctor (ModuleCat.{u + 1} Λ) cg ≅
        shriekFunctor (ModuleCat.{u + 1} Λ) cgf) := by
  unfold shriekFunctor
  exact nonempty_iso_etaleShriek_qcqs_compactification_comp Λ f g cf cg cgf

private instance {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (plusProperty P).IsClosedUnderIsomorphisms := by rw [plusProperty_eq]; infer_instance

private instance {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (plusProperty P).IsTriangulated := by rw [plusProperty_eq]; infer_instance

private noncomputable instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceFunctor A c).Additive := by
  unfold sourceFunctor
  infer_instance

private theorem constant_shriek
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated h] [IsAffineHom h] [SmoothOfRelativeDimension 1 h]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (c : Compactification h) [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((sourceFunctor (ModuleCat.{u + 1} Λ) c).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))  := by
  unfold sourceFunctor shriekFunctor
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hdim : topologicalKrullDim (Spec (.of A)) ≠ ⊤ := by
    change topologicalKrullDim (PrimeSpectrum A) ≠ ⊤
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
      (inferInstance : Algebra.FiniteType ℤ A)
    apply ne_top_of_le_ne_top ?_ (ringKrullDim_le_of_surjective g.toRingHom hg)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
    have hz : ringKrullDim ℤ ≤ 1 := by
      rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    apply ne_top_of_le_ne_top (show (1 : WithBot ℕ∞) + (Nat.card (Fin n) : WithBot ℕ∞) ≠ ⊤ by
      rw [← Nat.cast_one, ← Nat.cast_add]
      rw [← WithBot.coe_natCast, Ne, WithBot.coe_eq_top]
      exact ENat.natCast_ne_top _)
    rw [add_comm, add_comm 1]
    exact add_le_add_right hz _
  exact constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one_all_char
    (ringChar Λ) Λ (Spec (.of A)) hdim X h M c q

private abbrev sourceProperty (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  cohomologySourceProperty (ModuleCat.{u + 1} Λ) (constructibleProperty Λ Y) c

private instance (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceProperty Λ c).IsClosedUnderIsomorphisms := by
  unfold sourceProperty cohomologySourceProperty
  infer_instance

private instance (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceProperty Λ c).IsClosedUnderFiniteProducts := by
  apply ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape.{0}
  intro J _
  have : PreservesLimitsOfShape (Discrete.{0} J) (sourceFunctor (ModuleCat.{u + 1} Λ) c) :=
    preservesProductsOfShape_of_preservesBiproductsOfShape _
  unfold sourceProperty cohomologySourceProperty
  infer_instance

private theorem source_open_hom_comp
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X' X Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : X' ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (ca : Compactification (j ≫ f)) :
    Nonempty (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙
      sourceFunctor (ModuleCat.{u + 1} Λ) c ≅
        sourceFunctor (ModuleCat.{u + 1} Λ) ca) := by
  obtain ⟨ec⟩ := shriek_comp Λ j f (Compactification.ofIsOpenImmersion j) c ca
  unfold sourceFunctor
  exact ⟨single_composite_iso _ _ (shriekOpenIso _ j) ec⟩

private theorem source_proper_comp
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X' X Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X' ⟶ X) [IsProper g]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) g)]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (ca : Compactification (g ≫ f)) :
    Nonempty (lowerStar (ModuleCat.{u + 1} Λ) g ⋙
      sourceFunctor (ModuleCat.{u + 1} Λ) c ≅
        sourceFunctor (ModuleCat.{u + 1} Λ) ca) := by
  obtain ⟨ec⟩ := shriek_comp Λ g f (Compactification.ofIsProper g) c ca
  unfold sourceFunctor
  exact ⟨single_composite_iso _ _ (shriekProperIso _ g) ec⟩

private theorem sourceProperty_openExtension
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (T : X.Opens) (hT : IsCompact (T : Set X))
    (ca : Compactification (T.ι ≫ f))
    (Q : Sheaf T.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : sourceProperty Λ ca Q) :
    sourceProperty Λ c ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).obj Q) := by
  have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  have : QuasiSeparatedSpace T.toScheme := T.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨e⟩ := source_open_hom_comp Λ T.ι f c ca
  exact (prop_iff_of_natIso (plusProperty (constructibleProperty Λ Y)) e Q).mpr h

private theorem sourceProperty_shortExact_three
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : S.ShortExact) (h₁ : sourceProperty Λ c S.X₁)
    (h₂ : sourceProperty Λ c S.X₂) : sourceProperty Λ c S.X₃ := by
  exact (sourceFunctor_shortExact (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ Y) S hS).2 h₁ h₂

private theorem shriekProperty_shortExact
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : S.ShortExact)
    (h₁ : sourceProperty Λ c S.X₁)
    (h₃ : sourceProperty Λ c S.X₃) :
    sourceProperty Λ c S.X₂ := by
  exact (sourceFunctor_shortExact (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ Y) S hS).1 h₁ h₃

private theorem shriekProperty_filtration
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsAffineHom f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (c : Compactification f)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : ℕ) (F : Fin (r + 1) → Subobject L) (hF : Monotone F)
    (h₀ : IsZero (F 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hᵣ : F (Fin.last r) = ⊤)
    (hQ : ∀ i : Fin r, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ)
        (hF (Fin.castSucc_le_succ i))) ≅
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    sourceProperty Λ c L := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  apply sourceFunctor_filtration (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ (Spec (.of R)))
    (fun M : ModuleCat.{u + 1} Λ ↦
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (fun M ↦ Finite M) L r F hF h₀ hᵣ hQ
  intro M hM q
  have := hM
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (constant_shriek Λ R f M c q)

private theorem shriekProperty_disjoint
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (U : Fin n → X.Opens)
    (hdisj : Pairwise (fun a b ↦ Disjoint (U a) (U b)))
    (hcover : (⋃ a, (U a : Set X)) = Set.univ)
    (hcompact : ∀ a, IsCompact (U a : Set X))
    (hlocal : ∀ a (ca : Compactification ((U a).ι ≫ f)),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) (U a).ι).obj L))) :
    sourceProperty Λ c L := by
  classical
  let A := ModuleCat.{u + 1} Λ
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology A) := abelian_hasFiniteBiproducts
  let G (a : Fin n) := (openImmersionLowerShriek A (U a).ι).obj
    ((upperStar A (U a).ι).obj L)
  have htop : (⨆ a, U a) = ⊤ := by
    apply SetLike.coe_injective
    simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using hcover
  have : IsIso (⨆ a, U a).ι := by
    rw [htop]
    exact (inferInstance : IsIso X.topIso.hom)
  obtain ⟨e⟩ := disjointOpenExtension_biproduct_iso Λ L n U
    (fun _ _ h ↦ TopologicalSpace.Opens.coe_disjoint.mpr (hdisj h))
  let eL : L ≅ ⨁ G :=
    (asIso ((openImmersionLowerShriekUpperStarAdjunction A (⨆ a, U a).ι).counit.app L)).symm
      ≪≫ e
  have hG (a : Fin n) : sourceProperty Λ c (G a) := by
    have : CompactSpace (U a).toScheme := isCompact_iff_compactSpace.mp (hcompact a)
    have : QuasiSeparatedSpace (U a).toScheme :=
      (U a).ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨ca⟩ :=
      (inferInstance : HasCompactification ((U a).ι ≫ f)).nonempty_compactification
    exact sourceProperty_openExtension Λ f c (U a) (hcompact a) ca _ (hlocal a ca)
  apply (sourceProperty Λ c).prop_of_iso eL.symm
  exact objectProperty_map_biproduct (sourceFunctor A c)
    (plusProperty (constructibleProperty Λ Y)) G hG

private theorem shriekProperty_affine_prime
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : Spec (.of A) ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (L : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hL : ℓ • 𝟙 L = 0) (c : Compactification f) :
    sourceProperty Λ c L := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨T, g, hgfin, hget, hgsurj, d, hdpos, hd, hdeg,
    k, U, hU, hdisj, hcover, hfil⟩ :=
    exists_lisse_finiteEtale_filtration A Λ L ℓ 1 hℓ (by omega) (by simpa using hL)
  have := hgfin
  have := hget
  have : IsAffine T := isAffine_of_isAffineHom g
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  let B := ModuleCat.{u + 1} Λ
  let G := (upperStar B g).obj L
  let cg := Compactification.ofIsProper g
  have : SmoothOfRelativeDimension 1 (g ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (g ≫ f))
  obtain ⟨cf⟩ :=
    (inferInstance : HasCompactification (g ≫ f)).nonempty_compactification
  have hG : sourceProperty Λ cf G := by
    apply shriekProperty_disjoint Λ (g ≫ f) cf G k U hdisj hcover
      (fun a ↦ (hU a).1.isCompact)
    intro a ca
    have : IsAffine (U a).toScheme := (hU a).1
    have : IsClosedImmersion (U a).ι :=
      IsClosedImmersion.of_isPreimmersion (U a).ι (by simpa using (hU a).2)
    have : SmoothOfRelativeDimension 0 ((U a).ι ≫ g) := inferInstance
    have : SmoothOfRelativeDimension 1 ((U a).ι ≫ g ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((U a).ι ≫ (g ≫ f)))
    obtain ⟨r, F, hF, h₀, hᵣ, hQ⟩ := hfil a
    exact shriekProperty_filtration Λ R ((U a).ι ≫ g ≫ f) ca
      ((upperStar B (U a).ι).obj G) r F hF h₀ hᵣ hQ
  obtain ⟨ecomp⟩ := source_proper_comp Λ g f c cf
  have hpush : sourceProperty Λ c ((lowerStar B g).obj G) :=
    (prop_iff_of_natIso (plusProperty (constructibleProperty Λ (Spec (.of R)))) ecomp G).mpr hG
  obtain ⟨t, ht⟩ := lisse_trace_degree Λ g L d hdeg
  obtain ⟨a, _, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((hℓ.coprime_iff_not_dvd.mpr hd).symm) hℓ.one_lt
  have hret : (upperStarLowerStarAdjunction B g).unit.app L ≫ (a • t) = 𝟙 L := by
    rw [Preadditive.comp_nsmul, ht, Nat.cast_smul_eq_nsmul, smul_smul, mul_comm a d,
      ← Nat.mod_add_div (d * a) ℓ, add_nsmul, ha, one_nsmul]
    have hz : (ℓ * (d * a / ℓ)) • 𝟙 L = 0 := by
      rw [mul_comm, mul_smul, hL, smul_zero]
    rw [hz, add_zero]
  let retract : Retract L ((lowerStar B g).obj G) :=
    ⟨(upperStarLowerStarAdjunction B g).unit.app L, a • t, hret⟩
  intro q
  let H := sourceFunctor B c ⋙ _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  have : Scheme.IsConstructibleSheaf (H.obj ((lowerStar B g).obj G)) := hpush q
  exact Scheme.IsConstructibleSheaf.of_retract (retract.map H)

private theorem shriekProperty_spec
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : Spec (.of A) ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (L : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f) :
    sourceProperty Λ c L := by
  classical
  let H : ObjectProperty (Sheaf (Spec (.of A)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) := Scheme.IsFiniteLocallyConstantSheaf
  have hk (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hF : H F) (r : ℕ) : H (kernel (r • 𝟙 F)) := by
    have : Scheme.IsFiniteLocallyConstantSheaf F := hF
    exact Scheme.IsFiniteLocallyConstantSheaf.kernel (r • 𝟙 F)
  have hi (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hF : H F) (r : ℕ) : H (image (r • 𝟙 F)) := by
    have : Scheme.IsFiniteLocallyConstantSheaf F := hF
    have := Scheme.IsFiniteLocallyConstantSheaf.kernel (r • 𝟙 F)
    have := Scheme.IsFiniteLocallyConstantSheaf.cokernel (kernel.ι (r • 𝟙 F))
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (Abelian.coimageIsoImage' (r • 𝟙 F))
  let : Fintype Λ := Fintype.ofFinite Λ
  apply objectProperty_of_nsmul_id_eq_zero (sourceProperty Λ c) H
    (shriekProperty_shortExact Λ c) hk hi
    (fun r hr F hF hkill ↦ by
      have : Scheme.IsFiniteLocallyConstantSheaf F := hF
      exact shriekProperty_affine_prime Λ R A f F r hr hkill c)
    (Fintype.card Λ) Fintype.card_pos L inferInstance
  rw [← Nat.cast_smul_eq_nsmul Λ, Nat.cast_card_eq_zero, zero_smul]

private theorem shriekProperty_iso_source
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X X' Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : X' ≅ X) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : Compactification f) (c' : Compactification (e.hom ≫ f))
    (h : sourceProperty Λ c' (((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L))) :
    sourceProperty Λ c L := by
  let B := ModuleCat.{u + 1} Λ
  obtain ⟨ec⟩ := source_open_hom_comp Λ e.hom f c c'
  apply (sourceProperty Λ c).prop_of_iso
    (asIso ((openImmersionLowerShriekUpperStarAdjunction B e.hom).counit.app L))
  exact (prop_iff_of_natIso (plusProperty (constructibleProperty Λ Y)) ec
    ((upperStar B e.hom).obj L)).mpr h

private theorem shriekProperty_affine
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f) :
    sourceProperty Λ c L := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let e := X.isoSpec.symm
  obtain ⟨c'⟩ :=
    (inferInstance : HasCompactification (e.hom ≫ f)).nonempty_compactification
  apply shriekProperty_iso_source Λ e f L c c'
  have : SmoothOfRelativeDimension 1 (e.hom ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.hom ≫ f))
  have : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L) :=
    Scheme.IsFiniteLocallyConstantSheaf.upperStar e.hom L
  exact shriekProperty_spec Λ R Γ(X, ⊤) (e.hom ≫ f)
    ((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L) c'

private theorem shriekProperty_sup
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (c : Compactification f)
    (hU : ∀ ca : Compactification (U.ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj L)))
    (hV : ∀ ca : Compactification (V.ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) V.ι).obj L)))
    (hW : ∀ ca : Compactification ((U ⊓ V).ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).obj L))) :
    sourceProperty Λ c L := by
  let B := ModuleCat.{u + 1} Λ
  have hlocal (T : X.Opens)
      (h : ∀ ca : Compactification (T.ι ≫ f),
        sourceProperty Λ ca ((upperStar B T.ι).obj L)) :
      sourceProperty Λ c ((openImmersionLowerShriek B T.ι).obj
        ((upperStar B T.ι).obj L)) := by
    have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (T : Set X))
    have : QuasiSeparatedSpace T.toScheme := T.ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨ca⟩ := (inferInstance : HasCompactification (T.ι ≫ f)).nonempty_compactification
    exact sourceProperty_openExtension Λ f c T
      (TopologicalSpace.NoetherianSpace.isCompact _) ca _ (h ca)
  obtain ⟨iU, iV, hS⟩ := exists_natural_shortExact_openCover_lowerShriek Λ U V hcover
  obtain ⟨hz, hs⟩ := hS L
  apply sourceProperty_shortExact_three Λ c _ hs (hlocal (U ⊓ V) hW)
  exact (sourceProperty Λ c).prop_of_iso (biprod.isoProd _ _).symm
    ((sourceProperty Λ c).prop_prod _ _ (hlocal U hU) (hlocal V hV))

private theorem shriekProperty_affine_cover
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (n : ℕ) :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of R))
      [IsSeparated f] [SmoothOfRelativeDimension 1 f]
      (U : Fin (n + 1) → X.Opens), (∀ i, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
      ∀ (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f),
        sourceProperty Λ c L := by
  induction n with
  | zero =>
    intro X _ f _ _ U hU hcov L _ c
    have h0 : U 0 = ⊤ := by simpa using hcov
    have : IsAffine X := by
      have : IsAffine (⊤ : X.Opens).toScheme := h0 ▸ hU 0
      exact .of_isIso X.topIso.inv
    exact shriekProperty_affine Λ R f L c
  | succ n ih =>
    intro X _ f _ _ U hU hcov L _ c
    have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    let V₁ : X.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let V₂ : X.Opens := U (Fin.last _)
    have hV : V₁ ⊔ V₂ = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hsep := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal f))
      ⊤ (isAffineOpen_top (Spec (.of R)))
    have hsm (W : X.Opens) : SmoothOfRelativeDimension 1 (W.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (W.ι ≫ f))
    have hnoeth (W : X.Opens) : IsNoetherian W.toScheme := by
      have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
      exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
    apply shriekProperty_sup Λ f L V₁ V₂ hV c
    · intro ca
      have := hsm V₁
      have := hnoeth V₁
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) V₁.ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar V₁.ι L
      have ha (i : Fin (n + 1)) : IsAffineOpen (V₁.ι ⁻¹ᵁ U i.castSucc) := by
        apply (hU _).preimage_of_isOpenImmersion
        rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
      have hc : (⨆ i : Fin (n + 1), V₁.ι ⁻¹ᵁ U i.castSucc) = ⊤ := by
        rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
      exact ih (X := V₁.toScheme) (V₁.ι ≫ f) (fun i ↦ V₁.ι ⁻¹ᵁ U i.castSucc)
        ha hc ((upperStar (ModuleCat.{u + 1} Λ) V₁.ι).obj L) ca
    · intro ca
      have : IsAffine V₂.toScheme := hU _
      have := hsm V₂
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) V₂.ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar V₂.ι L
      exact shriekProperty_affine Λ R (V₂.ι ≫ f)
        ((upperStar (ModuleCat.{u + 1} Λ) V₂.ι).obj L) ca
    · intro ca
      have := hsm (V₁ ⊓ V₂)
      have := hnoeth (V₁ ⊓ V₂)
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) (V₁ ⊓ V₂).ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar (V₁ ⊓ V₂).ι L
      have ha (i : Fin (n + 1)) :
          IsAffineOpen ((V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) := by
        apply (hsep _ (by simp) _ (by simp) (hU _) (hU _)).preimage_of_isOpenImmersion
        rw [Scheme.Opens.opensRange_ι]
        exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
      have hc : (⨆ i : Fin (n + 1), (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) = ⊤ := by
        rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]
      exact ih (X := (V₁ ⊓ V₂).toScheme) ((V₁ ⊓ V₂).ι ≫ f)
        (fun i ↦ (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) ha hc
        ((upperStar (ModuleCat.{u + 1} Λ) (V₁ ⊓ V₂).ι).obj L) ca

end StableInstances

private theorem isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((L.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (U.toScheme.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M))
    (c : Compactification
      (U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L))) := by
  classical
  let : ∀ X : Scheme.{u}, Abelian
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := etaleSheafModuleAbelian Λ
  let : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := etaleSheafModuleHasDerivedCategory Λ
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let X := U.toScheme
  let f := U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))
  have : SmoothOfRelativeDimension 1
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over
      (ULift.{u} (Fin 1)) (Spec (.of R))
  have : Smooth (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : SmoothOfRelativeDimension 1 f :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) f)
  have : Scheme.IsFiniteLocallyConstantSheaf L :=
    (Scheme.finite_locally_constant_module_values_iff L).1.mp hL
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (U : Set (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))))
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun W : X.affineOpens ↦ (W : Set X)) (fun W ↦ W.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨W, hW⟩)
  let V : Fin (s.card + 1) → X.Opens := Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  have hV (i : Fin (s.card + 1)) : IsAffineOpen (V i) := by
    induction i using Fin.cases with
    | zero => exact isAffineOpen_bot X
    | succ i => exact (s.equivFin.symm i).1.2
  have hcov : (⨆ i, V i) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa [V] using hx⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have h := shriekProperty_affine_cover Λ R s.card (X := X) f V hV hcov L c
  unfold sourceProperty cohomologySourceProperty sourceFunctor shriekFunctor at h
  exact h q

end AlgebraicGeometry.Etale.C4Lisse


open CategoryTheory

namespace AlgebraicGeometry.C4Dense

private theorem affineLine_shriek_constructible_of_finite_complement
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (hU : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F))
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))
    [IsClosedImmersion i] (hij : Set.range i.base = (Set.range U.ι.base)ᶜ)
    (hZ : IsFinite (i ≫
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (c : Compactification
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let Y := Spec (.of R)
  let X := AffineSpace (ULift.{u} (Fin 1)) Y
  let f : X ⟶ Y := X ↘ Y
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : TopologicalSpace.NoetherianSpace X := inferInstance
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set X))
  let cU := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u} (U.ι ≫ f)).1
  let cZ := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u} (i ≫ f)).1
  have : QuasiCompact cZ.i := cZ.quasiCompact_openImmersion inferInstance
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT, _⟩ :=
    Etale.exists_compactSupport_openClosed_triangle Λ f U.ι i hij K c cU cZ
  let P := _root_.DerivedCategory.homologyProperty
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y)
  have h₁ : P T.obj₁ := by
    intro n
    have hn := Etale.C4Lisse.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
      Λ R U ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F)
      ((Scheme.finite_locally_constant_module_values_iff _).1.mpr hU) cU n
    have hn' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hn
    let e := (Functor.mapDerivedCategoryPlusSingleFunctor
      (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι) 0).app F
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e₁ ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ n).mapIso
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} Λ) cU).mapIso e)).symm hn'
  have hqf : (i ≫ f).IsQuasiFinite :=
    ⟨inferInstance, inferInstance, fun x ↦
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp ((i ≫ f).quasiFiniteAt x)⟩
  have hK : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus).obj K)) := by
    intro n
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
    have hc := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0
    have hc' := Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar i hc
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc'.2 n)
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  have hz := Etale.constructibleCohomology_lowerShriek_of_quasiFinite Λ (i ≫ f)
    hqf _ hK cZ
  have h₃ : P T.obj₃ := by
    intro n
    have hn := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hz n)
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e₃).symm hn
  have h₂ := P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e₂) (h₂ q)


private theorem exists_dense_open_affineLine_shriek_constructible
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      Scheme.IsConstructibleEtaleModuleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F)))) := by
  classical
  obtain ⟨R, hR, hft, g, hg, hgd, U, hU, Z, i, hi, hij, hZ⟩ :=
    exists_dense_affine_open_lisse_finite_complement Λ Y F hF
  let c' := c.ofIsPullback (AffineSpace.isPullback_map g)
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ)
    (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
  have := Scheme.IsConstructibleSheaf.upperStar
    (AffineSpace.map (ULift.{u} (Fin 1)) g) F
  have hF' : Scheme.IsConstructibleEtaleModuleSheaf F' :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr inferInstance
  have hij' : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact hij
  have hc := affineLine_shriek_constructible_of_finite_complement
    Λ R F' hF' U hU i hij' hZ
    c' q
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let e := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    H.mapIso ((asIso
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ
        (AffineSpace.isPullback_map g) c)).app K) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback (AffineSpace.isPullback_map g))).mapIso
        (((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) g)).mapDerivedCategoryPlusSingleFunctor
          0).app F)) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso Λ
      (c.ofIsPullback (AffineSpace.isPullback_map g)) c').app _)
  have hsrc : Scheme.IsConstructibleSheaf
      (H.obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c').obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F)))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
  let G := (_root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hc' : Scheme.IsConstructibleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G) :=
    @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _ e.symm hsrc
  let V := g.opensRange
  have heq : Set.range g.base = Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; rfl
  let eV := IsOpenImmersion.isoOfRangeEq g V.ι heq
  refine ⟨V, hgd, ?_⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have hcPull := Scheme.IsConstructibleSheaf.upperStar eV.inv
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G)
  have hc'' := (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) V.toScheme).prop_of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) eV.inv g).app G).symm hcPull
  have heV : eV.inv ≫ g = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac g V.ι heq
  rw [heV] at hc''
  exact hc''


end AlgebraicGeometry.C4Dense


open CategoryTheory

namespace AlgebraicGeometry.C4Line

private theorem affineLine_constructible_descent
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
      (g : Y ⟶ Spec (.of R))
      (F₀ : Sheaf (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)),
      Scheme.IsConstructibleEtaleModuleSheaf F₀ ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F₀ ≅ F) :=
    open CategoryTheory.Limits in by
  classical
  let A := Γ(Y, ⊤)
  have : IsFiltered (Finset A) := inferInstance
  have : IsConnected (Finset A)ᵒᵖ := IsCofiltered.isConnected _
  let D := (finsetSubringDiagram A).op ⋙ Scheme.Spec
  let c₀ := Scheme.Spec.mapCone (finsetSubringCocone A).op
  have hc₀ : IsLimit c₀ :=
    isLimitOfPreserves Scheme.Spec (isColimitFinsetSubringCocone A).op
  let c : Cone D :=
    { pt := Y
      π := { app := fun j ↦ Y.isoSpec.hom ≫ c₀.π.app j
             naturality := by
               intro j k f
               simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                 Category.assoc] using congrArg (Y.isoSpec.hom ≫ ·) (c₀.w f).symm } }
  have hc : IsLimit c := IsLimit.ofIsoLimit hc₀
    (Cone.ext Y.isoSpec (by intro j; rfl)).symm
  let L := AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin 1)))
  let a : D ⋙ L ⟶ D :=
    { app := fun j ↦ AffineSpace (ULift.{u} (Fin 1)) (D.obj j) ↘ D.obj j
      naturality := by intros; exact AffineSpace.map_over _ }
  let cL := L.mapCone c
  have hcL : IsLimit cL := isLimitOfIsPullbackOfIsConnected a cL c
    { hom := AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y
      w := by intro j; exact (AffineSpace.map_over _).symm }
    (fun j ↦ AffineSpace.isPullback_map _) hc
  have htrans : ∀ {j k : (Finset A)ᵒᵖ} (f : j ⟶ k),
      IsAffineHom ((D ⋙ L).map f) := fun f ↦
    by
      change IsAffineHom (AffineSpace.map (ULift.{u} (Fin 1)) (D.map f))
      have : ∀ j, IsAffine (D.obj j) := fun j ↦ inferInstanceAs (IsAffine (Spec _))
      exact isAffineHom_of_isAffine _
  have hcompact : ∀ j, CompactSpace ((D ⋙ L).obj j) := fun j ↦
    inferInstanceAs (CompactSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec _)))
  have hqs : ∀ j, QuasiSeparatedSpace ((D ⋙ L).obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec _)))
  obtain ⟨j₀, F₀, hF₀, he₀⟩ :=
    Scheme.exists_constructible_etaleModuleSheaf_descent (D ⋙ L) cL hcL Λ F hF
  let R := Algebra.adjoin ℤ (j₀ : Set A)
  have : Algebra.FiniteType ℤ R :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset j₀)
  exact ⟨R, inferInstance, inferInstance, c.π.app (Opposite.op j₀), F₀, hF₀, he₀⟩


private theorem compactSupport_homology_baseChange_iso
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (c' : Compactification f')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Nonempty
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c').obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F)))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  exact ⟨((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    H.mapIso ((asIso
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)).app K) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback sq)).mapIso
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlusSingleFunctor
          0).app F)) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso Λ
      (c.ofIsPullback sq) c').app _)⟩

private theorem constructible_of_generic_closed_restrictions
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
      ∃ U : Z.Opens, Dense (U : Set Z) ∧
        Scheme.IsConstructibleEtaleModuleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G))) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr
  suffices h : ∀ C : TopologicalSpace.Closeds Y, ∀ (Z : Scheme.{u}) (i : Z ⟶ Y)
      [IsClosedImmersion i], Set.range i.base ⊆ C →
      Scheme.IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G) by
    have := h ⊤ Y (𝟙 Y) (Set.subset_univ _)
    exact Scheme.IsConstructibleSheaf.of_iso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Y).app G)
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).obj G)
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hZC
  have : TopologicalSpace.NoetherianSpace Z :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      i.isClosedEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  by_cases hZ : IsEmpty Z
  · exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  rw [not_isEmpty_iff] at hZ
  obtain ⟨U, hUd, hU⟩ := hG Z i
  let i' := Scheme.Opens.closedComplement U
  have hij : Set.range i'.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set Z))
  rw [Scheme.isConstructibleSheaf_iff_upperStar U.ι i' hij]
  refine ⟨(Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hU, ?_⟩
  let C' : TopologicalSpace.Closeds Y :=
    ⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain ⟨z, rfl⟩ := hx
      exact hZC ⟨_, rfl⟩
    · obtain ⟨z, hz⟩ := hUd.nonempty
      have hx : i.base z ∈ (C : Set Y) := hZC ⟨z, rfl⟩
      rw [← h] at hx
      obtain ⟨w, hw⟩ := hx
      rw [Scheme.Hom.comp_apply] at hw
      have hw' : z ∈ Set.range i'.base := ⟨w, i.isClosedEmbedding.injective hw⟩
      rw [hij] at hw'
      exact hw' ⟨⟨z, hz⟩, rfl⟩
  have := ih C' hC' _ (i' ≫ i) subset_rfl
  exact Scheme.IsConstructibleSheaf.of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i' i).app G)

private theorem affineLine_shriek_constructible_of_finiteType
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have : IsNoetherianRing Γ(Y, ⊤) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : TopologicalSpace.NoetherianSpace Y := noetherianSpace_of_isAffine
  apply constructible_of_generic_closed_restrictions Λ Y _
  intro Z i hi
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : Algebra.FiniteType ℤ Γ(Z, ⊤) := by
    let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
    have : Algebra.FiniteType Γ(Y, ⊤) Γ(Z, ⊤) :=
      (RingHom.finiteType_algebraMap).mp
        (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) i inferInstance)
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ Γ(Y, ⊤))
      (inferInstance : Algebra.FiniteType Γ(Y, ⊤) Γ(Z, ⊤))
  let g' := AffineSpace.map (ULift.{u} (Fin 1)) i
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F
  have hF' : Scheme.IsConstructibleEtaleModuleSheaf F' := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F').mpr
      (Scheme.IsConstructibleSheaf.upperStar g' F)
  let c' := c.ofIsPullback (AffineSpace.isPullback_map i)
  obtain ⟨U, hUd, hU⟩ := C4Dense.exists_dense_open_affineLine_shriek_constructible Λ Z F' hF' c' q
  obtain ⟨e⟩ := compactSupport_homology_baseChange_iso Λ (AffineSpace.isPullback_map i)
    c c' F q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hU
  exact ⟨U, hUd, (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (Scheme.IsConstructibleSheaf.of_iso
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).mapIso e).symm)⟩

private theorem isConstructibleEtaleModuleSheaf_affineLine_shriek
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  obtain ⟨R, hR, hft, g, F₀, hF₀, ⟨eF⟩⟩ :=
    affineLine_constructible_descent Λ Y F hF
  let c₀ := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u}
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))).1
  have : Algebra.FiniteType ℤ Γ(Spec (.of R), ⊤) :=
    Algebra.FiniteType.equiv hft
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toIntAlgEquiv
  have h₀ := affineLine_shriek_constructible_of_finiteType Λ (Spec (.of R)) F₀ hF₀ c₀ q
  obtain ⟨e⟩ := compactSupport_homology_baseChange_iso Λ (AffineSpace.isPullback_map g)
    c₀ c F₀ q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h₀
  have := Scheme.IsConstructibleSheaf.upperStar g
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c₀).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F₀)))
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (e ≪≫ (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).mapIso
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)))

end AlgebraicGeometry.C4Line


open CategoryTheory

namespace AlgebraicGeometry.Etale.C4Compact

private lemma constructible_compactSupport_of_sheaf
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) (c : Compactification f)
    (hsheaf : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Scheme.IsConstructibleSheaf F →
      DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) X K.obj) :
    DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj) := by
  let R := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c
  have hGE (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) [L.IsGE a] :
      (R.obj L).IsGE a := by
    have := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj L a
    exact Functor.isGE_rightDerivedFunctor_obj _ _ a
  intro n
  have hb : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K.obj) := by
    obtain ⟨a, ha⟩ := K.property
    have : K.obj.IsGE a := ha
    refine ⟨⟨⟨a, ?_⟩, ⟨n, inferInstance⟩⟩, ?_⟩
    · exact inferInstanceAs (_root_.DerivedCategory.TStructure.t.IsGE
        ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K.obj) a)
    · rw [DerivedCategory.constructibleHomology_eq] at hK ⊢
      exact _root_.DerivedCategory.homologyProperty_truncLE hK n
  have hbounded := prop_of_boundedConstructible
    ((DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y).inverseImage R)
    hsheaf hb
  let T := (_root_.DerivedCategory.TStructure.t.triangleLEGT n).obj K.obj
  have hT := _root_.DerivedCategory.TStructure.t.triangleLEGT_distinguished n K.obj
  have : T.obj₃.IsGE (n + 1) := inferInstanceAs
    (_root_.DerivedCategory.TStructure.t.IsGE
      ((_root_.DerivedCategory.TStructure.t.truncGT n).obj K.obj) (n + 1))
  have hR : (R.obj T.obj₃).IsGE (n + 1) := hGE T.obj₃ (n + 1)
  have : IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map (R.map T.mor₁)) :=
    _root_.DerivedCategory.isIso_homologyMap_mor₁ _ (R.map_distinguished _ hT)
      (n - 1) n (by omega)
      (_root_.DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega) (hX := hR))
      (_root_.DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega) (hX := hR))
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj (R.obj T.obj₁)) := hbounded n
  exact Scheme.IsConstructibleSheaf.of_iso
    (asIso ((_root_.DerivedCategory.homologyFunctor _ n).map (R.map T.mor₁)))


private lemma compactSupportPlus_of_sheaf
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) (c : Compactification f)
    (hsheaf : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Scheme.IsConstructibleEtaleModuleSheaf F → ∀ q : ℤ,
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  have htotal : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj) := by
    apply constructible_compactSupport_of_sheaf Λ f c ?_ K
      (fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hK q))
    intro F hF q
    have h := hsheaf F
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr hF) q
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} Λ) c).app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).mapIso
            ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app F)))
  intro q
  have := htotal q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj))
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c).app K)).symm

private lemma compactSupportPlus_comp
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (c : Compactification (f ≫ g))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K)))
    (hg : ∀ L : _root_.DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj L)) →
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj L))) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ f g cf cg c
  intro q
  have h := hg
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K) hf q
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K)))
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (e.app K))

private lemma compactSupportPlus_affineSpace
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (Y : Scheme.{u}) [IsAffine Y]
 (n : ℕ)
    (c : Compactification (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y))
    (K : _root_.DerivedCategory.Plus
      (Sheaf (AffineSpace (ULift.{u} (Fin n)) Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  induction n generalizing Y with
  | zero =>
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    exact constructibleCohomology_lowerShriek_of_isClosedImmersion Λ _ K hK c
  | succ n ih =>
    let N := ULift.{u} (Fin n)
    let L := ULift.{u} (Fin 1)
    let B := AffineSpace N Y
    let e : ULift.{u} (Fin (n + 1)) ≃ N ⊕ L :=
      Equiv.ulift.trans ((finSumFinEquiv (m := n) (n := 1)).symm.trans
        (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
    let E := (AffineSpace.reindexIso (S := Y) e.symm) ≪≫
      (AffineSpace.sumIso (n := N) (m := L) Y)
    let a : AffineSpace L B ⟶ B := AffineSpace L B ↘ B
    let b : B ⟶ Y := B ↘ Y
    have hfac : E.hom ≫ a ≫ b = AffineSpace (ULift.{u} (Fin (n + 1))) Y ↘ Y := by
      dsimp [E, a, b, B]
      rw [Category.assoc, AffineSpace.sumIso_hom_over_over]
      exact AffineSpace.reindex_over _ _
    let cE := Compactification.ofIsProper E.hom
    let ca : Compactification a := HasCompactification.compactification a
    let cb : Compactification b := HasCompactification.compactification b
    have : QuasiCompact cE.i := cE.quasiCompact_openImmersion inferInstance
    have hE := constructibleCohomology_lowerShriek_of_isClosedImmersion Λ E.hom K hK cE
    have ha : ∀ M : _root_.DerivedCategory.Plus
        (Sheaf (AffineSpace L B).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj M)) →
        ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ca).obj M)) := by
      intro M hM
      apply compactSupportPlus_of_sheaf Λ a ca ?_ M hM
      exact fun F hF q ↦
        AlgebraicGeometry.C4Line.isConstructibleEtaleModuleSheaf_affineLine_shriek
          Λ B F hF ca q
    let cEa : Compactification (E.hom ≫ a) := ca.precomp E.hom
    have hEa := compactSupportPlus_comp Λ E.hom a cE ca cEa K hE ha
    exact compactSupportPlus_comp Λ (E.hom ≫ a) b cEa cb
      (c.copy (by simpa [Category.assoc] using hfac)) K hEa (fun M hM ↦ ih Y cb M hM)

private lemma constructible_compactSupport_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top f
  let v : ULift.{u} (Fin s.card) → Γ(X, ⊤) := fun i ↦ (s.equivFin.symm i.down).val
  have hv : Set.range v = (s : Set Γ(X, ⊤)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i.down).property
    · intro hx
      exact ⟨⟨s.equivFin ⟨x, hx⟩⟩, by simp [v]⟩
  let i := AffineSpace.homOfVector f v
  let p : AffineSpace (ULift.{u} (Fin s.card)) Y ⟶ Y :=
    AffineSpace (ULift.{u} (Fin s.card)) Y ↘ Y
  have hi : IsClosedImmersion i := AffineSpace.isClosedImmersion_homOfVector f v
    (by rw [hv]; exact hs)
  have hfac : i ≫ p = f := AffineSpace.homOfVector_over f v
  have : LocallyOfFinitePresentation (i ≫ p) := hfac.symm ▸ inferInstance
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i p
  let ci := Compactification.ofIsProper i
  let cp : Compactification p := HasCompactification.compactification p
  have : QuasiCompact ci.i := ci.quasiCompact_openImmersion inferInstance
  have hci := constructibleCohomology_lowerShriek_of_isClosedImmersion Λ i K hK ci
  exact compactSupportPlus_comp Λ i p ci cp (c.copy hfac) K hci
    (fun M hM ↦ compactSupportPlus_affineSpace Λ Y s.card cp M hM)


private lemma constructible_pullback_complex
    {X T : Scheme.{u}} (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (g : T ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).obj K)) := by
  intro q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hK q)
  have := Scheme.IsConstructibleSheaf.upperStar g
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).app K)

private lemma constructible_compactSupport_of_cover
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    {Y : Scheme.{u}} [IsAffine Y]
 (n : ℕ) :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
      [QuasiCompact f] [QuasiSeparated f]
      (U : Fin (n + 1) → X.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      ∀ (c : Compactification f)
        (K : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  induction n with
  | zero =>
    intro X _ _ f _ _ _ _ U hU hcov c K hK
    have h0 : U 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup U 0) (iSup_le fun i ↦ by
        rw [(Fin.ext (by have := i.2; omega) : i = 0)])
    have : IsAffine X := by
      have h := hU 0
      rw [h0] at h
      have : IsAffine (⊤ : X.Opens).toScheme := h
      exact .of_isIso X.topIso.inv
    exact constructible_compactSupport_affine Λ f c K hK
  | succ n ih =>
    intro X _ _ f _ _ _ _ U hU hcov c K hK
    let V : X.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let W : X.Opens := U (Fin.last _)
    have hcover : V ⊔ W = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hV : IsCompact (V : Set X) := by
      change IsCompact ((⨆ i : Fin (n + 1), U i.castSucc : X.Opens) : Set X)
      rw [TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun i ↦ (hU i.castSucc).isCompact
    have hW : IsCompact (W : Set X) := (hU (Fin.last _)).isCompact
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
    have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
    have : QuasiSeparatedSpace W.toScheme := quasiSeparatedSpace_of_quasiSeparated W.ι
    have : CompactSpace (V ⊓ W).toScheme := by
      apply isCompact_iff_compactSpace.mp
      exact hV.inter_of_isOpen hW V.isOpen W.isOpen
    have : QuasiSeparatedSpace (V ⊓ W).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (V ⊓ W).ι
    let cV : Compactification (V.ι ≫ f) := c.precomp V.ι
    let cW : Compactification (W.ι ≫ f) := c.precomp W.ι
    let cVW : Compactification ((V ⊓ W).ι ≫ f) := c.precomp (V ⊓ W).ι
    have hsep := isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal f)) ⊤ (isAffineOpen_top Y)
    have hKV := constructible_pullback_complex Λ V.ι K hK
    have hKW := constructible_pullback_complex Λ W.ι K hK
    have hKVW := constructible_pullback_complex Λ (V ⊓ W).ι K hK
    have hUV (i : Fin (n + 1)) : U i.castSucc ≤ Scheme.Hom.opensRange V.ι := by
      rw [Scheme.Opens.opensRange_ι]
      exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
    have hcovV : ⨆ i : Fin (n + 1), V.ι ⁻¹ᵁ U i.castSucc = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup]
      exact Scheme.Opens.ι_preimage_self V
    have hRV := ih (V.ι ≫ f) (fun i ↦ V.ι ⁻¹ᵁ U i.castSucc)
      (fun i ↦ (hU _).preimage_of_isOpenImmersion _ (hUV i)) hcovV cV
      (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K) hKV
    have hUVW (i : Fin (n + 1)) :
        U i.castSucc ⊓ W ≤ Scheme.Hom.opensRange (V ⊓ W).ι := by
      rw [Scheme.Opens.opensRange_ι]
      exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
    have hcovVW : ⨆ i : Fin (n + 1), (V ⊓ W).ι ⁻¹ᵁ (U i.castSucc ⊓ W) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq]
      exact Scheme.Opens.ι_preimage_self (V ⊓ W)
    have hRVW := ih ((V ⊓ W).ι ≫ f)
      (fun i ↦ (V ⊓ W).ι ⁻¹ᵁ (U i.castSucc ⊓ W))
      (fun i ↦ (hsep _ (by simp) _ (by simp) (hU _) (hU _)).preimage_of_isOpenImmersion _
        (hUVW i)) hcovVW cVW
      (((upperStar (ModuleCat.{u + 1} Λ) (V ⊓ W).ι).mapDerivedCategoryPlus).obj K) hKVW
    have : IsAffine W.toScheme := hU _
    have hRW := constructible_compactSupport_affine Λ (W.ι ≫ f) cW
      (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K) hKW
    obtain ⟨α, β, δ, hT⟩ :=
      exists_distinguished_relativeMayerVietoris Λ f V W hV hW hcover cV cW cVW c K
    let T := Pretriangulated.Triangle.mk α β δ
    let P := (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y).inverseImage
      _root_.DerivedCategory.Plus.ι
    have : P.IsTriangulated := by
      dsimp [P]
      infer_instance
    have hP₁ : P T.obj₁ := fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRVW q)
    have hP₂ : P T.obj₂ := by
      intro q
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
              (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K))) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRV q)
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
              (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K))) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRW q)
      let H := _root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
      have hH : H.Additive := by
        dsimp [H, _root_.DerivedCategory.Plus.homologyFunctor]
        infer_instance
      let M := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)
      let N := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K)
      have : Limits.PreservesBinaryBiproducts H :=
        Limits.preservesBinaryBiproducts_of_preservesBiproducts H
      have := Scheme.IsConstructibleSheaf.biprod (H.obj M) (H.obj N)
      exact Scheme.IsConstructibleSheaf.of_iso
        (F := H.obj M ⊞ H.obj N) (H.mapBiprod M N).symm
    have hP₃ : P T.obj₃ := P.ext_of_isTriangulatedClosed₃ T hT hP₁ hP₂
    intro q
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hP₃ q)

private lemma compactSupportPlus_affineBase
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine Y]
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) (by
      intro x _
      have : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  let U : Fin (s.card + 1) → X.Opens :=
    Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  have hU : ∀ i, IsAffineOpen (U i) := by
    intro i
    induction i using Fin.cases with
    | zero => exact isAffineOpen_bot X
    | succ i => exact (s.equivFin.symm i).1.2
  have hcov : ⨆ i, U i = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa [U] using hx⟩
  exact constructible_compactSupport_of_cover Λ s.card f U hU hcov c K hK


private lemma constructible_of_affine_restrictions
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ W : Y.Opens, IsAffineOpen W →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G)) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  apply ((Scheme.constructible_etale_module_qcqs_affine_local G).out 2 3).mp
  refine ⟨{W | IsAffineOpen W}, ?_, ?_⟩
  · intro y
    obtain ⟨W, hW, hy⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨W, hW, hy.1⟩
  · intro W hW U hU
    have : IsAffine W.toScheme := hW
    have :=
      (Scheme.constructible_etale_module_qcqs_affine_local
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G)).out 3 1 |>.mp (hG W hW)
    obtain ⟨S, hS, hr, hf⟩ := this U hU
    refine ⟨S, hS, hr, fun k ↦ ?_⟩
    have := hf k
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (upperStar (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G))
      ((upperStarComp (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι) W.ι
        (S.immersion k ≫ U.ι ≫ W.ι) (Category.assoc _ _ _).symm).app G).symm

private lemma compactSupport_constructible_of_affine_base
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (q : ℤ)
    (hlocal : ∀ W : Y.Opens, IsAffineOpen W →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.baseChange W.ι)).obj
            (((upperStar (ModuleCat.{u + 1} Λ)
              (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus).obj K)))) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  apply constructible_of_affine_restrictions Λ
  intro W hW
  have hex := (compactSupportFiniteTorsion Λ (IsPullback.of_hasPullback f W.ι) c).1 K
  let e := (upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlusHomologyFunctorIso q
  have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (hlocal W hW)
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  let eout :=
    (((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ
        (IsPullback.of_hasPullback f W.ι) c).app K))).symm ≪≫
      (e.app ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)).symm)
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.ofIsPullback (IsPullback.of_hasPullback f W.ι))).obj K)) := by
    exact h
  exact Scheme.IsConstructibleSheaf.of_iso eout

private theorem isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [Field Λ] [Finite Λ]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj))   := by
  have hK' : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj K) := hK
  have hplus : Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
    apply compactSupport_constructible_of_affine_base Λ f c K q
    intro W hW
    have : IsAffine W.toScheme := hW
    have : CompactSpace ↥(Limits.pullback f W.ι) :=
      QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd f W.ι)
    have : QuasiSeparatedSpace ↥(Limits.pullback f W.ι) :=
      quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd f W.ι)
    exact compactSupportPlus_affineBase Λ
      (Limits.pullback.snd f W.ι) (c.baseChange W.ι)
      (((upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus).obj K)
      (constructible_pullback_complex Λ (Limits.pullback.fst f W.ι) K hK') q
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hplus
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K))
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c).app K))

end AlgebraicGeometry.Etale.C4Compact


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Generic local constancy of proper étale cohomology

Source: Stacks Project, `more-etale.tex`, Tag 0GL0 (theorem-constructible-shriek),
generic-stratum consequence for a proper morphism over an integral affine Noetherian base,
with Tags 0GKY and 0GKZ for its proof, and `etale-cohomology.tex`, Tag 03RW, for finite
locally constant constructible sheaves
(blueprint: lem-fd-proper-cohomology-generic-local-constancy).

For a proper morphism `f : X ⟶ S` to an integral affine Noetherian scheme, a constructible
sheaf `F` of modules over a finite field `A` of characteristic `ℓ` and `q ≥ 0`, some nonempty
open of `S` carries `R^q f_* F` as a finite locally constant sheaf. No invertibility of `ℓ`
is assumed.
-/

/-- **Generic local constancy of one proper higher direct image.** Source: Stacks Project,
`more-etale.tex`, Tag 0GL0 (identity open compactification), with `etale-cohomology.tex`,
Tag 03RW (blueprint: lem-fd-proper-cohomology-generic-local-constancy).

Let `A` be a finite field of characteristic the prime `ℓ`, `S` an integral affine Noetherian
scheme, `f : X ⟶ S` proper, `F` a constructible sheaf of `A`-modules on `X_ét` and `q ≥ 0`.
Then there is a nonempty open immersion `j : U ⟶ S` such that `j^{-1} R^q f_* F`, with
`R^q f_* F = H^q(Rf_*(F[0]))`, is finite locally constant. No invertibility of `ℓ` is assumed.

Proof (blueprint steps):
1. For a compactification `(j, p)`, exact extension by zero and the right derived direct image
   make `Rp_* j_!` additive and triangulated; it preserves lower cohomological bounds, and
   complexes with constructible cohomology form a triangulated subcategory (Serre class).
2. Over an affine base `Y` of finite type over `ℤ` and an affine open `W` of `𝔸¹_Y` with a
   finite locally constant `L`, the finite-étale filtration theorem gives a finite étale
   `g : T → W` of degree prime to `ℓ`; the trace identity makes `L` a retract of `g_* g^* L`,
   and finite direct image is exact.
3. The pieces `T_a → Y` are smooth affine curves; the constant smooth-affine-curve result
   (Tag 0GKX, no invertibility), finite-filtration dévissage, disjoint-open extension and
   compact-support composition give constructibility over `W`.
4. An arbitrary open of `𝔸¹_Y` is handled by a finite affine cover, relative Mayer–Vietoris
   and Serre closure, inducting on the cover size.
5. For constructible `F` on `𝔸¹_Y`, a dense lisse open with finite closed complement, the
   open–closed triangle and quasi-finite shriek constructibility give the result.
6. Noetherian induction on closed subsets of `Y` (reduced induced structures, exact inverse
   image, compact-support base change) gives constructibility over all of `Y`.
7. An arbitrary affine `Y = Spec R` is the limit over finitely generated `ℤ`-subalgebras;
   constructible-module limit descent gives the same conclusion.
8. Truncation and bounded dévissage upgrade the result to bounded-below complexes with
   constructible cohomology, and induction on dimension gives it for affine space.
9. An affine open `W ⊆ X` is a finite-presentation closed subscheme of `𝔸ⁿ_S`; closed
   immersion, quasi-finite shriek and composition give constructibility on `W`.
10. A finite affine cover of the quasi-compact `X`, with affine intersections, Mayer–Vietoris
    and induction on the cover size, give constructibility of `R^q f_* F`.
11. The identity compactification identifies `Rf_!` with `Rf_*`; generic constancy of the
    constructible `R^q f_* F` gives a dense open on which it is finite locally constant, and
    a dense open of the integral (hence nonempty, irreducible) `S` is nonempty. -/
theorem proper_cohomology_generic_local_constancy
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    (S : Scheme.{u}) [IsAffine S] [IsIntegral S] [IsLocallyNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) (hq : 0 ≤ q) :
    ∃ (U : Scheme.{u}) (j : U ⟶ S),
      Nonempty U ∧ IsOpenImmersion j ∧
        Scheme.IsFiniteLocallyConstantSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.homologyFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
              ((Etale.rightDerivedLowerStarPlus
                  (ModuleCat.{u + 1} A) f).obj
                ((DerivedCategory.Plus.singleFunctor
                    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F)))) := by
  classical
  have _hq := hq
  have : IsNoetherian S :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hK : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    intro n
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    by_cases hn : n = 0
    · subst n
      have : Scheme.IsConstructibleSheaf ((𝟭 _).obj F) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
      exact Scheme.IsConstructibleSheaf.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm
    · apply Scheme.IsConstructibleSheaf.of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have hc := Etale.C4Compact.isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
    A f (Compactification.ofIsProper f) K hK q
  let B := ModuleCat.{u + 1} A
  have e₀ : Etale.openImmersionLowerShriek B (𝟙 X) ≅ 𝟭 _ :=
    (Etale.upperStarIsoOpenImmersionLowerShriekInv B (Iso.refl X)).symm ≪≫
      Etale.upperStarId B X
  have e : (Etale.rightDerivedLowerShriekOfCompactification B
      (Compactification.ofIsProper f)).obj K.obj ≅
      (Etale.lowerStar B f).rightDerivedFunctor.obj K.obj :=
    (Etale.lowerStar B f).rightDerivedFunctor.mapIso
      ((Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryIdIso _).app K.obj)
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus B f).obj K)) := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hc
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Etale.lowerStar B f).rightDerivedFunctor.obj K.obj)) :=
      Scheme.IsConstructibleSheaf.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar B f).rightDerivedFunctor.obj K.obj))
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.lowerStar B f).rightDerivedFunctorPlusCompatibility.app K).symm)
  obtain ⟨U, hUdense, hUlisse⟩ := Scheme.IsConstructibleSheaf.exists_dense_open
    ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((Etale.rightDerivedLowerStarPlus B f).obj K))
  exact ⟨U.toScheme, U.ι, hUdense.nonempty.to_subtype, inferInstance, hUlisse⟩

end AlgebraicGeometry
