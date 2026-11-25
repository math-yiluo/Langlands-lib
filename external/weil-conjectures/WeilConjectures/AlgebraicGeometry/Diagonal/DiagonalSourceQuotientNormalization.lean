/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Supported.SupportedPadicScalarExtension
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralScalar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The normalized ordinary quotient of the supported integral constant
Source: diagonal tower system proof, source paragraph of step (3).
(blueprint: lem-sfb-diagonal-source-quotient-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

private abbrev padicRing (ℓ : ℕ) [Fact ℓ.Prime] := ULift.{u + 1} ℤ_[ℓ]

private def residueLinear (ℓ n : ℕ) [Fact ℓ.Prime] :
    ModuleCat.of (padicRing.{u} ℓ) (padicRing.{u} ℓ) ⟶
      (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n)).obj
        (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n)) :=
  ModuleCat.ofHom (Y :=
    (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n)).obj
      (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n)))
    { toFun := diagonalResidueProjection.{u} ℓ n
      map_add' := (diagonalResidueProjection.{u} ℓ n).map_add
      map_smul' := (diagonalResidueProjection.{u} ℓ n).map_mul }

private theorem residueLinear_cokernel (ℓ n : ℕ) [Fact ℓ.Prime] :
    ∃ w : (ℓ ^ (n + 1) • 𝟙 (ModuleCat.of (padicRing.{u} ℓ) (padicRing.{u} ℓ))) ≫
        residueLinear.{u} ℓ n = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (residueLinear.{u} ℓ n) w)) := by
  let A := padicRing.{u} ℓ
  let f : ModuleCat.of A A ⟶ ModuleCat.of A A := ℓ ^ (n + 1) • 𝟙 _
  let q := residueLinear.{u} ℓ n
  have hmul (x : A) : (f x).down = (ℓ : ℤ_[ℓ]) ^ (n + 1) * x.down := by
    change (ℓ ^ (n + 1)) • x.down = _
    simp [nsmul_eq_mul]
  have hker (x : A) : q x = 0 ↔
      x.down ∈ Ideal.span ({(ℓ : ℤ_[ℓ]) ^ (n + 1)} : Set ℤ_[ℓ]) := by
    change ULift.up (PadicInt.toZModPow (n + 1) x.down) =
      (0 : ULift (ZMod (ℓ ^ (n + 1)))) ↔ _
    rw [ULift.ext_iff]
    change PadicInt.toZModPow (n + 1) x.down = 0 ↔ _
    rw [← PadicInt.ker_toZModPow]
    rfl
  have w : f ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change q (f x) = 0
    apply (hker (f x)).2
    rw [hmul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hex : (ShortComplex.mk f q w).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ((hker x).mp hx)
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    rw [hmul]
    exact hy.symm
  have : Epi q := by
    rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up y, ULift.ext hy⟩
  exact ⟨w, ⟨hex.gIsCokernel⟩⟩

private def constantRestrictionIso (ℓ n : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (padicRing.{u} ℓ))).obj
        ((ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n)).obj
          (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n))) ≅
      (Sheaf.restrictScalars (Scheme.ProEt.topology X)
        (diagonalResidueProjection.{u} ℓ n)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) X) := by
  let J := Scheme.ProEt.topology X
  let U := ModuleCat.restrictScalars.{u + 1} (diagonalResidueProjection.{u} ℓ n)
  let P := (Functor.const X.ProEtᵒᵖ).obj
    (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n))
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (diagonalResidueProjection.{u} ℓ n)).isLeftAdjoint
  let e := sheafifyComposeIso J U P
  exact { hom := ⟨e.hom⟩
          inv := ⟨e.inv⟩
          hom_inv_id := by ext : 1; exact e.hom_inv_id
          inv_hom_id := by ext : 1; exact e.inv_hom_id }

private def constantReduction (ℓ n : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    geoCartierConstant (padicRing.{u} ℓ) X ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology X)
        (diagonalResidueProjection.{u} ℓ n)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) X) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (padicRing.{u} ℓ))).map
    (residueLinear ℓ n) ≫ (constantRestrictionIso ℓ n X).hom

private theorem constantReduction_generator (ℓ n : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (W : X.ProEtᵒᵖ) (a : padicRing.{u} ℓ) :
    (constantReduction ℓ n X).hom.app W
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of (padicRing.{u} ℓ)
            (padicRing.{u} ℓ)))).app W a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n)))).app W
            (diagonalResidueProjection.{u} ℓ n a) := by
  let J := Scheme.ProEt.topology X
  let U := ModuleCat.restrictScalars.{u + 1} (diagonalResidueProjection.{u} ℓ n)
  let P := (Functor.const X.ProEtᵒᵖ).obj
    (ModuleCat.of (diagonalResidue.{u} ℓ n) (diagonalResidue.{u} ℓ n))
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (diagonalResidueProjection.{u} ℓ n)).isLeftAdjoint
  have hnat := congr_app (toSheafify_naturality J
    ((Functor.const X.ProEtᵒᵖ).map (residueLinear.{u} ℓ n))) W
  have hfac := congr_app (sheafComposeIso_hom_fac J U P) W
  have h := congrArg (fun f ↦ f a) (hnat.symm)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  change (constantRestrictionIso ℓ n X).hom.hom.app W
    (((constantSheaf J (ModuleCat.{u + 1} (padicRing.{u} ℓ))).map
      (residueLinear ℓ n)).hom.app W
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (ModuleCat.of (padicRing.{u} ℓ) (padicRing.{u} ℓ)))).app W a)) = _
  erw [h]
  exact ConcreteCategory.congr_hom hfac (diagonalResidueProjection.{u} ℓ n a)

private theorem supportedReduction_cokernel (ℓ n : ℕ) [Fact ℓ.Prime]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsFinite i] [LocallyOfFinitePresentation i] :
    ∃ w : (ℓ ^ (n + 1) • 𝟙
        ((lowerStar (ModuleCat.{u + 1} (padicRing.{u} ℓ)) i).obj
          (geoCartierConstant (padicRing.{u} ℓ) X))) ≫
        (lowerStar (ModuleCat.{u + 1} (padicRing.{u} ℓ)) i).map
          (constantReduction ℓ n X) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((lowerStar (ModuleCat.{u + 1} (padicRing.{u} ℓ)) i).map
          (constantReduction ℓ n X)) w)) := by
  let A := padicRing.{u} ℓ
  let C := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let F := lowerStar (ModuleCat.{u + 1} A) i
  have : PreservesFiniteColimits F := preservesFiniteColimits_lowerStar_of_isFinite A i
  obtain ⟨w₀, ⟨h₀⟩⟩ := residueLinear_cokernel.{u} ℓ n
  let G := C ⋙ F
  let e := F.mapIso (constantRestrictionIso ℓ n X)
  have hmap : G.map (ℓ ^ (n + 1) • 𝟙 (ModuleCat.of A A)) =
      ℓ ^ (n + 1) • 𝟙 (F.obj (geoCartierConstant A X)) := by
    change G.map (ℓ ^ (n + 1) • 𝟙 (ModuleCat.of A A)) =
      ℓ ^ (n + 1) • 𝟙 (G.obj (ModuleCat.of A A))
    rw [Functor.map_nsmul]
    exact congrArg (fun f ↦ ℓ ^ (n + 1) • f) (G.map_id (ModuleCat.of A A))
  have hq : G.map (residueLinear ℓ n) ≫ e.hom = F.map (constantReduction ℓ n X) := by
    exact (F.map_comp _ _).symm
  have w : (ℓ ^ (n + 1) • 𝟙 (F.obj (geoCartierConstant A X))) ≫
      F.map (constantReduction ℓ n X) = 0 := by
    change (ℓ ^ (n + 1) • 𝟙 (G.obj (ModuleCat.of A A))) ≫
      F.map (constantReduction ℓ n X) = 0
    have hmap' : G.map (ℓ ^ (n + 1) • 𝟙 (ModuleCat.of A A)) =
        ℓ ^ (n + 1) • 𝟙 (G.obj (ModuleCat.of A A)) := hmap
    erw [← hq, ← hmap', ← Category.assoc, ← G.map_comp, w₀, G.map_zero, zero_comp]
  refine ⟨w, ⟨?_⟩⟩
  exact IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₀ G)
    (CokernelCofork.ofπ (F.map (constantReduction ℓ n X)) w)
    (Iso.refl _) (Iso.refl _) e
    (by
      erw [Category.id_comp, Category.comp_id]
      convert! hmap.symm)
    (by erw [Category.id_comp])

/-- The ordinary reduction of the supported integral constant is the supported
residue constant, with its specified quotient generator.

Source: diagonal tower system proof, step (3), source paragraph; Cartier unit
proof, supported integral/residue sequence
(blueprint: lem-sfb-diagonal-source-quotient-normalization).

Proof: the supported integral/residue sequence is short exact: its geometric
stalks are the integer/residue sequence on the diagonal and zero off it.
Extend the supported integral constant to the constant p-adic scalars. The
coefficient projection is onto because every finite residue class has an integer
representative; PadicInt.ker_toZModPow identifies its kernel with the prime-power
ideal. Transport this calculation through ULift and the constant-ring module-sheaf
equivalence. On the etale site, extension of the supported constant has the
corresponding coefficient stalk on the diagonal and zero stalk off it. Exact
comparison pullback preserves the resulting quotient diagram. Thus the residue
constant, restricted along the residue projection, is the cokernel of multiplication
by the indicated prime power. The insertion-of-one scalar adjunction identifies
its quotient generator with the original integral
generator. The specified ordinary reduction is another cokernel of the same
map. The unique cokernel comparison is therefore invertible and has exactly
the displayed generator normalization. This argument is independent of derived
reduction, the units sheaf, a Cartier boundary, and invertibility of the prime
on the base; on the empty base it is the unique isomorphism of zero objects. -/
theorem diagonal_source_quotient_normalization (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u})
    (D : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ) :
    ∃ s : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))),
      DiagonalSourceNormalization ℓ Y D n s := by
  let A := padicRing.{u} ℓ
  let i := diagonalImmersion Y
  let S := diagonalIntegralSource Y
  let F := lowerStar (ModuleCat.{u + 1} A) i
  have : LocallyOfFinitePresentation i := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine Y ↘ Y))
    have : Smooth (ProjectiveLine Y ↘ Y) :=
      SmoothOfRelativeDimension.smooth 1 (ProjectiveLine Y ↘ Y)
    infer_instance
  obtain ⟨e, he⟩ := supported_padic_scalar_extension ℓ i
  obtain ⟨w₀, ⟨h₀⟩⟩ := supportedReduction_cokernel ℓ n i
  let q := F.map (constantReduction ℓ n (ProjectiveLine Y))
  have w : (ℓ ^ (n + 1) • 𝟙 ((diagonalScalarExtension ℓ (diagonalSurface Y)).obj S)) ≫
      (e.hom ≫ q) = 0 := by
    calc
      (ℓ ^ (n + 1) • 𝟙 _) ≫ (e.hom ≫ q) =
          e.hom ≫ ((ℓ ^ (n + 1) • 𝟙 _) ≫ q) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp]
      _ = 0 := by rw [w₀, comp_zero]
  have hc : IsColimit (CokernelCofork.ofπ (e.hom ≫ q) w) := by
    exact IsCokernel.ofIso _ h₀ (CokernelCofork.ofπ (e.hom ≫ q) w)
      e.symm e.symm (Iso.refl _)
      (by simp only [Iso.symm_hom, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
            Category.id_comp, Category.comp_id])
      (by
        change e.inv ≫ (e.hom ≫ q) = q
        exact e.inv_hom_id_assoc q)
  let s := CokernelCofork.mapIsoOfIsColimit (D.quotient n S) hc (Iso.refl _)
  have hs : (D.π n).app S ≫ s.hom = e.hom ≫ q := by
    exact (CokernelCofork.π_mapOfIsColimit (D.quotient n S) _ (𝟙 _)).trans
      (Category.id_comp _)
  refine ⟨s, ?_⟩
  let U := diagonalForget ℓ (diagonalSurface Y)
  let v := (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app S
  have hπ : v ≫ U.map ((D.π n).app S ≫ s.hom) =
      v ≫ U.map (e.hom ≫ q) := congrArg (fun f ↦ v ≫ U.map f) hs
  have hunit : v ≫ U.map e.hom = cartierProIntegralGenerator A i := eq_of_heq he
  have hcomp : v ≫ U.map (e.hom ≫ q) =
      cartierProIntegralGenerator A i ≫ U.map q := by
    calc
      _ = v ≫ (U.map e.hom ≫ U.map q) :=
        congrArg (fun f ↦ v ≫ f) (U.map_comp _ _)
      _ = (v ≫ U.map e.hom) ≫ U.map q := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun f ↦ f ≫ U.map q) hunit
  have hqgen := pro_supported_generator_scalar (diagonalResidueProjection.{u} ℓ n) i
    (constantReduction ℓ n (ProjectiveLine Y))
    (constantReduction_generator ℓ n (ProjectiveLine Y))
  change cartierProIntegralGenerator A i ≫ U.map q = _ at hqgen
  change HEq (v ≫ U.map ((D.π n).app S ≫ s.hom)) _
  exact (heq_of_eq (hπ.trans hcomp)).trans (heq_of_eq hqgen)

end AlgebraicGeometry.ProEtale
