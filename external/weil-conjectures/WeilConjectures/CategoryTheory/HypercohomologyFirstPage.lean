/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.CartanEilenbergSecondFiltration
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-! # The first hypercohomology spectral sequence

Source: Stacks Project, Tags 0130 and 015H; blueprint order 522
(blueprint: thm-sp-if-e1).

The bicomplex uses the Stacks order (complex degree, resolution degree); flipping after
extension by zero gives the order (resolution degree, complex degree) of the blueprint.
The spectral sequence uses Mathlib's order (filtration degree, complementary degree).
Thus the blueprint term E₁^{r,s} is `(E.page 1).X (s,r)` here. Signed identifications
with the derived functors absorb the second-filtration sign in Tag 0130.
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option linter.unusedVariables false in
/-- The second-degree filtration of a Cartan--Eilenberg total complex gives the first
hypercohomology spectral sequence, with its induced differential and derived abutment.
Source: Stacks Project, Tags 0130 and 015H; blueprint order 522
(blueprint: thm-sp-if-e1).

Proof:
1. Each column in the Stacks indexing is an injective resolution of K^s
   (def-sp-injective-resolutions). Its F-image computes R^r F(K^s)
   (def-sp-left-exact-additive). Extend the resolution index by zero and flip.
   The second filtration is preserved by the total differential
   (def-sp-double-complex-total). In total degree n its steps are the whole object
   below the lower bound and zero above n, so it is finite degreewise.
2. Apply thm-sp-spectral-object-yields to this filtration. The page-zero and
   cycle/boundary identifications below specify the associated spectral sequence.
   Its first page is the row cohomology. Under the unmodified row identifications
   the differential is (-1)^r R^r F(d_K), by Tag 0130; multiplying the identification
   in bidegree (s,r) by (-1)^(rs) gives the displayed unsigned differential.
   The bounded filtration gives convergence to total cohomology (def-sp-convergence).
3. The total complex before applying F is bounded below and degreewise a finite sum
   of injectives, hence K-injective (lem-sp-kinjective-computes). The augmented rows
   are exact; filtering their total by complex degree gives zero first page, so the
   augmentation K -> Tot(I) is a quasi-isomorphism (thm-sp-spectral-object-yields).
4. It is therefore a K-injective resolution (def-sp-kinjective-bridge). Additivity
   of F commutes with the finite diagonal sums, identifying its image with the
   total used below. The canonical cohomology comparison to any chosen K-injective
   resolution identifies the abutment with H^n(RFK): `aug` is the augmentation into the
   summands of resolution degree zero, `u` a comparison map over K to the chosen
   resolution, `w` its F-image on the diagonal sums, and `c` the map `w` induces.
   Comparison maps are unique up to homotopy (lem-sp-kinjective-computes), so their
   induced cohomology maps are independent of the map and the Cartan--Eilenberg
   resolution.
-/
theorem exists_hypercohomology_firstPage
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hterms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s))
    (hinjective : ∀ (s : ℤ) (r : ℕ),
      Injective ((I.cycles s).X r) ∧
      Injective ((image (I.d (s - 1) s)).X r) ∧ Injective ((I.homology s).X r))
    (hquasi : ∀ s : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap a s) ∧
      QuasiIso (image.map (Arrow.homMk' (a.f (s - 1)) (a.f s) (a.comm (s - 1) s))) ∧
      QuasiIso (HomologicalComplex.homologyMap a s)) :
    ∃ (L : DecreasingFiltration
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
          (ComplexShape.up ℤ)))
      (E : CohomologicalSpectralSequence B 0)
      (e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q))
      (e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
        (F.rightDerived r).obj (K.obj.X s)),
      (∀ p n : ℤ, L.complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
          p) ∧
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
        (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      (∀ (p q t : ℤ) (ht : 1 ≤ t),
        ∃ hBZ : L.complexBoundaries p (p + q) t ≤ L.complexCycles p (p + q) t,
          Nonempty ((E.page t (le_trans (by decide : (0 : ℤ) ≤ 1) ht)).X (p, q) ≅
            cokernel (Subobject.ofLE _ _ hBZ))) ∧
      (∀ (r : ℕ) (s : ℤ),
        (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e₁ r (s + 1)).hom =
          (e₁ r s).hom ≫ (F.rightDerived r).map (K.obj.d s (s + 1))) ∧
      (∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      (∀ ρ : CochainComplex.KInjectiveResolutionChoice K.obj,
        ∃ (aug : K.obj ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
              (ComplexShape.up ℤ))
          (u : (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
              (ComplexShape.up ℤ) ⟶ ρ.complex)
          (w : (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
              (ComplexShape.up ℤ) ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ρ.complex)
          (c : ∀ n : ℤ,
            ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
              (ComplexShape.up ℤ)).homology n ≅ F.rightDerivedCohomologyWithResolution K ρ n)
          (H : ∀ n : ℤ, DecreasingFiltration (F.rightDerivedCohomologyWithResolution K ρ n)),
          (∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
              ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
            (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
              (ComplexShape.up ℤ) 0 n n (zero_add n)) ∧
          Nonempty (Homotopy (aug ≫ u) ρ.map) ∧
          (∀ (m : ℕ) (s n : ℤ) (h : (m : ℤ) + s = n),
            (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
                (ComplexShape.up ℤ) (m : ℤ) s n h ≫ w.f n =
              (HomologicalComplex.extendXIso
                ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
                ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
              F.map ((HomologicalComplex.extendXIso
                  (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
                  ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
                  (ComplexShape.up ℤ) (m : ℤ) s n h ≫ u.f n)) ∧
          (∀ n : ℤ, (c n).hom = HomologicalComplex.homologyMap w n) ∧
          (∀ n : ℤ, (H n).IsFinite) ∧
          (∀ p n : ℤ, (H n).step p =
            (Subobject.«exists» (c n).hom).obj
              (imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n))) ∧
          (∀ p n : ℤ, ∃ (t : ℤ) (ht : 1 ≤ t), ∀ (r : ℤ) (hr : t ≤ r),
            Nonempty ((E.page r (le_trans (by decide : (0 : ℤ) ≤ 1)
              (le_trans ht hr))).X (p, n - p) ≅ (H n).gradedPiece p))) := by
  classical
  obtain ⟨L, E, e₀, e₁, hL, hd₀, hBZ, hd₁, hneg, habut⟩ :=
    cartanEilenberg_second_filtration F K I a hbelow hterms hrows
  obtain ⟨aug, haug, hq, hki⟩ :=
    cartanEilenberg_total_resolution K I a hbelow hterms hrows
  obtain ⟨e, he⟩ := cartanEilenberg_mapped_total_iso F I hbelow
  refine ⟨L, E, e₀, e₁, hL, hd₀, hBZ, hd₁, hneg, ?_⟩
  intro ρ
  let τ : CochainComplex.KInjectiveResolutionChoice K.obj :=
    ⟨_, aug, hq, hki⟩
  let τR : CochainComplex.KInjectiveResolution K.obj :=
    { I := τ.complex, ι := τ.map, quasiIso_ι := τ.quasiIso, isKInjective := τ.isKInjective }
  let ρR : CochainComplex.KInjectiveResolution K.obj :=
    { I := ρ.complex, ι := ρ.map, quasiIso_ι := ρ.quasiIso, isKInjective := ρ.isKInjective }
  let u : τ.complex ⟶ ρ.complex := (τR.homotopyEquiv ρR).hom
  let v : ρ.complex ⟶ τ.complex := (τR.homotopyEquiv ρR).inv
  have hu : Nonempty (Homotopy (τ.map ≫ u) ρ.map) := ⟨τR.homotopyEquivHomotopy ρR⟩
  have huv : Nonempty (Homotopy (u ≫ v) (𝟙 _)) :=
    ⟨(τR.homotopyEquiv ρR).homotopyHomInvId⟩
  have hvu : Nonempty (Homotopy (v ≫ u) (𝟙 _)) :=
    ⟨(τR.homotopyEquiv ρR).homotopyInvHomId⟩
  let equiv : HomotopyEquiv τ.complex ρ.complex :=
    ⟨u, v, huv.some, hvu.some⟩
  let w := e.hom ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u
  let c : ∀ n : ℤ,
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)).homology n ≅ F.rightDerivedCohomologyWithResolution K ρ n :=
    fun n ↦ (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n).mapIso e ≪≫
      (F.mapHomotopyEquiv equiv).toHomologyIso n
  obtain ⟨H, hfin, hstep, hstab⟩ :=
    habut (fun n ↦ F.rightDerivedCohomologyWithResolution K ρ n) c
  refine ⟨aug, u, w, c, H, haug, hu, ?_, ?_, hfin, hstep, hstab⟩
  · intro m s n h
    dsimp only [w, HomologicalComplex.comp_f]
    rw [← Category.assoc, he m s n h, Category.assoc,
      mapHomologicalComplex_map_f, ← F.map_comp, Category.assoc]
  · intro n
    exact (HomologicalComplex.homologyMap_comp e.hom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map u) n).symm

end CategoryTheory.Functor
