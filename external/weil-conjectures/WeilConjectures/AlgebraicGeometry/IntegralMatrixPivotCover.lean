/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData

import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # A single integral matrix pivot

This isolates the continuous-function pivot construction. Repeated elimination, rational
cokernel comparisons, and constructible kernel closure are proved in the parent module.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- The witnesses transport finite biproduct bases through normalized coefficient pullbacks.
/-- One integral pivot, after refining a free rational cokernel cover.

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1),
for the integral coefficient framework and kernel-closure application. The
continuous-function pivot argument below is an agent reduction, not an argument
written out in Lemma 6.8.7 (which reduces to Corollary 6.8.5).
(auxiliary; not a blueprint node)

Proof:
1. Refine the supplied covering where the scalar-extended cokernel is finite free.
   The coefficient pullback comparisons identify the restricted coefficients with
   the actual integral and field coefficient rings on each covering scheme. Transport
   the two chosen free-module bases along these comparisons. The continuous-function
   realization of the coefficients identifies the matrix entries with continuous
   O_E-valued functions on the underlying scheme, naturally under restriction.
2. On a piece where the rational cokernel has rank q and the target has rank t,
   the matrix has pointwise E-rank t-q. To see this, pull its cokernel presentation
   and the free cokernel isomorphism to an algebraically closed residue field at a
   point. Geometric-field evaluation preserves cokernels and finite free modules;
   the coefficient comparison evaluates each continuous entry at that point.
   Consequently, if the matrix is zero at a point of this piece, t-q is zero,
   every entry vanishes at every point of the piece, and the whole matrix is zero.
   This gives the first alternative and also covers empty matrices and zero ranks.
3. Otherwise fix a point and a matrix entry of maximal norm there. Its value is
   nonzero. For every matrix entry f, restrict to the open neighborhood on which
   |f(y)-f(x)| is strictly smaller than the chosen pivot norm at x. There are
   finitely many entries, so this is an open neighborhood. The ultrametric inequality
   shows that the pivot norm stays equal to its value at x, and every entry has
   norm at most the pivot norm throughout the neighborhood.
4. Permute the chosen column and row to the first positions. Split each finite free
   module into its first regular summand and the remaining finite free summands.
   The source has n>0; its complementary rank m=n-1 satisfies m<n. The first row
   entries divided by the pivot are continuous O_E-valued functions: their E-valued
   quotients are continuous because the pivot is nowhere zero, and the preceding
   norm bound puts them in O_E. Assemble these quotients into r. Call the first
   column below the pivot c and the remaining block d. Equality of continuous
   functions gives exactly the displayed block matrix with top row (p,r p).
5. Multiplication by the pivot is monic on the regular integral sheaf: on every
   site object its restriction is multiplication by a nowhere-zero function, so
   pointwise cancellation in O_E proves injectivity on sections. After extending
   scalars to E it is invertible, with inverse multiplication by the continuous
   reciprocal of the pivot. These constructions agree with the coefficient
   comparison and scalar-extension regular-module isomorphisms. The open
   neighborhoods of the points cover each nonzero piece; compose them with the
   original pro-etale covering. The resulting covering and the bases above give
   all witnesses in the statement. No finite-dimensionality or noetherianity is
   used once the rational cokernel covering has been supplied. -/
theorem integralMatrix_pivot_cover (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
  ∀ (n : ℕ) (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
    Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
    (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) →
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      T.map a = 0 ∨
        ∃ (m : ℕ), m < n ∧
          ∃ (A₁ B₁ : Mod (Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) R)
            (_ : A₁ ≅ Mod.finiteFree R m),
            Mod.IsFree R B₁ ∧
              ∃ (p : Mod.regular R ⟶ Mod.regular R), Mono p ∧
                IsIso ((Mod.extendScalars
                  (coefficientMap (integralScalarMap ℓ E) (V.X k))).map p) ∧
                ∃ (r : A₁ ⟶ Mod.regular R) (c : Mod.regular R ⟶ B₁) (d : A₁ ⟶ B₁)
                  (eA : T.obj A ≅ Mod.regular R ⊞ A₁)
                  (eB : T.obj B ≅ Mod.regular R ⊞ B₁),
                  eA.inv ≫ T.map a ≫ eB.hom =
                    biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d) := by
  intro n X A B a hA hB hC
  classical
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  by_cases ha : a = 0
  · let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
      Precoverage.ZeroHypercover.singleton (𝟙 X)
        (Scheme.proetalePrecoverage.mem_coverings_of_isIso _)
    refine ⟨U, fun k ↦ ?_⟩
    left
    simp only [ha, Functor.map_zero]
  obtain ⟨eA₀⟩ := hA
  obtain ⟨t₀, ⟨eB₀⟩⟩ := hB
  let R₀ := condensedRingObj (integralCoeff ℓ E) X
  let f₀ : Mod.finiteFree R₀ n ⟶ Mod.finiteFree R₀ t₀ := eA₀.inv ≫ a ≫ eB₀.hom
  let ec : cokernel a ≅ cokernel f₀ := cokernel.mapIso a f₀ eA₀ eB₀ (by simp [f₀])
  have hC₀ : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel f₀))) := by
    obtain ⟨U, hU⟩ := hC
    refine ⟨U, fun k ↦ ?_⟩
    obtain ⟨q, ⟨eq⟩⟩ := hU k
    let G := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)
    let F := (ProEtale.upperStar Ab.{u + 1} (U.f k)).mapMod
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
    exact ⟨q, ⟨(F.mapIso (G.mapIso ec)).symm ≪≫ eq⟩⟩
  obtain ⟨V, hV⟩ := integralMatrix_analytic_cover ℓ E n t₀ X f₀ hC₀
  refine ⟨V, fun k ↦ ?_⟩
  let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
  let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
      (condensedRingObj (integralCoeff ℓ E) X) ⋙
    Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
  change T.map a = 0 ∨ _
  rcases hV k with hz | ⟨i, j, hzero, hbound⟩
  · left
    have ha₀ : a = eA₀.hom ≫ f₀ ≫ eB₀.inv := by simp [f₀]
    rw [ha₀, Functor.map_comp, Functor.map_comp, hz, Limits.zero_comp, Limits.comp_zero]
  · right
    let t := t₀
    let eA₁ := integralFiniteFreePullbackIso ℓ E (V.f k) n
    let eB₁ := integralFiniteFreePullbackIso ℓ E (V.f k) t₀
    let eA := T.mapIso eA₀ ≪≫ eA₁
    let eB := T.mapIso eB₀ ≪≫ eB₁
    let e := chartComparison (V.X k) (continuousIntegers ℓ E)
    let eE := chartComparison (V.X k) E
    have : IsIso eE := chartComparison_isIso (V.X k) E
    have hcompat : coefficientMap (integralScalarMap ℓ E) (V.X k) ≫ eE =
        e ≫ integralFunctionInclusion ℓ E (V.X k) :=
      chartComparison_naturality (V.X k) (continuousIntegers ℓ E) E
        (continuousIntegers ℓ E).subtype continuous_subtype_val
    let f : Mod.finiteFree R n ⟶ Mod.finiteFree R t :=
      eA.inv ≫ T.map a ≫ eB.hom
    have hf : f = eA₁.inv ≫ T.map f₀ ≫ eB₁.hom := by
      simp only [f, eA, eB, f₀, Iso.trans_inv, Iso.trans_hom,
        Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    obtain ⟨hp, hunit, q, hq⟩ :=
      integralMatrix_entry_properties ℓ E (V.X k) e eE hcompat f i j
        (by simpa only [hf] using hzero) (by simpa only [hf] using hbound)
    obtain ⟨m, s, hmn, eA', eB', r, c, d, hblock⟩ :=
      finiteBiproduct_pivot f i j q hq
    refine ⟨m, hmn, Mod.finiteFree R m, Mod.finiteFree R s, Iso.refl _,
      ⟨s, ⟨Iso.refl _⟩⟩,
      biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
        biproduct.π (fun _ : Fin t ↦ Mod.regular R) i,
      hp, hunit, r, c, d, eA ≪≫ eA', eB ≪≫ eB', ?_⟩
    simpa only [f, Iso.trans_inv, Iso.trans_hom, Category.assoc] using hblock

end AlgebraicGeometry.ProEtale.CondensedRing
