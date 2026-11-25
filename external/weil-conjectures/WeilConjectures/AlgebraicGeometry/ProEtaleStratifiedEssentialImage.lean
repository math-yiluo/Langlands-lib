/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequence

/-! # Descent of classicality through a finite stratification -/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem comparison_essImage_of_openCover
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (h : ∀ i, (ν^*(U i)[ModuleCat.{u + 1} Λ]).essImage
      ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F := by
  let R := (DerivedCategory.singleFunctor _ 0).obj F
  have hR : DerivedCategory.TStructure.t.plus
      ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj R) := by
    have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (ν_*(X)[ModuleCat.{u + 1} Λ]) F
    exact ⟨0, inferInstance⟩
  have hloc : ∀ i, ∃ N, Nonempty
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R ≅
        D(ν^*(U i)[ModuleCat.{u + 1} Λ]).obj N) := by
    intro i
    obtain ⟨G, ⟨e⟩⟩ := h i
    refine ⟨(DerivedCategory.singleFunctor _ 0).obj G, ⟨?_⟩⟩
    exact ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
      (((ν^*(U i)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G).symm
  have := isIso_derivedComparisonAdjunction_counit_app_of_openCover
    (ModuleCat.{u + 1} Λ) U hU R hR hloc
  let M := (R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj R
  refine ⟨(DerivedCategory.homologyFunctor _ 0).obj M, ⟨?_⟩⟩
  exact (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso 0).app M) ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app R)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F

private theorem comparison_essImage_openClosed
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hi : (ν^*(Z)[ModuleCat.{u + 1} Λ]).essImage ((i)^*[ModuleCat.{u + 1} Λ].obj F))
    (hj : (ν^*(U)[ModuleCat.{u + 1} Λ]).essImage ((j)^*[ModuleCat.{u + 1} Λ].obj F)) :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F := by
  obtain ⟨hm, he, hx⟩ := exact_openClosedSequence Λ i j hU F
  let Q := ShortComplex.mk
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F)
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) (hx.toIsComplex.zero 0)
  have hQ : Q.ShortExact :=
    { exact := (Q.exact_iff_exact_toComposableArrows).mpr hx
      mono_f := hm
      epi_g := he }
  apply etaleOrigin_of_shortExact hQ
  · obtain ⟨G, ⟨e⟩⟩ := hj
    exact ⟨(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj G,
      ⟨(openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).app G ≪≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapIso e⟩⟩
  · obtain ⟨G, ⟨e⟩⟩ := hi
    have := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} Λ)
    exact ⟨(Etale.lowerStar (ModuleCat.{u + 1} Λ) i).obj G,
      ⟨asIso ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} Λ)).app G) ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) i).mapIso e⟩⟩

private def eraseEmptyStratum {X : Scheme.{u}} (S : Scheme.Stratification X)
    {n : ℕ} (hn : S.n = n + 1) (k : Fin (n + 1))
    (hk : S.stratum (Fin.cast hn.symm k) = ∅) : Scheme.Stratification X where
  n := n
  stratum i := S.stratum (Fin.cast hn.symm (k.succAbove i))
  isLocallyClosed_stratum i := S.isLocallyClosed_stratum _
  isConstructible_stratum i := S.isConstructible_stratum _
  pairwise_disjoint_stratum a b hab := S.pairwise_disjoint_stratum
    (by
      intro h
      apply hab
      apply k.succAbove_right_injective
      exact Fin.cast_injective hn.symm h)
  iUnion_stratum_eq_univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hik : Fin.cast hn i ≠ k := by
      intro he
      have hie : i = Fin.cast hn.symm k := by subst he; simp
      rw [hie, hk] at hi
      exact hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hik
    refine ⟨j, ?_⟩
    simpa [hj] using hi
  domain i := S.domain (Fin.cast hn.symm (k.succAbove i))
  immersion i := S.immersion (Fin.cast hn.symm (k.succAbove i))
  isImmersion i := S.isImmersion _
  range_immersion i := S.range_immersion _

private theorem comparison_essImage_strata_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (S : Scheme.Stratification X) (g : Y ⟶ X)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k, (ν^*(S.domain k)[ModuleCat.{u + 1} Λ]).essImage
      (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F)) (k : Fin S.n) :
    (ν^*((S.pullback g).domain k)[ModuleCat.{u + 1} Λ]).essImage
      ((((S.pullback g).immersion k)^*[ModuleCat.{u + 1} Λ]).obj
        (((g)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  let e := ((upperStarComp (ModuleCat.{u + 1} Λ)
      (pullback.fst (S.immersion k) g) (S.immersion k)).app F).symm ≪≫
    eqToIso (congrArg (fun m ↦ ((m)^*[ModuleCat.{u + 1} Λ]).obj F) pullback.condition) ≪≫
    (upperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd (S.immersion k) g) g).app F
  exact ((ν^*(_)[ModuleCat.{u + 1} Λ]).essImage).prop_of_iso e
    (etaleOrigin_upperStar_obj (pullback.fst (S.immersion k) g) (hS k))

/-- A sheaf is classical if its restrictions to a finite constructible stratification
are classical. Source: Stacks Project, Tag 09AK, proof of lemma-compare-constructible,
after local constancy has supplied classicality on each stratum.
(auxiliary; not a blueprint node).

Proof: classicality is Zariski local by placing the sheaf in degree zero, applying
the derived open-cover comparison theorem, and taking zeroth homology. Induct on the
number of strata, simultaneously for all schemes. At a point
choose an affine open where its selected stratum is closed and has quasi-compact open
complement. Pull the strata back as schemes. The complement has fewer nonempty strata;
the selected closed restriction is classical by hypothesis and pullback compatibility.
The open-closed short exact sequence has classical end terms: comparison commutes with
extension by zero on the open and with direct image on the closed immersion. Classicality
is closed under extensions because exact comparison is fully faithful on bounded below
derived categories, so the extension boundary lifts. Thus the middle sheaf is classical
on the affine neighborhood, and Zariski locality finishes. For zero strata the base is
empty and its sheaf category is zero. A full-image stratum need not be an isomorphism:
use the same closed-immersion argument in that case. The open-closed sequence and
all the comparison and extension arguments work over an arbitrary commutative ring;
no finite coefficient or finite stalk condition is used.
-/
theorem comparison_essImage_of_stratification
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (S : Scheme.Stratification X)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k : Fin S.n, (ν^*(S.domain k)[ModuleCat.{u + 1} Λ]).essImage
      (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F := by
  classical
  suffices H : ∀ n, ∀ {X : Scheme.{u}} (S : Scheme.Stratification X), S.n = n →
      ∀ (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)),
      (∀ k, (ν^*(S.domain k)[ModuleCat.{u + 1} Λ]).essImage
        (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F)) →
      (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F from H S.n S rfl F hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X S hn F hS
    have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
        (ν^*(V)[ModuleCat.{u + 1} Λ]).essImage
          ((((V).ι)^*[ModuleCat.{u + 1} Λ]).obj F) := by
      intro x
      have hx : x ∈ ⋃ k, S.stratum k := by rw [S.iUnion_stratum_eq_univ]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      cases n with
      | zero => exact Fin.elim0 (Fin.cast hn k)
      | succ m =>
        obtain ⟨V, hV, hxV, hc, _, hcomp⟩ := exists_affineOpen_closed_stratum X S.n
          S.stratum S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum
          S.isLocallyClosed_stratum S.isConstructible_stratum x k hk
        let T := S.pullback V.ι
        let i := T.immersion k
        have hi : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i
          (by rw [T.range_immersion]; exact hc)
        let U : (V : Scheme.{u}).Opens := ⟨(Set.range i)ᶜ,
          i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
        have hcompact : CompactSpace U := by
          apply isCompact_iff_compactSpace.mp
          change IsCompact ((Set.range i)ᶜ)
          rw [T.range_immersion]
          exact hcomp
        have : IsAffine (V : Scheme.{u}) := hV
        have : QuasiCompact U.ι := inferInstance
        let R := T.pullback U.ι
        have hempty : R.stratum k = ∅ := by
          ext y
          change (U.ι y ∈ T.stratum k) ↔ False
          rw [← T.range_immersion]
          exact ⟨fun hy ↦ y.property hy, False.elim⟩
        let R' := eraseEmptyStratum R hn (Fin.cast hn k) (by simpa using hempty)
        have hR : (ν^*(U)[ModuleCat.{u + 1} Λ]).essImage
            ((((U).ι)^*[ModuleCat.{u + 1} Λ]).obj
              ((((V).ι)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
          apply ih m (Nat.lt_succ_self m) R' rfl
          intro a
          exact comparison_essImage_strata_pullback Λ T U.ι
            ((((V).ι)^*[ModuleCat.{u + 1} Λ]).obj F)
            (comparison_essImage_strata_pullback Λ S V.ι F hS) _
        refine ⟨V, hxV, comparison_essImage_openClosed Λ i U.ι (by rw [U.range_ι]; rfl) _ ?_ hR⟩
        exact comparison_essImage_strata_pullback Λ S V.ι F hS k
    choose V hxV hV using hloc
    exact comparison_essImage_of_openCover Λ V (fun x ↦ ⟨x, hxV x⟩) F hV

end AlgebraicGeometry.ProEtale
