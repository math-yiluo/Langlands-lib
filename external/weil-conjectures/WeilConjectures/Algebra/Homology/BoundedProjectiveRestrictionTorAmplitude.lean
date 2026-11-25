/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.BoundedComplexTermAmplitude
import WeilConjectures.Algebra.Homology.ProjectiveRestrictionTorBound
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Tor amplitude after restricting a bounded projective complex

Source: Stacks Project, Tag 0B6G, lemma-perfect-proper-perfect-direct-image,
condition (3); More on Algebra, Tags 066H, 066K and 0655.
(blueprint: lem-pc-bounded-projective-restriction-tor-amplitude).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Projective resolutions calculate the amplitude of a module in a single degree
from its Tor bound. Source: Stacks Project, Tag 0655. -/
private theorem single_torAmplitude_of_Tor
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : ModuleCat.{u} R) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} R, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} R) j).obj E).obj M)) (n : ℤ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) (n - (d : ℤ)) n
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj E) := by
  let T := projectiveResolution E
  let e := ComplexShape.embeddingUpIntLE n
  let P : CochainComplex (ModuleCat.{u} R) ℤ := T.complex.extend e
  have hbounded : P.IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact T.complex.isZero_extend_X e i (by intro j; change n - (j : ℤ) ≠ i; omega)
  have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
    apply (ModuleCat.flat_iff_flat _).2
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have (X : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight X))
  have hP := CochainComplex.kFlat_of_isStrictlyLE_of_flat P n hflat
  let g := HomologicalComplex.extendMap T.π e ≫
    (HomologicalComplex.extendSingleIso e E 0 n (by simp [e])).hom
  have hg : QuasiIso g := by dsimp [g]; infer_instance
  have : IsIso (DerivedCategory.Q.map g) := by infer_instance
  let eP : DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj E :=
    asIso (DerivedCategory.Q.map g) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) n).app E).symm
  apply (DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) (n - (d : ℤ)) n).prop_of_iso eP
  intro M
  let F := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let L := (F.mapHomologicalComplex (.up ℤ)).obj P
  have eL : MonoidalCategory.tensorObj (DerivedCategory.Q.obj P)
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M) ≅ DerivedCategory.Q.obj L :=
    DerivedCategory.QObjTensorSingleFunctorObjIso P hP M
  apply (DerivedCategory.homologyConcentratedIn (n - (d : ℤ)) n).prop_of_iso eL.symm
  constructor
  · apply (DerivedCategory.isGE_iff _ _).2
    intro i hi
    have hin : i ≤ n := by omega
    obtain ⟨j, hj⟩ := Int.le.dest hin
    have hj' : e.f j = i := by change n - (j : ℤ) = i; omega
    have hdj : d < j := by omega
    have eh : L.homology i ≅ (((Tor' (ModuleCat R) j).obj E).obj M) :=
      (HomologicalComplex.homologyFunctor _ _ i).mapIso
        ((e.mapExtendFunctorNatIso F).app T.complex) ≪≫
      ((F.mapHomologicalComplex (.down ℕ)).obj T.complex).extendHomologyIso e hj' ≪≫
      (T.isoLeftDerivedObj F j).symm
    exact (hTor M j hdj).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app L ≪≫ eh)
  · apply (DerivedCategory.isLE_iff _ _).2
    intro i hi
    have hz : IsZero (L.X i) := F.map_isZero
      (CochainComplex.isZero_of_isStrictlyLE P n i hi)
    exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology.of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app L)


/-- A bounded complex of projective B-modules acquires amplitude [r-d,s] over A
when the regular B-module has Tor dimension at most d over A.

Source: Stacks Project, Tag 0B6G, lemma-perfect-proper-perfect-direct-image,
condition (3); More on Algebra, Tags 066H, 066K and 0655.
(blueprint: lem-pc-bounded-projective-restriction-tor-amplitude).

Proof: each projective B-term, restricted to A, inherits B's Tor bound by
projective_restriction_tor_bound. Reindex its projective A-resolution in degrees
n-j. Its bounded-above flat terms make it K-flat. Tensoring this resolution with
an A-module computes the derived tensor and its homology in degree n-j is Tor_j.
Thus the term in degree n has amplitude [n-d,n], which lies in [r-d,s] whenever
r ≤ n ≤ s. The finite stupid-truncation induction in
bounded_torAmplitude_of_single_terms combines these termwise bounds. Tensoring
the truncation triangles with a module preserves distinguished triangles, and
both homology bounds are extension closed. The empty interval case is handled
inside this induction: all terms, and hence the entire complex, are zero.
No finite generation or ordering of r and s is required. -/
theorem boundedProjective_restriction_torAmplitude
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (C : CochainComplex (ModuleCat.{u} B) ℤ)
    (r s : ℤ) (hdegrees : ∀ t : ℤ, t < r ∨ s < t → IsZero (C.X t))
    (hprojective : ∀ t : ℤ, Projective (C.X t)) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of B B))).obj M)) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) (r - (d : ℤ)) s
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj C)) := by
  let K := ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj C
  have hK : ∀ t : ℤ, t < r ∨ s < t → IsZero (K.X t) := fun t ht ↦
    (ModuleCat.restrictScalars ρ).map_isZero (hdegrees t ht)
  apply bounded_torAmplitude_of_single_terms K r s (r - (d : ℤ)) s hK
  intro t hrt hts
  have hterm := ModuleCat.projective_restriction_tor_bound ρ (C.X t) (hprojective t) d hTor
  exact (single_torAmplitude_of_Tor ((ModuleCat.restrictScalars ρ).obj (C.X t))
    d hterm t).mono (by omega) hts

end CochainComplex
