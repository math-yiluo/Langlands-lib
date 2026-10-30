import Langlands.Cohomology.DivisibleSystem.CompatibleHomologyZero
import Langlands.Cohomology.DivisibleSystem.HomSurjective
import Langlands.Cohomology.InverseLimit.Statement

/-!
# Cohomology of the inverse limit of the Hom complexes

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: the maps (4.10.3) are surjective for all `m`, and "Since the
right-hand side of the spectral sequence (4.9) is a finite group for all `m`, the complexes
in (4.10.2) satisfy a Mittag-Leffler condition." In our reading, this condition is what allows
the passage to the inverse limit over `m` of the complexes (4.10.2).

For `ℓ`-divisible systems `T` and `W` of cochain complexes in an `R`-linear abelian category,
`DivisibleSystem.HomSystem` constructs the inverse system `homComplexSystem R T W` of Hom
complexes `m ↦ Hom^•(T m, W m)` and its limit `homComplexLimit R T W`. This module defines the
canonical comparison `homComplexLimitHomologyComparison` from the cohomology of
`homComplexLimit R T W` to the inverse limit of the cohomology modules of the complexes
`Hom^•(T m, W m)`, the morphism `limit.post` induced by the limit projections. When every term
`(T m) ^ p` is projective relative to objects killed by `ℓ ^ m` (`PowTorsionProjective`), the
degreewise maps of the system are surjective (`DivisibleSystem.HomSurjective`), and:

* given `FiniteCohomologyInverseLimitStatement` and finiteness of the cohomology of every
  `Hom^•(T m, W m)`, the comparison is an isomorphism in every degree;
* given `DegreewiseInverseLimitCohomologyStatement`, the comparison is surjective in every
  degree, and an isomorphism in degree `q` when the cohomology in degree `q - 1` of every
  `Hom^•(T m, W m)` is finite.

The second case uses that an inverse system of finite sets satisfies the Mittag-Leffler
condition (`isMittagLeffler_of_finite`). In degree `0` this identifies the morphisms of
inverse systems `T.tower ⟶ W.tower` modulo those admitting a compatible null-homotopy with the
inverse limit of the degree `0` cohomology modules of the complexes `Hom^•(T m, W m)`.

The inverse-limit statements are hypotheses here; they are proposition targets of
`Langlands.Cohomology.InverseLimit.Statement`. The spectral sequences (4.9), (4.10.1) and
(4.10.4), the finiteness of the cohomology of Harris's complexes and the identification of
the complexes (4.10.2) with Hom complexes of `ℓ`-divisible systems are not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u₁ v₁

section MittagLeffler

/-- A functor to finite types from a cofiltered category satisfies the Mittag-Leffler
condition: for each `j`, the range of `F.map (𝟙 j)` is finite. -/
lemma isMittagLeffler_of_finite {J : Type u₁} [Category.{v₁} J] [IsCofilteredOrEmpty J]
    (F : J ⥤ Type w) (hF : ∀ j, Finite (F.obj j)) : F.IsMittagLeffler :=
  F.isMittagLeffler_of_exists_finite_range fun j =>
    ⟨j, 𝟙 j, haveI := hF j; Set.toFinite _⟩

/-- A functor to modules with finite underlying sets from a cofiltered category satisfies the
Mittag-Leffler condition. -/
lemma isMittagLeffler_moduleCat_of_finite {R : Type w} [Ring R] {J : Type u₁}
    [Category.{v₁} J] [IsCofilteredOrEmpty J] (F : J ⥤ ModuleCat.{v} R)
    (hF : ∀ j, Finite (F.obj j)) :
    (F ⋙ CategoryTheory.forget (ModuleCat.{v} R)).IsMittagLeffler :=
  isMittagLeffler_of_finite _ hF

end MittagLeffler

namespace DivisibleSystem

section HomComplexLimit

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The canonical comparison from the degree `q` cohomology of the inverse limit
`homComplexLimit R T W` of the Hom complexes to the inverse limit over `m` of the degree `q`
cohomology modules of the complexes `Hom^•(T m, W m)`. -/
def homComplexLimitHomologyComparison (q : ℤ) :
    (homComplexLimit R T W).homology q ⟶
      limit (homComplexSystem R T W ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q) :=
  limit.post (homComplexSystem R T W)
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)

/-- The component at level `m` of `homComplexLimitHomologyComparison` is the map on
cohomology induced by the limit projection `homComplexLimit R T W ⟶ Hom^•(T m, W m)`. -/
@[reassoc (attr := simp)]
lemma homComplexLimitHomologyComparison_π (q : ℤ) (m : ℕᵒᵖ) :
    homComplexLimitHomologyComparison R T W q ≫ limit.π _ m =
      HomologicalComplex.homologyMap (limit.π (homComplexSystem R T W) m) q :=
  limit.post_π _ _ _

variable {R T W}

/-- Harris 1999, proof of Proposition 4.10: given `FiniteCohomologyInverseLimitStatement`, the
comparison `homComplexLimitHomologyComparison` is an isomorphism in every degree when every
term `(T m) ^ p` is projective relative to objects killed by `ℓ ^ m` and every complex
`Hom^•(T m, W m)` has finite cohomology. -/
theorem isIso_homComplexLimitHomologyComparison_of_finite
    (hS : FiniteCohomologyInverseLimitStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m q, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology q))
    (q : ℤ) : IsIso (homComplexLimitHomologyComparison R T W q) :=
  hS (homComplexSystem R T W) (fun _ _ φ n => homComplexSystem_map_f_surjective R T W hT φ n)
    (fun i q => hfin (unop i) q) q

/-- Given `DegreewiseInverseLimitCohomologyStatement`, the comparison
`homComplexLimitHomologyComparison` is surjective in every degree when every term `(T m) ^ p`
is projective relative to objects killed by `ℓ ^ m`. -/
theorem homComplexLimitHomologyComparison_surjective
    (hS : DegreewiseInverseLimitCohomologyStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)) (q : ℤ) :
    Function.Surjective (homComplexLimitHomologyComparison R T W q) :=
  (hS _ (isMittagLeffler_homComplexSystem_eval R T W hT) q).1

/-- Given `DegreewiseInverseLimitCohomologyStatement`, the comparison
`homComplexLimitHomologyComparison` is an isomorphism in degree `q` when every term
`(T m) ^ p` is projective relative to objects killed by `ℓ ^ m` and the degree `q - 1`
cohomology modules of the complexes `Hom^•(T m, W m)` satisfy the Mittag-Leffler
condition. -/
theorem isIso_homComplexLimitHomologyComparison_of_isMittagLeffler
    (hS : DegreewiseInverseLimitCohomologyStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)) (q : ℤ)
    (hML : (homComplexSystem R T W ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) (q - 1) ⋙
        CategoryTheory.forget (ModuleCat.{v} R)).IsMittagLeffler) :
    IsIso (homComplexLimitHomologyComparison R T W q) :=
  (hS _ (isMittagLeffler_homComplexSystem_eval R T W hT) q).2 hML

/-- Given `DegreewiseInverseLimitCohomologyStatement`, the comparison
`homComplexLimitHomologyComparison` is an isomorphism in degree `q` when every term
`(T m) ^ p` is projective relative to objects killed by `ℓ ^ m` and the degree `q - 1`
cohomology of every complex `Hom^•(T m, W m)` is finite. -/
theorem isIso_homComplexLimitHomologyComparison_of_finite_sub_one
    (hS : DegreewiseInverseLimitCohomologyStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)) (q : ℤ)
    (hfin : ∀ m, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology (q - 1))) :
    IsIso (homComplexLimitHomologyComparison R T W q) :=
  isIso_homComplexLimitHomologyComparison_of_isMittagLeffler hS hT q
    (isMittagLeffler_moduleCat_of_finite (homComplexSystem R T W ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) (q - 1))
        fun i => hfin (unop i))

/-- Given `FiniteCohomologyInverseLimitStatement`, the comparison
`homComplexLimitHomologyComparison` as an isomorphism, when every term `(T m) ^ p` is
projective relative to objects killed by `ℓ ^ m` and every complex `Hom^•(T m, W m)` has
finite cohomology. -/
def homComplexLimitHomologyIso (hS : FiniteCohomologyInverseLimitStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m q, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology q))
    (q : ℤ) :
    (homComplexLimit R T W).homology q ≅
      limit (homComplexSystem R T W ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q) :=
  haveI := isIso_homComplexLimitHomologyComparison_of_finite hS hT hfin q
  asIso (homComplexLimitHomologyComparison R T W q)

@[simp]
lemma homComplexLimitHomologyIso_hom (hS : FiniteCohomologyInverseLimitStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m q, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology q))
    (q : ℤ) :
    (homComplexLimitHomologyIso hS hT hfin q).hom = homComplexLimitHomologyComparison R T W q :=
  rfl

/-- Given `DegreewiseInverseLimitCohomologyStatement`, the morphisms of inverse systems
`T.tower ⟶ W.tower` modulo those admitting a compatible null-homotopy are the inverse limit of
the degree `0` cohomology modules of the complexes `Hom^•(T m, W m)`, when every term
`(T m) ^ p` is projective relative to objects killed by `ℓ ^ m` and the degree `-1`
cohomology of every complex `Hom^•(T m, W m)` is finite. The equivalence is
`towerHomQuotientEquivLimitHomologyZero` followed by `homComplexLimitHomologyComparison`. -/
def towerHomQuotientEquivLimitOfHomologyZero
    (hS : DegreewiseInverseLimitCohomologyStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology (-1))) :
    ((T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) ≃ₗ[R]
      (limit (homComplexSystem R T W ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0) :
          ModuleCat.{v} R) :=
  haveI := isIso_homComplexLimitHomologyComparison_of_finite_sub_one hS hT 0 hfin
  (towerHomQuotientEquivLimitHomologyZero R T W).trans
    (asIso (homComplexLimitHomologyComparison R T W 0)).toLinearEquiv

lemma towerHomQuotientEquivLimitOfHomologyZero_apply
    (hS : DegreewiseInverseLimitCohomologyStatement.{w, v} R)
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology (-1)))
    (x : (T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) :
    towerHomQuotientEquivLimitOfHomologyZero hS hT hfin x =
      (homComplexLimitHomologyComparison R T W 0).hom
        (towerHomQuotientEquivLimitHomologyZero R T W x) :=
  rfl

end HomComplexLimit

end DivisibleSystem

section Smooth

variable {R : Type u} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- Harris 1999, proof of Proposition 4.10, for `ℓ`-divisible systems of cochain complexes of
smooth representations: given `FiniteCohomologyInverseLimitStatement`, the cohomology of the
inverse limit of the Hom complexes of equivariant maps is the inverse limit of their
cohomology, when every term `(T m) ^ p` is projective, in the category of smooth
representations, relative to objects killed by `ℓ ^ m` and every Hom complex has finite
cohomology. -/
theorem isIso_smoothHomComplexLimitHomologyComparison_of_finite
    (hS : FiniteCohomologyInverseLimitStatement.{u, w} R)
    (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ)
    (hT : ∀ m p, DivisibleSystem.PowTorsionProjective ℓ m ((T.obj m).X p))
    (hfin : ∀ m q, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology q))
    (q : ℤ) : IsIso (DivisibleSystem.homComplexLimitHomologyComparison R T W q) :=
  DivisibleSystem.isIso_homComplexLimitHomologyComparison_of_finite hS hT hfin q

/-- For `ℓ`-divisible systems of cochain complexes of smooth representations: given
`DegreewiseInverseLimitCohomologyStatement`, the comparison for the Hom complexes of
equivariant maps is an isomorphism in degree `q` when every term `(T m) ^ p` is projective,
in the category of smooth representations, relative to objects killed by `ℓ ^ m` and the
degree `q - 1` cohomology of every Hom complex is finite. -/
theorem isIso_smoothHomComplexLimitHomologyComparison_of_finite_sub_one
    (hS : DegreewiseInverseLimitCohomologyStatement.{u, w} R)
    (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ)
    (hT : ∀ m p, DivisibleSystem.PowTorsionProjective ℓ m ((T.obj m).X p)) (q : ℤ)
    (hfin : ∀ m, Finite ((LinearHomComplex.complex R (T.obj m) (W.obj m)).homology (q - 1))) :
    IsIso (DivisibleSystem.homComplexLimitHomologyComparison R T W q) :=
  DivisibleSystem.isIso_homComplexLimitHomologyComparison_of_finite_sub_one hS hT q hfin

end Smooth

end Langlands.Cohomology
