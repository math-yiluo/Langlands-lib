import Langlands.GroupScheme.OuterClassEtaleTrivialization
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # Finite outer-class carriers from an étale trivializing covering family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.FiniteGenericOuterClass

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {G H A : GroupScheme (Spec (CommRingCat.of R))}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}

/-- A covering family of actual constant trivializations suffices; its index
of copies is allowed to depend on the member of the cover. -/
def ofEtaleCover
    (O : OuterIsomorphismScheme I a) [IsSeparated O.parameter.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of R)))
    (h𝒰 : ∀ i : 𝒰.I₀, ∃ J : Type u,
      Nonempty ((Over.pullback (𝒰.f i)).obj O.parameter ≅
        Over.mk (Sigma.desc (fun _ : J => 𝟙 (𝒰.X i)))))
    (p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter) :
    FiniteGenericOuterClass O p := by
  have hc := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp 𝒰.mem₀
  let i := (hc.1 (IsLocalRing.closedPoint R)).choose
  have hi : IsLocalRing.closedPoint R ∈ Set.range (𝒰.f i) :=
    (hc.1 (IsLocalRing.closedPoint R)).choose_spec
  letI : Etale (𝒰.f i) := hc.2 i
  letI : Surjective (𝒰.f i) :=
    Langlands.AlgebraicGeometry.surjective_of_isOpenMap_of_closedPoint_mem
      (𝒰.f i) (𝒰.f i).isOpenMap hi
  let J : Type u := (h𝒰 i).choose
  let e : (Over.pullback (𝒰.f i)).obj O.parameter ≅
      Over.mk (Sigma.desc (fun _ : J => 𝟙 (𝒰.X i))) :=
    Classical.choice (h𝒰 i).choose_spec
  exact ofEtaleTrivialization R K O (𝒰.f i) J e p

/-- A constant trivializing covering family for one quotient supplies a finite
carrier for the exact prescribed class in any other supplied quotient. -/
def ofComparisonEtaleCover
    (O O' : OuterIsomorphismScheme I a) [IsSeparated O'.parameter.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of R)))
    (h𝒰 : ∀ i : 𝒰.I₀, ∃ J : Type u,
      Nonempty ((Over.pullback (𝒰.f i)).obj O'.parameter ≅
        Over.mk (Sigma.desc (fun _ : J => 𝟙 (𝒰.X i)))))
    (p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter) :
    FiniteGenericOuterClass O p :=
  (ofEtaleCover R K O' 𝒰 h𝒰 p).ofComparison

end Langlands.GroupScheme.FiniteGenericOuterClass
