import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupConjugation

/-! # Conjugation of the original compact cohomology towers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

private theorem stableNeighbourhoods_of_equivariantHomeomorph
    {G X Y : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction G Y]
    [HasStableNeighbourhoods G X] (e : X ≃ₜ Y)
    (he : ∀ (a : G) (x : X), e (a • x) = a • e x) :
    HasStableNeighbourhoods G Y where
  exists_stable y O hO hy := by
    obtain ⟨H, V, hV, hxV, hVO, hHV⟩ :=
      HasStableNeighbourhoods.exists_stable (G := G) (e.symm y) (e ⁻¹' O)
        (hO.preimage e.continuous) (by simpa using hy)
    refine ⟨H, e '' V, e.isOpenMap V hV, ⟨e.symm y, hxV, e.apply_symm_apply y⟩,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hVO hx
    · intro a ha z hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨a • x, hHV a ha x hx, he a x⟩

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P} {U : OpenSubgroup G}

namespace OpenSubgroupTransport.FiniteIndexLevel

variable (d : ρ.InvariantRationalDomain U) (g : G)
  [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
    ((inclusion U).obj d).LocalSpectrum]

include targetStable in
/-- The original local stability premise transports to the actual moved domain. -/
theorem hasStableNeighbourhoods_conjugate_local :
    HasStableNeighbourhoods
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).subgroup.toSubgroup
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).LocalSpectrum := by
  let := hasStableNeighbourhoods_induced d (base U)
  have h := stableNeighbourhoods_of_equivariantHomeomorph
    (inducedConjugationHomeomorph d g (base U))
    (inducedConjugationHomeomorph_smul d g (base U))
  exact (SpatialSheaves.hasStableNeighbourhoods_iff
    ((inclusion (conjugateOpenSubgroup U g)).obj
      ((ρ.invariantConjugationEquivalence U g).functor.obj d))).mpr h

local instance conjugateLocalStable :
    HasStableNeighbourhoods
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).subgroup.toSubgroup
      ((inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d)).LocalSpectrum :=
  hasStableNeighbourhoods_conjugate_local d g

/-- The original rational translation and its inverse are proper smooth arrows. -/
def smoothConjugationIso (V : FiniteIndexLevel U) :
    smoothObject d V ≅
      smoothObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V) where
  hom := SmoothProperTransport.Hom.ofTransport (rationalConjugationIso d g V).hom
    (isProperMap_rationalConjugationIso_hom d g V)
  inv := SmoothProperTransport.Hom.ofTransport (rationalConjugationIso d g V).inv
    (isProperMap_rationalConjugationIso_inv d g V)
  hom_inv_id := by
    apply (SmoothProperTransport.forget ρ).map_injective
    exact (rationalConjugationIso d g V).hom_inv_id
  inv_hom_id := by
    apply (SmoothProperTransport.forget ρ).map_injective
    exact (rationalConjugationIso d g V).inv_hom_id

/-- Actual conjugation as a natural isomorphism of the existing smooth proper towers. -/
def smoothTowerConjugationIso :
    smoothTower d ≅ (conjugationEquivalence U g).functor ⋙
      smoothTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) :=
  NatIso.ofComponents (smoothConjugationIso d g) (by
    intro V W f
    apply (SmoothProperTransport.forget ρ).map_injective
    exact rationalConjugationIso_naturality d g f)

@[simp]
theorem smoothConjugationIso_hom_transport (V : FiniteIndexLevel U) :
    SmoothProperTransport.Hom.transport (smoothConjugationIso d g V).hom =
      (rationalConjugationIso d g V).hom := rfl

@[simp]
theorem smoothConjugationIso_inv_transport (V : FiniteIndexLevel U) :
    SmoothProperTransport.Hom.transport (smoothConjugationIso d g V).inv =
      (rationalConjugationIso d g V).inv := rfl

variable (R : Type u) [CommRing R]

/-- Pullback of all original compact functions along the conjugation homeomorphisms. -/
def compactFunctionsTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        compactFunctionsTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      compactFunctionsTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.compactFunctionsDiagram (R := R) ρ)

/-- The same original conjugation pullback after whole-group invariants. -/
def invariantCompactFunctionsTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        invariantCompactFunctionsTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      invariantCompactFunctionsTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.invariantCompactFunctionsDiagram (R := R) ρ)

/-- Conjugation of the full compact smooth Godement complexes at all original levels. -/
def godementCompactTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        godementCompactTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      godementCompactTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.godementCompactDiagram (R := R) ρ)

/-- Conjugation of those complexes after termwise whole-group invariants. -/
def godementInvariantCompactTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        godementInvariantCompactTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      godementInvariantCompactTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.godementInvariantCompactDiagram (R := R) ρ)

/-- The actual homology of the conjugation chain maps in every degree. -/
def godementCohomologyTowerConjugationIso (q : ℕ) :
    (conjugationEquivalence U g).functor.op ⋙
        godementCohomologyTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R q ≅
      godementCohomologyTower d R q :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.godementCohomologyDiagram (R := R) ρ q)

/-- Homology of the same original chain maps after termwise invariants. -/
def godementInvariantCohomologyTowerConjugationIso (q : ℕ) :
    (conjugationEquivalence U g).functor.op ⋙
        godementInvariantCohomologyTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R q ≅
      godementInvariantCohomologyTower d R q :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.godementInvariantCohomologyDiagram (R := R) ρ q)

/-- Conjugation retains the original invariants-edge squares in the arrow category. -/
def godementInvariantsArrowTowerConjugationIso (q : ℕ) :
    (conjugationEquivalence U g).functor.op ⋙
        godementInvariantsArrowTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R q ≅
      godementInvariantsArrowTower d R q :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.godementInvariantsArrowDiagram (R := R) ρ q)

/-- Conjugation of sheaf-derived compact sections with their existing degree-zero maps. -/
def compactDerivedZeroTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        compactDerivedZeroTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      compactDerivedZeroTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.compactDerivedZeroDiagram (R := R) ρ)

/-- The same sheaf-derived degree-zero transport after whole-group invariants. -/
def invariantCompactDerivedZeroTowerConjugationIso :
    (conjugationEquivalence U g).functor.op ⋙
        invariantCompactDerivedZeroTower
          ((ρ.invariantConjugationEquivalence U g).functor.obj d) R ≅
      invariantCompactDerivedZeroTower d R :=
  Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g))
    (SmoothProperTransport.invariantCompactDerivedZeroDiagram (R := R) ρ)

open OpenSubgroupTransport.Hom OpenSubgroupTransport.SmoothCohomology

local instance originalInducedStable (V : FiniteIndexLevel U) :
    HasStableNeighbourhoods G (rationalObject d V).InducedSpectrum :=
  hasStableNeighbourhoods_induced d V

local instance conjugateInducedStable (V : FiniteIndexLevel U) :
    HasStableNeighbourhoods G
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)).InducedSpectrum :=
  hasStableNeighbourhoods_induced
    ((ρ.invariantConjugationEquivalence U g).functor.obj d)
    ((conjugationEquivalence U g).functor.obj V)

/-- The forward compact-function map is the original proper pullback. -/
@[simp]
theorem compactFunctionsTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (compactFunctionsTowerConjugationIso d g R).hom.app (op V) =
      compactSupportPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- Its inverse uses the original inverse rational translation. -/
@[simp]
theorem compactFunctionsTowerConjugationIso_inv_app (V : FiniteIndexLevel U) :
    (compactFunctionsTowerConjugationIso d g R).inv.app (op V) =
      compactSupportPullbackNatTrans (R := R) (rationalConjugationIso d g V).inv
        (isProperMap_rationalConjugationIso_inv d g V) := rfl

/-- Whole-group invariants restrict precisely that original compact-function map. -/
@[simp]
theorem invariantCompactFunctionsTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (invariantCompactFunctionsTowerConjugationIso d g R).hom.app (op V) =
      invariantCompactSupportPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- The forward chain map is the full original coefficient and spatial pullback. -/
@[simp]
theorem godementCompactTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (godementCompactTowerConjugationIso d g R).hom.app (op V) =
      godementCompactPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- The invariant chain map retains the original termwise-invariant pullback. -/
@[simp]
theorem godementInvariantCompactTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (godementInvariantCompactTowerConjugationIso d g R).hom.app (op V) =
      godementInvariantCompactPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- The cohomology map is homology of the same original chain map. -/
@[simp]
theorem godementCohomologyTowerConjugationIso_hom_app (q : ℕ) (V : FiniteIndexLevel U) :
    (godementCohomologyTowerConjugationIso d g R q).hom.app (op V) =
      godementCohomologyPullbackNatTrans (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) q := rfl

/-- The invariant cohomology map is homology after termwise invariants. -/
@[simp]
theorem godementInvariantCohomologyTowerConjugationIso_hom_app
    (q : ℕ) (V : FiniteIndexLevel U) :
    (godementInvariantCohomologyTowerConjugationIso d g R q).hom.app (op V) =
      godementInvariantCohomologyPullbackNatTrans (R := R)
        (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) q := rfl

/-- The arrow isomorphism retains both original maps and their edge square. -/
@[simp]
theorem godementInvariantsArrowTowerConjugationIso_hom_app
    (q : ℕ) (V : FiniteIndexLevel U) :
    (godementInvariantsArrowTowerConjugationIso d g R q).hom.app (op V) =
      godementInvariantsEdgePullback (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) q := rfl

@[simp]
theorem compactDerivedZeroTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (compactDerivedZeroTowerConjugationIso d g R).hom.app (op V) =
      compactDerivedZeroPullback (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

@[simp]
theorem invariantCompactDerivedZeroTowerConjugationIso_hom_app (V : FiniteIndexLevel U) :
    (invariantCompactDerivedZeroTowerConjugationIso d g R).hom.app (op V) =
      invariantCompactDerivedZeroPullback (R := R) (rationalConjugationIso d g V).hom
        (isProperMap_rationalConjugationIso_hom d g V) := rfl

/-- Original compact functions are composed with the actual quotient homeomorphism. -/
@[simp]
theorem compactFunctionsTowerConjugationIso_apply (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M)
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)))
    (z : (rationalObject d V).InducedSpectrum) :
    (SmoothRep.hom (((compactFunctionsTowerConjugationIso d g R).hom.app (op V)).app M)
        s).val z =
      s.val (inducedConjugationHomeomorph d g V z) := rfl

/-- The inverse-label correction also appears in the original function pullback. -/
theorem compactFunctionsTowerConjugationIso_apply_mk (V : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M)
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)))
    (a : G) (x : (rationalObject d V).LocalSpectrum) :
    (SmoothRep.hom (((compactFunctionsTowerConjugationIso d g R).hom.app (op V)).app M)
        s).val ((rationalObject d V).inducedMk a x) =
      s.val ((rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)).inducedMk
          (a * g⁻¹) ((rationalConjugationIso d g V).hom.localSpectrumMap x)) := by
  rw [compactFunctionsTowerConjugationIso_apply, inducedConjugationHomeomorph_mk]

/-- Conjugation commutes with the comparison to termwise-invariant complexes. -/
@[reassoc]
theorem godementInvariantCompactTowerConjugationIso_comparison :
    Functor.whiskerRight (godementCompactTowerConjugationIso d g R).hom
        ((Functor.whiskeringRight _ _ _).obj
          ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ))) ≫
        (godementInvariantCompactTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementInvariantCompactTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (godementInvariantCompactTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.godementInvariantCompactDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- The original invariants edge commutes with conjugation in every degree. -/
@[reassoc]
theorem godementInvariantsEdgeTower_conjugation (q : ℕ) :
    (godementInvariantCohomologyTowerConjugationIso d g R q).hom ≫
        godementInvariantsEdgeTower d R q =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementInvariantsEdgeTower
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R q) ≫
        Functor.whiskerRight (godementCohomologyTowerConjugationIso d g R q).hom
          ((Functor.whiskeringRight _ _ _).obj (smoothInvariants R G)) := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.godementInvariantsEdgeDiagram (R := R) ρ q).naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- The Godement degree-zero identification preserves conjugation pullback. -/
@[reassoc]
theorem godementCohomologyZeroTowerIso_conjugation :
    (godementCohomologyTowerConjugationIso d g R 0).hom ≫
        (godementCohomologyZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementCohomologyZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (compactFunctionsTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.godementCohomologyZeroDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- The same Godement degree-zero identification after invariants. -/
@[reassoc]
theorem godementInvariantCohomologyZeroTowerIso_conjugation :
    (godementInvariantCohomologyTowerConjugationIso d g R 0).hom ≫
        (godementInvariantCohomologyZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementInvariantCohomologyZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (invariantCompactFunctionsTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact
    (SmoothProperTransport.godementInvariantCohomologyZeroDiagramIso (R := R) ρ).hom.naturality
      (smoothConjugationIso d g V.unop).hom.op

/-- Sheaf-derived degree zero recovers the same conjugation pullback of functions. -/
@[reassoc]
theorem compactDerivedZeroTowerIso_conjugation :
    (compactDerivedZeroTowerConjugationIso d g R).hom ≫
        (compactDerivedZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (compactDerivedZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (compactFunctionsTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.compactDerivedZeroDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- The sheaf-derived degree-zero identification after invariants is also preserved. -/
@[reassoc]
theorem invariantCompactDerivedZeroTowerIso_conjugation :
    (invariantCompactDerivedZeroTowerConjugationIso d g R).hom ≫
        (invariantCompactDerivedZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (invariantCompactDerivedZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (invariantCompactFunctionsTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.invariantCompactDerivedZeroDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- Both routes from Godement degree zero to sheaf-derived degree zero commute. -/
@[reassoc]
theorem godementDerivedZeroTowerIso_conjugation :
    (godementCohomologyTowerConjugationIso d g R 0).hom ≫
        (godementDerivedZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementDerivedZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (compactDerivedZeroTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.godementDerivedZeroDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

/-- The invariant Godement/sheaf-derived comparison commutes with conjugation. -/
@[reassoc]
theorem godementInvariantDerivedZeroTowerIso_conjugation :
    (godementInvariantCohomologyTowerConjugationIso d g R 0).hom ≫
        (godementInvariantDerivedZeroTowerIso d R).hom =
      Functor.whiskerLeft (conjugationEquivalence U g).functor.op
          (godementInvariantDerivedZeroTowerIso
            ((ρ.invariantConjugationEquivalence U g).functor.obj d) R).hom ≫
        (invariantCompactDerivedZeroTowerConjugationIso d g R).hom := by
  apply NatTrans.ext
  funext V
  exact (SmoothProperTransport.godementInvariantDerivedZeroDiagramIso (R := R) ρ).hom.naturality
    (smoothConjugationIso d g V.unop).hom.op

end OpenSubgroupTransport.FiniteIndexLevel

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
