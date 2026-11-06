import Mathlib.GroupTheory.DoubleCoset
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Filtration.Definitions
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # The geometric lemma for represented parabolics (Renard VI.5.1)

For represented parabolics `P = MN` and `Q = LU` of a connected reductive group over a
nonarchimedean local field, the functor `r_Q ∘ i_P` from smooth representations of `M(F)`
to representations of `L(F)` has a natural finite filtration. Its graded pieces are
`i^L_{Q'} ∘ ι ∘ r^M_{P'}`, one for each double coset `P z Q`, where
`P' = M ∩ zQz⁻¹`, `Q' = L ∩ z⁻¹Pz` and `ι` is restriction along conjugation by `z`.
Representatives, intersection data and the filtration are all conclusions.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance geometricAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

/-- The composite `r_Q ∘ i_P` of normalized induction from `M(F)` to `G(F)` and the
normalized Jacquet functor from `G(F)` to `L(F)`, valued in all representations of `L(F)`. -/
def leviJacquetInductionFunctor (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ) (hlQ : IsRationalLeviSubgroup lQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ)) :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L) :=
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  leviInductionFunctor p l r hp hr hl hmul ⋙
    leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ ⋙ SmoothRep.toRep

/-- Intersection data for one double coset `P z Q`, as in Renard VI.5.1. The represented
parabolic `P' = M' N'` of `M` is `M ∩ zQz⁻¹`, with Levi `M ∩ zLz⁻¹` and radical
`M ∩ zUz⁻¹`; the represented parabolic `Q' = L' U'` of `L` is `L ∩ z⁻¹Pz`, with Levi
`L ∩ z⁻¹Mz` and radical `L ∩ z⁻¹Nz`. These six identities are equalities of subgroup functors
of `G`, so they identify the actual scheme intersections. The isomorphism `φ : L' ≅ M'` is
conjugation by `z`, and `e` is its map on rational points with the canonical topologies.
Finally `t` is a maximal split torus of `G` contained in `M'`, which holds for Renard's
representatives (V.4.7). This structure only bundles data; it asserts nothing about
representations. -/
structure GeometricLemmaIntersectionDatum (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ) (hlQ : IsRationalLeviSubgroup lQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (z : rationalPoints G) where
  /-- The parabolic `P' = M ∩ zQz⁻¹` of `M`. -/
  P' : GroupScheme (Spec (CommRingCat.of k))
  /-- The Levi `M' = M ∩ zLz⁻¹` of `P'`. -/
  M' : GroupScheme (Spec (CommRingCat.of k))
  /-- The radical `N' = M ∩ zUz⁻¹` of `P'`. -/
  N' : GroupScheme (Spec (CommRingCat.of k))
  p' : P' ⟶ M
  l' : M' ⟶ P'
  r' : N' ⟶ P'
  hp' : IsParabolicSubgroup p'
  hr' : LeviSubgroup.IsGeometricUnipotentRadical r'
  hl' : IsRationalLeviSubgroup l'
  hmul' : IsIso (subgroupMultiplication l' r')
  /-- The parabolic `Q' = L ∩ z⁻¹Pz` of `L`. -/
  Q' : GroupScheme (Spec (CommRingCat.of k))
  /-- The Levi `L' = L ∩ z⁻¹Mz` of `Q'`. -/
  L' : GroupScheme (Spec (CommRingCat.of k))
  /-- The radical `U' = L ∩ z⁻¹Nz` of `Q'`. -/
  U' : GroupScheme (Spec (CommRingCat.of k))
  q' : Q' ⟶ L
  lQ' : L' ⟶ Q'
  rQ' : U' ⟶ Q'
  hq' : IsParabolicSubgroup q'
  hrQ' : LeviSubgroup.IsGeometricUnipotentRadical rQ'
  hlQ' : IsRationalLeviSubgroup lQ'
  hmulQ' : IsIso (subgroupMultiplication lQ' rQ')
  parabolic_eq : SubgroupFunctor.range (p' ≫ l ≫ p) =
    SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (q ≫ (G.innerIso z).hom)
  levi_eq : SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p) =
    SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q ≫ (G.innerIso z).hom)
  radical_eq : SubgroupFunctor.range (r' ≫ p' ≫ l ≫ p) =
    SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (rQ ≫ q ≫ (G.innerIso z).hom)
  parabolic_eq' : SubgroupFunctor.range (q' ≫ lQ ≫ q) =
    SubgroupFunctor.range (lQ ≫ q) ⊓ SubgroupFunctor.range (p ≫ (G.innerIso z⁻¹).hom)
  levi_eq' : SubgroupFunctor.range (lQ' ≫ q' ≫ lQ ≫ q) =
    SubgroupFunctor.range (lQ ≫ q) ⊓ SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom)
  radical_eq' : SubgroupFunctor.range (rQ' ≫ q' ≫ lQ ≫ q) =
    SubgroupFunctor.range (lQ ≫ q) ⊓ SubgroupFunctor.range (r ≫ p ≫ (G.innerIso z⁻¹).hom)
  /-- Conjugation by `z`, `L' ≅ M'`. -/
  φ : L' ≅ M'
  φ_comp : φ.hom ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom
  /-- The rational points of `φ`, a topological-group isomorphism `L'(F) ≃ M'(F)`. -/
  e : letI := leviPointTopology lQ' hlQ'
    letI := leviPointTopology l' hl'
    rationalPoints L' ≃ₜ* rationalPoints M'
  e_apply : ∀ x, e x = rationalPoints.map φ.hom x
  /-- A split torus `T` of `G` contained in `M' = M ∩ zLz⁻¹`. -/
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  /-- The inclusion `T ⟶ M'`. -/
  t : torus.toGrp ⟶ M'
  /-- `T` is a maximal split torus of `G`. -/
  isMaximalSplitTorus : IsMaximalSplitTorus (t ≫ l' ≫ p' ≫ l ≫ p)

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- The graded piece `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of Renard VI.5.1: the normalized Jacquet
functor of `M(F)` along `P'`, restriction along `e`, then normalized induction from
`L'(F)` to `L(F)` along `Q'`. -/
def pieceFunctor
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z) :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L) :=
  haveI := hl.isConnectedReductive.isAffineHom
  haveI := hlQ.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
  haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  letI := leviPointTopology D.l' D.hl'
  letI := leviPointTopology D.lQ' D.hlQ'
  leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ⋙
    SmoothRep.pullbackFunctor D.e ⋙
    leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ' ⋙ SmoothRep.toRep

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.1 for represented parabolics. For represented parabolics `P = MN` and
`Q = LU` of a connected reductive group over a nonarchimedean local field, there are a finite
enumeration of the actual double cosets `P(F) \ G(F) / Q(F)`, a representative `z i` of each,
and intersection data for each representative, such that `r_Q ∘ i_P` is glued, in some order,
from the graded pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}` by a natural finite filtration. -/
def RepresentedGeometricLemmaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      ∃ (m : ℕ)
        (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
          (pointImage q : Set (rationalPoints G)))
        (z : Fin m → rationalPoints G),
        (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i) ∧
        ∃ D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
            q lQ rQ hq hrQ hlQ hmulQ (z i),
          IsGluedFrom
            (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
            (fun i => (D i).pieceFunctor)

end Langlands.Aubert.General.RepresentedParabolic
