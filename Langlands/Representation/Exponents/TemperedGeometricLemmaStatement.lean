import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Filtration.ObjectDefinitions

/-! # The geometric lemma for tempered representations (Renard VII.2.5)

For represented parabolics `P = MN` and `Q = LU` and a tempered representation `ρ` of
`M(F)`, the unitary part `(r_Q^G i_P^G ρ)_0` has a finite filtration whose graded pieces
are `i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`, one for each double coset `P z Q`, with the
intersection data of the represented geometric lemma VI.5.1.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedGeometricAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- The graded piece `i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0` of Renard VII.2.5 for one double
coset: the unitary part of the normalized Jacquet module of `ρ` along `P'`, for the split
component `a'` of `M'`, restricted along `e : L'(F) ≃ M'(F)` and induced from `L'(F)` to
`L(F)` along `Q'`. -/
def unitaryPieceRep
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
    (ha' : IsSplitComponent a') :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) → Rep.{max u v} ℂ (rationalPoints L) :=
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
  fun ρ => SmoothRep.toRep.obj
    ((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ').obj
      ((SmoothRep.pullbackFunctor D.e).obj
        (leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ)))

end GeometricLemmaIntersectionDatum

/-- Renard VII.2.5 for represented parabolics. For represented parabolics `P = MN` and
`Q = LU`, a split component of `L` and a tempered representation `ρ` of `M(F)`, there are
a finite enumeration of the actual double cosets `P(F) \ G(F) / Q(F)`, a representative
`z i` of each and intersection data for each representative such that, for every choice of
split components of the Levis `M'`, the unitary part `(r_Q^G i_P^G ρ)_0` has a finite
filtration whose graded pieces are, in some order, isomorphic to the pieces
`i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`. -/
def TemperedGeometricLemmaStatement : Prop :=
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
      (hmulQ : IsIso (subgroupMultiplication lQ rQ))
      (AL : CommGroupScheme (Spec (CommRingCat.of k))) (aL : AL.toGrp ⟶ L)
      (haL : IsSplitComponent aL),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hlQ.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        IsNormalizedExponentTempered hl.isConnectedReductive ρ →
          ∃ (m : ℕ)
            (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
              (pointImage q : Set (rationalPoints G)))
            (z : Fin m → rationalPoints G),
            (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i) ∧
            ∃ D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
                q lQ rQ hq hrQ hlQ hmulQ (z i),
              ∀ (A' : Fin m → CommGroupScheme (Spec (CommRingCat.of k)))
                (a' : ∀ i, (A' i).toGrp ⟶ (D i).M') (ha' : ∀ i, IsSplitComponent (a' i)),
                ∃ (s : ObjectRepFiltration
                    (SmoothRep.toRep.obj
                      (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
                        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) m)
                  (e : Equiv.Perm (Fin m)),
                  ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
                    ((D (e j)).unitaryPieceRep (ha' (e j)) ρ).ρ)

end Langlands.Aubert.General.RepresentedParabolic
