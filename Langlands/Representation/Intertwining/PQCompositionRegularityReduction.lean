import Langlands.Representation.Intertwining.PQRegularityPerClass
import Langlands.Representation.Intertwining.PieceKernelFaithful
import Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction
import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Geometric.RepresentedGeometricLemmaTorusFactorConstruction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # Inheritance of regularity in Renard VII.3.5 (i), reduced to Bruhat geometry -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Transfer

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance transferAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N P₁ N₁ Q U Q₁ U₁ : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} {r₁ : N₁ ⟶ P₁} {hp₁ : IsParabolicSubgroup p₁}
  {hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁} {hl₁ : IsRationalLeviSubgroup l₁}
  {hmul₁ : IsIso (subgroupMultiplication l₁ r₁)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {q₁ : Q₁ ⟶ G} {lQ₁ : M ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁} {hq₁ : IsParabolicSubgroup q₁}
  {hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁} {hlQ₁ : IsRationalLeviSubgroup lQ₁}
  {hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

/-- For two intersection data at the same `z`, for parabolics `P` and `P₁` with the same
embedding of `M` and the same `Q`, the two Levis `L' = M ∩ z⁻¹Mz` are isomorphic over `G`. -/
def leviIsoOfSameLevi
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (D' : GeometricLemmaIntersectionDatum p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
      q lQ rQ hq hrQ hlQ hmulQ z)
    (hM : l ≫ p = l₁ ≫ p₁) : D.L' ≅ D'.L' :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (D.lQ' ≫ D.q' ≫ lQ ≫ q))
    ⟨D.isClosedSubgroup_lQ'_q'_lQ_q.mono_overHom, rfl⟩
    ⟨D'.isClosedSubgroup_lQ'_q'_lQ_q.mono_overHom, by
      rw [D.levi_eq', D'.levi_eq', reassoc_of% hM]⟩

omit [IsAffineHom G.X.hom] [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
theorem leviIsoOfSameLevi_hom_comp
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (D' : GeometricLemmaIntersectionDatum p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
      q lQ rQ hq hrQ hlQ hmulQ z)
    (hM : l ≫ p = l₁ ≫ p₁) :
    (D.leviIsoOfSameLevi D' hM).hom ≫ D'.lQ' ≫ D'.q' ≫ lQ ≫ q =
      D.lQ' ≫ D.q' ≫ lQ ≫ q :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The intersection datum for `(P₁, Q)` at `z` with the `P'`-side, `φ`, `e` and torus of `D`
(a datum for `(P, Q)` at `z`, where `P` and `P₁` have the same embedding of `M`) and the
`Q'`-side of `D'`, its Levi reparametrized by `leviIsoOfSameLevi`. -/
def withSourceOf
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (D' : GeometricLemmaIntersectionDatum p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
      q lQ rQ hq hrQ hlQ hmulQ z)
    (hM : l ≫ p = l₁ ≫ p₁) :
    GeometricLemmaIntersectionDatum p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ q lQ rQ hq hrQ hlQ hmulQ z where
  P' := D.P'
  M' := D.M'
  N' := D.N'
  p' := D.p'
  l' := D.l'
  r' := D.r'
  hp' := D.hp'
  hr' := D.hr'
  hl' := D.hl'
  hmul' := D.hmul'
  Q' := D'.Q'
  L' := D.L'
  U' := D'.U'
  q' := D'.q'
  lQ' := (D.leviIsoOfSameLevi D' hM).hom ≫ D'.lQ'
  rQ' := D'.rQ'
  hq' := D'.hq'
  hrQ' := D'.hrQ'
  hlQ' := D'.hlQ'.iso_comp _
  hmulQ' := isIso_subgroupMultiplication_iso_comp _ D'.hmulQ'
  parabolic_eq := by rw [← hM]; exact D.parabolic_eq
  levi_eq := by rw [← hM]; exact D.levi_eq
  radical_eq := by rw [← hM]; exact D.radical_eq
  parabolic_eq' := D'.parabolic_eq'
  levi_eq' := by rw [Category.assoc, SubgroupFunctor.range_iso_comp]; exact D'.levi_eq'
  radical_eq' := D'.radical_eq'
  φ := D.φ
  φ_comp := by
    rw [← hM, D.φ_comp, Category.assoc, reassoc_of% (D.leviIsoOfSameLevi_hom_comp D' hM)]
  e := D.e
  e_apply := D.e_apply
  torus := D.torus
  t := D.t
  isMaximalSplitTorus := by rw [← hM]; exact D.isMaximalSplitTorus

/-- The intersection datum for `(P, Q₁)` at `z` with all data of `D` (a datum for `(P, Q)`),
when `Q` and `Q₁` have the same embedding of `M` and `M ∩ zQz⁻¹ = M ∩ zQ₁z⁻¹`,
`M ∩ zUz⁻¹ = M ∩ zU₁z⁻¹`. -/
def withTargetOfEq
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (hL : lQ ≫ q = lQ₁ ≫ q₁)
    (hpar : SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (q₁ ≫ (G.innerIso z).hom))
    (hrad : SubgroupFunctor.range (l ≫ p) ⊓
        SubgroupFunctor.range (rQ ≫ q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (rQ₁ ≫ q₁ ≫ (G.innerIso z).hom)) :
    GeometricLemmaIntersectionDatum p l r hp hr hl hmul q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ z where
  P' := D.P'
  M' := D.M'
  N' := D.N'
  p' := D.p'
  l' := D.l'
  r' := D.r'
  hp' := D.hp'
  hr' := D.hr'
  hl' := D.hl'
  hmul' := D.hmul'
  Q' := D.Q'
  L' := D.L'
  U' := D.U'
  q' := D.q'
  lQ' := D.lQ'
  rQ' := D.rQ'
  hq' := D.hq'
  hrQ' := D.hrQ'
  hlQ' := D.hlQ'
  hmulQ' := D.hmulQ'
  parabolic_eq := D.parabolic_eq.trans hpar
  levi_eq := by rw [D.levi_eq, reassoc_of% hL]
  radical_eq := D.radical_eq.trans hrad
  parabolic_eq' := by rw [← hL]; exact D.parabolic_eq'
  levi_eq' := by rw [← hL]; exact D.levi_eq'
  radical_eq' := by rw [← hL]; exact D.radical_eq'
  φ := D.φ
  φ_comp := by rw [← reassoc_of% hL]; exact D.φ_comp
  e := D.e
  e_apply := D.e_apply
  torus := D.torus
  t := D.t
  isMaximalSplitTorus := D.isMaximalSplitTorus

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

set_option maxHeartbeats 1600000 in
/-- Swapping in the `Q'`-side of another datum does not change the piece kernel: both are the
kernel on the common inner representation `ι ∘ r^M_{P'}(σ)`. -/
theorem pieceSplitComponentKernel_withSourceOf
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (D' : GeometricLemmaIntersectionDatum p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
      q lQ rQ hq hrQ hlQ hmulQ z)
    (hM : l ≫ p = l₁ ≫ p₁) {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    pieceSplitComponentKernel a (D.withSourceOf D' hM) σ = pieceSplitComponentKernel a D σ := by
  obtain ⟨b, hb, -⟩ := D.exists_isCentralSplitTorus_factor ha.isCentralSplitTorus
  have hb' : b ≫ (D.withSourceOf D' hM).lQ' ≫ (D.withSourceOf D' hM).q' = a := by
    have hrep : (SubgroupFunctor.range (lQ ≫ q)).IsRepresentedBy (lQ ≫ q) :=
      ⟨(hlQ.isClosedSubgroup.comp hq.isClosedSubgroup).mono_overHom, rfl⟩
    apply SubgroupFunctor.IsRepresentedBy.hom_ext hrep
    change (b ≫ ((D.leviIsoOfSameLevi D' hM).hom ≫ D'.lQ') ≫ D'.q') ≫ lQ ≫ q = a ≫ lQ ≫ q
    rw [← hb]
    simp only [Category.assoc]
    rw [D.leviIsoOfSameLevi_hom_comp D' hM]
  rw [(D.withSourceOf D' hM).pieceSplitComponentKernel_eq_inner ha b hb' σ,
    D.pieceSplitComponentKernel_eq_inner ha b hb σ]
  rfl

set_option maxHeartbeats 1600000 in
/-- Rewriting the target parabolic does not change the piece kernel: both are the kernel on the
same inner representation. -/
theorem pieceSplitComponentKernel_withTargetOfEq
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (hL : lQ ≫ q = lQ₁ ≫ q₁)
    (hpar : SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (q₁ ≫ (G.innerIso z).hom))
    (hrad : SubgroupFunctor.range (l ≫ p) ⊓
        SubgroupFunctor.range (rQ ≫ q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (rQ₁ ≫ q₁ ≫ (G.innerIso z).hom))
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    pieceSplitComponentKernel (hq := hq₁) (hrQ := hrQ₁) (hlQ := hlQ₁) (hmulQ := hmulQ₁) a
        (D.withTargetOfEq hL hpar hrad) σ =
      pieceSplitComponentKernel a D σ := by
  obtain ⟨b, hb, -⟩ := D.exists_isCentralSplitTorus_factor ha.isCentralSplitTorus
  rw [(D.withTargetOfEq hL hpar hrad).pieceSplitComponentKernel_eq_inner ha b hb σ,
    D.pieceSplitComponentKernel_eq_inner ha b hb σ]
  rfl

end GeometricLemmaIntersectionDatum

end Transfer

/-- The Bruhat-order input of the regularity part of Renard VII.3.5 (i) (printed pp.237–239),
for `z ∈ G(F)` such that `M ∩ zMz⁻¹` contains a maximal split torus `T` of `G`:
* if `P₂zP₃ <_{P₂P₃} P₂P₃` then `P₁zP₃ <_{P₁P₃} P₁P₃`;
* if `P₁zP₂ <_{P₁P₂} P₁P₂` then `P₁zP₃ <_{P₁P₃} P₁P₃`, `M ∩ zP₂z⁻¹ = M ∩ zP₃z⁻¹` and
  `M ∩ zN₂z⁻¹ = M ∩ zN₃z⁻¹`.
The hypotheses are those of `PQCompositionRegularityStatement`. -/
def PQCompositionBruhatStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (_hp₁ : IsParabolicSubgroup p₁) (_hl₁ : IsRationalLeviSubgroup l₁)
      (_hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (_hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (_hp₂ : IsParabolicSubgroup p₂) (_hl₂ : IsRationalLeviSubgroup l₂)
      (_hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (_hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (_hp₃ : IsParabolicSubgroup p₃) (_hl₃ : IsRationalLeviSubgroup l₃)
      (_hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (_hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        ∀ (z : rationalPoints G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
          (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
          ∀ ta : T.toGrp ⟶ M, ta ≫ l₁ ≫ p₁ = i →
          ∀ tb : T.toGrp ⟶ M, tb ≫ l₁ ≫ p₁ ≫ (G.innerIso z).hom = i →
          (Geometric.BruhatLT (pointImage p₂) (pointImage p₃)
              (DoubleCoset.mk (pointImage p₂) (pointImage p₃) z)
              (identityParabolicDoubleCoset p₂ p₃) →
            Geometric.BruhatLT (pointImage p₁) (pointImage p₃)
              (DoubleCoset.mk (pointImage p₁) (pointImage p₃) z)
              (identityParabolicDoubleCoset p₁ p₃)) ∧
          (Geometric.BruhatLT (pointImage p₁) (pointImage p₂)
              (DoubleCoset.mk (pointImage p₁) (pointImage p₂) z)
              (identityParabolicDoubleCoset p₁ p₂) →
            Geometric.BruhatLT (pointImage p₁) (pointImage p₃)
                (DoubleCoset.mk (pointImage p₁) (pointImage p₃) z)
                (identityParabolicDoubleCoset p₁ p₃) ∧
              SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                  SubgroupFunctor.range (p₂ ≫ (G.innerIso z).hom) =
                SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                  SubgroupFunctor.range (p₃ ≫ (G.innerIso z).hom) ∧
              SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                  SubgroupFunctor.range (r₂ ≫ p₂ ≫ (G.innerIso z).hom) =
                SubgroupFunctor.range (l₁ ≫ p₁) ⊓
                  SubgroupFunctor.range (r₃ ≫ p₃ ≫ (G.innerIso z).hom))

set_option maxHeartbeats 1000000 in
/-- The regularity part of Renard VII.3.5 (i) from its Bruhat-order input: a piece of the
geometric lemma for `(P₂, P₃)`, resp. `(P₁, P₂)`, below the identity is, with the same piece
kernel, a piece for `(P₁, P₃)` below the identity. -/
theorem pqCompositionRegularity_of_bruhat (hB : PQCompositionBruhatStatement.{u}) :
    PQCompositionRegularityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
    pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
  have hB' := hB k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
    pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1
  have := hl₁.isConnectedReductive.isAffineHom
  let := leviPointTopology l₁ hl₁
  intro σ hreg
  have h13 := (isPQRegular_iff_forall_piece k G hG P₁ M N₁ P₃ N₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃ h31.symm A a ha σ).1 hreg
  constructor
  · refine (isPQRegular_iff_forall_piece k G hG P₂ M N₂ P₃ N₃ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃ (h21.trans h31.symm) A a ha σ).2 ?_
    intro z hz D
    have hta : (D.t ≫ D.l' ≫ D.p') ≫ l₁ ≫ p₁ = D.t ≫ D.l' ≫ D.p' ≫ l₂ ≫ p₂ := by
      rw [h21]; simp only [Category.assoc]
    have htb₃ : (D.t ≫ D.φ.inv ≫ D.lQ' ≫ D.q') ≫ l₃ ≫ p₃ ≫ (G.innerIso z).hom =
        D.t ≫ D.l' ≫ D.p' ≫ l₂ ≫ p₂ := by
      simp only [Category.assoc]
      rw [← D.φ_comp, Iso.inv_hom_id_assoc]
    have htb : (D.t ≫ D.φ.inv ≫ D.lQ' ≫ D.q') ≫ l₁ ≫ p₁ ≫ (G.innerIso z).hom =
        D.t ≫ D.l' ≫ D.p' ≫ l₂ ≫ p₂ := by
      rw [← reassoc_of% h31]; exact htb₃
    let D' := geometricLemmaIntersectionDatumOfTorusFactors parabolicDynamic hG
      p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃ z
      (D.t ≫ D.l' ≫ D.p' ≫ l₂ ≫ p₂) D.isMaximalSplitTorus (D.t ≫ D.l' ≫ D.p') hta
      (D.t ≫ D.φ.inv ≫ D.lQ' ≫ D.q') htb₃
    have hlt := (hB' z D.torus _ D.isMaximalSplitTorus _ hta _ htb).1 hz
    have h := h13 z hlt (D.withSourceOf D' h21)
    rw [D.pieceSplitComponentKernel_withSourceOf D' h21 ha σ] at h
    exact h
  · refine (isPQRegular_iff_forall_piece k G hG P₁ M N₁ P₂ N₂ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ h21.symm A a ha σ).2 ?_
    intro z hz D
    have hta : (D.t ≫ D.l' ≫ D.p') ≫ l₁ ≫ p₁ = D.t ≫ D.l' ≫ D.p' ≫ l₁ ≫ p₁ := by
      simp only [Category.assoc]
    have htb : (D.t ≫ D.φ.inv ≫ D.lQ' ≫ D.q') ≫ l₁ ≫ p₁ ≫ (G.innerIso z).hom =
        D.t ≫ D.l' ≫ D.p' ≫ l₁ ≫ p₁ := by
      rw [← reassoc_of% h21]
      simp only [Category.assoc]
      rw [← D.φ_comp, Iso.inv_hom_id_assoc]
    obtain ⟨hlt, hpar, hrad⟩ :=
      (hB' z D.torus _ D.isMaximalSplitTorus _ hta _ htb).2 hz
    have hL : l₂ ≫ p₂ = l₃ ≫ p₃ := h21.trans h31.symm
    have h := h13 z hlt (D.withTargetOfEq hL hpar hrad)
    rw [D.pieceSplitComponentKernel_withTargetOfEq hL hpar hrad ha σ] at h
    exact h

set_option linter.defProp false in
/-- The implication of `pqCompositionRegularity_of_bruhat`, recorded as a definition: the
Bruhat-order input implies `PQCompositionRegularityStatement`. -/
def pqCompositionRegularityOfBruhat :
    PQCompositionBruhatStatement.{u} → PQCompositionRegularityStatement.{u, v} :=
  pqCompositionRegularity_of_bruhat

end Langlands.Aubert.General.RepresentedParabolic
