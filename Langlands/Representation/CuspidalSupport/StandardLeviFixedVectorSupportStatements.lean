import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionStatement

/-! # Compact open subgroups and standard Levi subgroups in the Bernstein decomposition
(Renard VI.10.6, Corollary)

Statements only. Let `K` be a compact open subgroup of `G(F)`, contained and normal in `K₀`, with
an Iwahori decomposition along every standard parabolic `P_J = M_J N_J`.

* `StandardLeviCompactInheritanceStatement`: `K_M = K ∩ M_J` has the same properties relative to
  `M_J` (the paragraph before the Corollary).
* `StandardRepresentativeFixedVectorCriterionStatement`: for a standard cuspidal datum
  `a = (M_I, σ)`, the class `[a]_G` lies in `B(G)_K` iff `σ` has a nonzero `K ∩ M_I`-fixed vector
  (the first claim of the Corollary's proof).
* `StandardLeviFixedVectorSupportStatement`: the Corollary `B(M)_{K_M} = i_{MG}⁻¹(B(G)_K)`, with
  the cuspidal data of `M_J` given, as in `BernsteinInductionRestrictionStatement`, by the standard
  cuspidal data `b` of `G` with `b.roots ⊆ J`. -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open Langlands.Jacquet

namespace Langlands.CuspidalSupport

/-- The standard Levi scheme is a closed subgroup (the local instance of `BernsteinData`). -/
local instance standardLeviFixedClosedImmersion {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)

/-- The standard Levi scheme is affine (the local instance of `BernsteinData`). -/
local instance standardLeviFixedAffine {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left

/-- The standard Levi scheme is locally of finite type (the local instance of
`BernsteinData`). -/
local instance standardLeviFixedFiniteType {F : Type uF} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I : Finset (SimpleRoot i ν)} :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Renard VI.10.6, the paragraph before the Corollary: for `K` as in the VI.10.6 Proposition
and a standard Levi `M = M_J`, `K_M = K ∩ M` has the same properties as `K` relative to `M`:
it is compact open in `M`; it is contained and normal in a compact subgroup `K₀M ≤ M` for which
the Iwasawa decomposition `M = M_∅ (N_∅ ∩ M) K₀M` holds; and it has an Iwahori decomposition
along every standard parabolic `M_I (N_I ∩ M)`, `I ⊆ J`, of `M`. -/
def StandardLeviCompactInheritanceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
      (J : Set (characterLattice S)), J ⊆ simpleRelativeRoots i ν →
      let M := standardLeviPoints i ν J
      IsOpen ((K.toSubgroup.comap M.subtype : Subgroup M) : Set M) ∧
        IsCompact ((K.toSubgroup.comap M.subtype : Subgroup M) : Set M) ∧
        (∃ K₀M : Subgroup (rationalPoints G), K₀M ≤ M ∧
          IsCompact (K₀M : Set (rationalPoints G)) ∧
          (∀ g ∈ M, ∃ m ∈ standardLeviPoints i ν ∅,
            ∃ n ∈ standardUnipotentPoints i ν ∅ ⊓ M, ∃ k ∈ K₀M, g = m * n * k) ∧
          K.toSubgroup ⊓ M ≤ K₀M ∧ K₀M ≤ Subgroup.normalizer (K.toSubgroup ⊓ M)) ∧
        ∀ I ⊆ J,
          HasIwahoriIntersectionDecomposition (K.toSubgroup ⊓ M) (standardLeviPoints i ν I)
            (standardUnipotentPoints i ν I ⊓ M) (standardOppositeUnipotentPoints i ν I ⊓ M)

/-- Renard VI.10.6, first claim of the proof of the Corollary: for a standard cuspidal datum
`a = (M_I, σ)` of the standard family, the inertial class `[a]_G` lies in `B(G)_K` (some
irreducible representation with inertial support `[a]_G` has a nonzero `K`-fixed vector) iff `σ`,
transported to the literal Levi `M_I(F)`, has a nonzero vector fixed by `K ∩ M_I(F)`. -/
def StandardRepresentativeFixedVectorCriterionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)),
      letI : T2Space F := BruhatTits.localField_t2Space F
      letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
      letI : NonarchimedeanGroup (rationalPoints G) :=
        Plancherel.rationalPoints_nonarchimedeanGroup G
      let family := standardBernsteinFamily i ν hG hi hν
      ∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
        (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
            IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ∧
              Nontrivial (fixedVectors π.representation K.toSubgroup)) ↔
          Nontrivial (fixedVectors
            (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
            (K.toSubgroup.comap (levi i ν a.roots).subtype))

/-- Renard VI.10.6, Corollary: `B(M)_{K_M} = i_{MG}⁻¹(B(G)_K)` for the standard Levi `M = M_J`.
An inertial class `𝔱 = [b]_M` of `M` is given by a standard cuspidal datum `b` with
`b.roots ⊆ J`, and `i_{MG}(𝔱) = [b]_G`. The left side says `𝔱 ∈ B(M)_{K_M}`: some irreducible
smooth `τ` of `M(F)` with a nonzero `K ∩ M(F)`-fixed vector is a subquotient of the normalized
induction inside `M` of a datum `b'` with roots in `J` that is `M(F)`-inertially equivalent to
`b` (conjugation by a point of `M(F)` and an unramified twist). The right side says
`[b]_G ∈ B(G)_K`. -/
def StandardLeviFixedVectorSupportStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)),
      letI : T2Space F := BruhatTits.localField_t2Space F
      letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
      letI : NonarchimedeanGroup (rationalPoints G) :=
        Plancherel.rationalPoints_nonarchimedeanGroup G
      let family := standardBernsteinFamily i ν hG hi hν
      ∀ (J : Finset (SimpleRoot i ν)) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
        b.roots ⊆ J →
        ((∃ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J),
            τ.IsIrreducible ∧
              Nontrivial (fixedVectors τ.representation
                (K.toSubgroup.comap (levi i ν J).subtype)) ∧
              ∃ (I : Finset J) (b' : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
                (h : leviIndex J I = b'.roots),
                (∃ c : RationalLeviConjugacy
                    (Standard.leviHom i ν (rootSet i ν b.roots))
                    (Standard.leviHom i ν (rootSet i ν b'.roots)),
                  c.point ∈ levi i ν J ∧
                    IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots)
                      b.representation (rationalIsoPullback c.iso b'.representation)) ∧
                SmoothRep.IsSubquotient τ
                  ((leviNormalizedInductionFunctor (family.closedLevi J)
                    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
                      family.maximalSplitTorus family.genericCocharacter b'.roots J
                      (h ▸ leviIndex_subset J I))
                    (h ▸ family.leviDecomposition J I) (family.closedUnipotent b'.roots)).obj
                    (bernsteinLiteralLeviRep i ν b'.roots b'.representation))) ↔
          ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
            IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family b) π ∧
              Nontrivial (fixedVectors π.representation K.toSubgroup))

end Langlands.CuspidalSupport
