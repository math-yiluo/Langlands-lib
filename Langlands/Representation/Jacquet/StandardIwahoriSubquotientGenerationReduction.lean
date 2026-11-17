import Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements
import Langlands.Representation.Jacquet.StandardFixedVectorDetectionAssembly
import Langlands.Representation.Jacquet.StationaryRangeLift
import Langlands.Representation.Jacquet.StandardGeneralizedJacquetLift
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly
import Langlands.BruhatTits.SpecialCompact.AvailableBasisProof
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof

/-! # Renard VI.9.4 Corollary with the Iwahori hypothesis, from the special-vertex inputs

The only retained premise is `CuspidalSupport.RationalSpecialVertexCompactInputsStatement`.
The contracting element for the weak Jacquet lemma comes from the standard cocharacter
itself, so no split component and no contraction clause on `K` is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe uF uV uG uH

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Jacquet

section AbstractContraction

variable {H : Type uH} [Group H] [TopologicalSpace H]

/-- An element central in `M`, normalizing `N` and `Nbar`, whose positive powers
eventually conjugate every compact subset of `N` (forwards) and of `Nbar` (backwards)
into any identity neighbourhood, has a positive power that is an Iwahori contraction
for every compact open subgroup with the ordered decomposition along `Nbar`, `M`, `N`. -/
theorem exists_pow_isIwahoriContraction_of_eventualContraction
    {K : OpenSubgroup H} {N M Nbar : Subgroup H} {g : H}
    (hK : IsCompact (K : Set H)) (hN : IsClosed (N : Set H))
    (hNbar : IsClosed (Nbar : Set H))
    (hfactor : HasIwahoriIntersectionDecomposition K.toSubgroup M N Nbar)
    (hMN : M ≤ Subgroup.normalizer (N : Set H))
    (hMNbar : M ≤ Subgroup.normalizer (Nbar : Set H))
    (hgM : g ∈ M) (hcomm : ∀ m ∈ M, m * g = g * m)
    (hU : ∀ C : Set H, IsCompact C → C ⊆ (N : Set H) → ∀ W ∈ 𝓝 (1 : H),
      ∀ᶠ n : ℕ in atTop, ∀ c ∈ C, g ^ n * c * (g ^ n)⁻¹ ∈ W)
    (hO : ∀ C : Set H, IsCompact C → C ⊆ (Nbar : Set H) → ∀ W ∈ 𝓝 (1 : H),
      ∀ᶠ n : ℕ in atTop, ∀ c ∈ C, (g ^ n)⁻¹ * c * g ^ n ∈ W) :
    ∃ n : ℕ, IsIwahoriContraction K N M Nbar (g ^ n) := by
  have hKnhds : (K : Set H) ∈ 𝓝 (1 : H) := K.isOpen.mem_nhds K.one_mem
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp
    (hU ((K : Set H) ∩ N) (hK.inter_right hN) Set.inter_subset_right _ hKnhds)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp
    (hO ((K : Set H) ∩ Nbar) (hK.inter_right hNbar) Set.inter_subset_right _ hKnhds)
  have hn1 : n₁ ≤ n₁ + n₂ + 1 := by omega
  have hn2 : n₂ ≤ n₁ + n₂ + 1 := by omega
  have hnpos : 1 ≤ n₁ + n₂ + 1 := by omega
  have hgnM : g ^ (n₁ + n₂ + 1) ∈ M := pow_mem hgM _
  refine ⟨n₁ + n₂ + 1, hgnM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨l, m, u⟩, heq⟩ := hfactor.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, u, u.property, (congrArg Subtype.val heq).symm⟩
  · intro u hu
    exact ⟨hn₁ _ hn1 u ⟨hu.1, hu.2⟩,
      (Subgroup.mem_normalizer_iff.mp (hMN hgnM) u).mp hu.2⟩
  · intro m hm
    have hc : m * g ^ (n₁ + n₂ + 1) = g ^ (n₁ + n₂ + 1) * m :=
      (show Commute m g from hcomm m hm.2).pow_right _
    have h : (g ^ (n₁ + n₂ + 1))⁻¹ * m * g ^ (n₁ + n₂ + 1) = m := by
      rw [mul_assoc, hc, inv_mul_cancel_left]
    rw [h]
    exact hm
  · intro l hl
    refine ⟨hn₂ _ hn2 l ⟨hl.1, hl.2⟩, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hMNbar (inv_mem hgnM)) l).mp hl.2
    have h' : (g ^ (n₁ + n₂ + 1))⁻¹ * l * g ^ (n₁ + n₂ + 1) ∈ Nbar := by
      simpa only [inv_inv] using h
    exact h'
  · intro x hx
    obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp
      (hU {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx) _ hKnhds)
    refine ⟨r₀, ?_⟩
    rw [← pow_mul]
    exact hr₀ _ (le_mul_of_one_le_left (Nat.zero_le _) hnpos) x (Set.mem_singleton x)
  · intro L
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp
      (hO ((K : Set H) ∩ Nbar) (hK.inter_right hNbar) Set.inter_subset_right _
        (L.isOpen.mem_nhds L.one_mem))
    refine ⟨s₀, fun l hl => ?_⟩
    rw [← pow_mul]
    exact hs₀ _ (le_mul_of_one_le_left (Nat.zero_le _) hnpos) l ⟨hl.1, hl.2⟩

end AbstractContraction

section DynamicContraction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- For a cocharacter `χ` of an affine group over a nonarchimedean local field, every
compact open subgroup of `G(F)` with the ordered Iwahori decomposition along the dynamic
opposite radical, centralizer and radical of `χ` admits a contracting element in the
sense of `IsIwahoriContraction`: a power of `χ(t)` for a field unit `t` whose powers
tend to zero. -/
theorem exists_isIwahoriContraction_of_dynamic
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
      HasIwahoriIntersectionDecomposition K.toSubgroup
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) →
      ∃ g : rationalPoints G, IsIwahoriContraction K
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro K hK hfactor
  have : T2Space F := BruhatTits.localField_t2Space F
  obtain ⟨g, hgM, hcomm, hU, hO⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint (F := F) χ
  have hMNbar : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ≤
      Subgroup.normalizer (((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier
        (Over.mk (𝟙 _)) : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  obtain ⟨n, hn⟩ := exists_pow_isIwahoriContraction_of_eventualContraction hK
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints
      (Dynamic.inverseCocharacter χ))
    hfactor (Dynamic.centralizer_le_normalizer_unipotent χ _) hMNbar hgM hcomm hU hO
  exact ⟨g ^ n, hn⟩

end DynamicContraction

section StandardContraction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

local instance standardIwahoriReductionIsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardIwahoriReductionTopologicalSpace :
    TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- A compact open subgroup with the ordered Iwahori decomposition along an actual
standard parabolic has a contracting element in the standard Levi, for the standard
radical, Levi and opposite radical. No split component and no basis-member clause is
used: the element is a power of the standard cocharacter at a contracting field unit. -/
theorem exists_standard_isIwahoriContraction
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    {zeta : cocharacterLattice S} (hzeta : IsStandardCocharacter i ν J zeta)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)) :
    ∃ g : rationalPoints G, IsIwahoriContraction K (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J) g := by
  have hstd := standard_eq_dynamic_of_relativeRootNegation relativeRootNegation
    F G hG S i hi ν hν J zeta hzeta
  have hM : standardLeviPoints i ν J =
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hstd.2.1
  have hN : standardUnipotentPoints i ν J =
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hstd.2.2
  have hNbar := standardOppositeUnipotentPoints_eq_dynamic i ν hG hi hν hzeta
  rw [hM, hN, hNbar] at hIwahori ⊢
  exact exists_isIwahoriContraction_of_dynamic _ K hK hIwahori

/-- The weak Jacquet lemma for one actual standard parabolic, under the source's
Iwahori decomposition of `K` alone: a nonzero `K ∩ M_J`-fixed vector of the
unnormalized standard Jacquet module forces a nonzero `K`-fixed vector, for every
smooth representation. No finiteness or stabilization premise is used. -/
theorem standardIwahoriFixedJacquet_exists_ne_zero
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    {zeta : cocharacterLattice S} (hzeta : IsStandardCocharacter i ν J zeta)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ)
    (y : fixedVectors (standardJacquetAction i ν ρ J)
      (K.toSubgroup.comap (standardLeviPoints i ν J).subtype)) (hy : y ≠ 0) :
    ∃ x : fixedVectors ρ K.toSubgroup, x ≠ 0 := by
  let : Smooth G.X.hom := hG.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨g, hcon⟩ := exists_standard_isIwahoriContraction i ν hG hi hν hzeta K hK hIwahori
  obtain ⟨s, x, hx⟩ := exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction ρ hρ hK
    hcon (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) y
  refine ⟨x, fun hx0 => hy ?_⟩
  have h0 := hx.symm.trans
    (show mk ρ (standardUnipotentPoints i ν J) (x : V) = 0 by simp [hx0])
  exact Subtype.ext ((Representation.apply_bijective _ _).injective
    (h0.trans (map_zero _).symm))

end StandardContraction

end Langlands.Jacquet

namespace Langlands.NormalizedJacquetBridge

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Nonvanishing lifts from the actual normalized Jacquet module as soon as every
nonzero unnormalized `K ∩ M`-fixed Jacquet vector forces a nonzero `K`-fixed vector. -/
theorem nonzero_fixed_of_nonzero_unnormalizedLift
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (D : SmoothRep.{0, uG, uV} ℂ G)
    (hlift : ∀ y : fixedVectors (Jacquet.action D.representation N M hMN)
        (K.toSubgroup.comap M.subtype), y ≠ 0 →
      ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0)
    (hD : ∃ w : (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D,
      w ∈ fixedVectors
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
        (K.toSubgroup.comap M.subtype) ∧ w ≠ 0) :
    ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hD
  let e := normalizedFixedVectorsEquiv N M hN hMN hM K hK D
  apply hlift (e ⟨w, hw⟩)
  intro hez
  apply hw0
  have hwz : (⟨w, hw⟩ : fixedVectors
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
        (K.toSubgroup.comap M.subtype)) = 0 :=
    e.injective (hez.trans (map_zero e).symm)
  exact congrArg Subtype.val hwz

end Langlands.NormalizedJacquetBridge

namespace Langlands

/-- Rational-Levi fixed-vector detection when nonzero Levi-fixed vectors of the
unnormalized Jacquet module of `D` force nonzero `K`-fixed vectors of `D`. This
replaces surjectivity of the fixed-vector Jacquet map by nonvanishing. -/
theorem rationalLeviJacquetNonzeroFixedVector_of_lift
    (hfinite : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν)),
        let L := Standard.leviScheme i ν (rootSet i ν I)
        ∀ (hL : IsConnectedReductive L),
          haveI := hL.isAffineHom
          haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
          letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
          letI : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
          ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
            [T2Space (rationalPoints G)]
            [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
            [T2Space (rationalPoints L)]
            (hN : IsClosed (unipotent i ν I : Set (rationalPoints G)))
            (hMN : levi i ν I ≤ Subgroup.normalizer (unipotent i ν I))
            (_hM : IsClosed (levi i ν I : Set (rationalPoints G)))
            (_hcompact : ∀ s : Finset (unipotent i ν I),
              ∃ J : OpenSubgroup (unipotent i ν I),
                IsCompact (J : Set (unipotent i ν I)) ∧ ∀ n ∈ s, n ∈ J)
            (K : OpenSubgroup (rationalPoints G)) (K0 : Subgroup (rationalPoints G))
            (_hK : IsCompact (K : Set (rationalPoints G)))
            (_hK0 : K0 ≤ Subgroup.normalizer K.toSubgroup)
            (_hfactor : ∀ x : rationalPoints G, ∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I,
              ∃ k ∈ K0, x = m * n * k)
            (A D : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
            (_hlift : ∀ y : fixedVectors (Jacquet.action D.representation
                (unipotent i ν I) (levi i ν I) hMN)
                (K.toSubgroup.comap (levi i ν I).subtype), y ≠ 0 →
              ∃ w : D, w ∈ fixedVectors D.representation K.toSubgroup ∧ w ≠ 0)
            (_hgen : ∀ S : Subrepresentation A.representation,
              fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
            (_hDA : SmoothRep.IsSubquotient D A)
            (E : SmoothRep.{0, uF, uV} ℂ (levi i ν I))
            (_hEirr : E.IsIrreducible)
            (_hEsub : SmoothRep.IsSubquotient E
              ((Aubert.General.normalizedJacquetFunctor
                (unipotent i ν I) (levi i ν I) hN hMN).obj D))
            (_hcoeff : HasCompactSmoothDualCoefficients
              (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L)
                (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E)).representation),
            ∃ w : D, w ∈ fixedVectors D.representation K.toSubgroup ∧ w ≠ 0 := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro T i ν I L hL
  let := hL.isAffineHom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  intro _ _ _ _ _ _ hN hMN hM hcompact K K0 hK hK0 hfactor
    A D hlift hgen hDA E hEirr hEsub hcoeff
  let M := levi i ν I
  let J := Aubert.General.normalizedJacquetFunctor (unipotent i ν I) M hN hMN
  let JA := J.obj A
  let JD := J.obj D
  let e := leviRationalPointHomeomorph i ν I
  let KL : Subgroup (rationalPoints L) :=
    (K.toSubgroup.comap M.subtype).comap e.toMonoidHom
  have hKback : KL.comap e.symm.toMonoidHom = K.toSubgroup.comap M.subtype := by
    ext m
    change e (e.symm m) ∈ K.toSubgroup.comap M.subtype ↔
      m ∈ K.toSubgroup.comap M.subtype
    rw [e.apply_symm_apply]
  have hgenJA := NormalizedJacquetBridge.normalized_generation
    (unipotent i ν I) M hN hMN hM K K0 hK hK0 hfactor A hgen
  have hJDA : SmoothRep.IsSubquotient JD JA :=
    NormalizedJacquetBridge.normalized_isSubquotient (unipotent i ν I) M hN hMN hcompact hDA
  have hEJA : SmoothRep.IsSubquotient E JA :=
    smoothSubquotientTransitivity ℂ M JA JD E hEsub hJDA
  have hgenL : ∀ S : Subrepresentation (SmoothRep.pullback e JA).representation,
      fixedVectors (SmoothRep.pullback e JA).representation KL ≤ S.toSubmodule →
        S = ⊤ := by
    apply (fixedVectors_generate_comp_mulEquiv_iff JA.representation e.toMulEquiv KL).mpr
    change ∀ S : Subrepresentation JA.representation,
      fixedVectors JA.representation (KL.comap e.symm.toMonoidHom) ≤ S.toSubmodule → S = ⊤
    rwa [hKback]
  have hELirr : (SmoothRep.pullback e E).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff E.representation e).mpr hEirr
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hKL : IsCompact (KL : Set (rationalPoints L)) :=
    e.toHomeomorph.isCompact_preimage.mpr hKM
  obtain ⟨w, hw, hw0⟩ := rationalNormKernelFixedVectorDetection hfinite F L hL
    (SmoothRep.pullback e JA) (SmoothRep.pullback e E) KL hKL hELirr hgenL hcoeff
    (hEJA.pullback e)
  have hwM : w ∈ fixedVectors E.representation (K.toSubgroup.comap M.subtype) := by
    change w ∈ fixedVectors (E.representation.comp e.toMonoidHom) KL at hw
    rw [fixedVectors_comp_mulEquiv E.representation e.toMulEquiv KL] at hw
    change w ∈ fixedVectors E.representation (KL.comap e.symm.toMonoidHom) at hw
    rwa [hKback] at hw
  exact NormalizedJacquetBridge.nonzero_fixed_of_nonzero_unnormalizedLift (unipotent i ν I) M
    hN hMN hM K hK D hlift (NormalizedJacquetBridge.nonzero_fixed_subquotient KM hKM hEsub
      ⟨w, hwM, hw0⟩)

end Langlands

namespace Langlands.Jacquet

open Aubert.General

set_option maxHeartbeats 1600000 in
/-- Detect a nonzero `K`-fixed vector in every nonzero actual subquotient of a
representation generated by its `K`-fixed vectors, from the special-vertex inputs alone,
under the source's Iwahori decomposition of `K`. The relative root system and the
norm-kernel finite restriction are the published theorems, and the weak Jacquet lemma
replaces the generalized one. -/
theorem standardIwahoriSubquotient_nonzero_fixed_of_specialVertexInputs
    (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{uF}) :
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
        (_hν : IsGenericCocharacter i ν)
        (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν,
          ∃ zeta, IsStandardCocharacter i ν J zeta)
        (K0 : Subgroup (rationalPoints G))
        (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
          ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K0, g = m * n * k)
        (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
        (_hnormal : K0 ≤ Subgroup.normalizer K.toSubgroup)
        (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
          HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
            (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
        (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
        (_hgen : ∀ S : Subrepresentation V.representation,
          fixedVectors V.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
        (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
        (_hDA : SmoothRep.IsSubquotient D V) (_hD : Nontrivial D),
        ∃ w : D, w ∈ fixedVectors D.representation K.toSubgroup ∧ w ≠ 0 := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  intro T i hi ν hν hstandard K0 hIwasawa K hK hnormal hIwahori V hgen D hDA hD
  classical
  have := hi.isSplitSubtorus.mono
  have hRoot : RelativeRootSystemStatement.{uF} := relativeRootSystem
  have hStandard := standardCocharacterStatement_of_relativeRootSystem_of_signs
    hRoot relativeRootSignsDetermineDynamic
  have hInter := standardLeviIntersection_of_relativeRootSystem hRoot
  have hRoots := hRoot F G hG T i hi
  let V' := SmoothRep.universeLift.{uF + 1} V
  let D' := SmoothRep.universeLift.{uF + 1} D
  let : Nontrivial D := hD
  let : Nontrivial D' := (SmoothRep.universeLiftEquiv D).toLinearEquiv.symm.toEquiv.nontrivial
  have hgen' : fixedVectorGenerated K.toSubgroup V' :=
    (fixedVectorGenerated_universeLift_iff K.toSubgroup V).mpr hgen
  have hDA' : SmoothRep.IsSubquotient D' V' := hDA.universeLift
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  let hM := isClosed_levi_of_isNonarchimedeanLocalField i ν
  obtain ⟨I, -, E, hE, hEcusp, hEJ⟩ :=
    exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM D'
  obtain ⟨zeta, hzeta⟩ := hstandard (rootSet i ν I) (rootSet_subset i ν I)
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L :=
    BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I)
  have := hL.isAffineHom
  have := hL.smooth
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace F L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  have hcoeff := leviCompactCoefficients_of_specialVertexInputs
    hStandard hInter hRoot hInputs G hG T i hi ν hν hU I (hM I) hL E hEcusp
  have hlift : ∀ y : fixedVectors (Jacquet.action D'.representation
      (standardUnipotentPoints i ν (rootSet i ν I)) (standardLeviPoints i ν (rootSet i ν I))
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν (rootSet i ν I)))
      (K.toSubgroup.comap (standardLeviPoints i ν (rootSet i ν I)).subtype), y ≠ 0 →
      ∃ w : D', w ∈ fixedVectors D'.representation K.toSubgroup ∧ w ≠ 0 := by
    intro y hy
    obtain ⟨x, hx⟩ := standardIwahoriFixedJacquet_exists_ne_zero i ν hG hi hν hzeta K hK
      (hIwahori (rootSet i ν I) (rootSet_subset i ν I)) D'.representation D'.isSmooth y hy
    exact ⟨x.val, x.property, fun h => hx (Subtype.ext h)⟩
  have hfactor := standard_factorization_of_minimal i ν hG hi hν
    (rootSet i ν I) ⟨zeta, hzeta⟩ K0 hIwasawa
  have hcompact := standardUnipotentPoints_finite_compactOpenContainment i ν
    (rootSet i ν I) hG ⟨zeta, hzeta⟩
  have hdet := rationalLeviJacquetNonzeroFixedVector_of_lift
    CuspidalSupport.rationalNormKernelFiniteRestriction F G hG
    T i ν I hL (hU I)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν (rootSet i ν I))
    (hM I) hcompact K K0 hK hnormal hfactor V' D' hlift hgen' hDA' E hE hEJ hcoeff
  exact (exists_nonzero_fixed_universeLift_iff K.toSubgroup D).mp hdet

/-- Renard VI.9.4, Corollary, with the source's Iwahori hypothesis on `K`, from the
special-vertex inputs alone. This is a conditional reduction with one retained premise. -/
theorem standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs
    (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{uF}) :
    StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro T i hi ν hν hstandard K0 _hK0 hIwasawa K hK _hKK0 hnormal hIwahori V hgen
  exact SmoothRep.fixedVectors_generate_subquotients_of_detection V K hK
    (fun D hDA hD => standardIwahoriSubquotient_nonzero_fixed_of_specialVertexInputs
      hInputs F G hG T i hi ν hν hstandard K0 hIwasawa
      K hK hnormal hIwahori V hgen D hDA hD)

/-- Renard VI.9.4, Corollary, with the Iwahori hypothesis, from the joint
special-compact basis existence alone. -/
theorem standardIwahoriFixedVectorSubquotientGeneration_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF}) :
    StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV} :=
  standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs
    (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis hJoint)

end Langlands.Jacquet

namespace Langlands.Jacquet

open Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact

/-- Renard VI.9.4, Corollary, with the Iwahori hypothesis, from
`BruhatTitsAvailabilityStatement` (the availability conclusion of KP Theorem 9.2.7). -/
theorem standardIwahoriFixedVectorSubquotientGeneration_of_availability
    (hAvail : BruhatTitsAvailabilityStatement.{uF}) :
    StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV} :=
  standardIwahoriFixedVectorSubquotientGeneration_of_jointBasis
    (jointSpecialCompactBasisExistence_of_availability_and_basis hAvail
      availableSimultaneousStandardBasis)

/-- Renard VI.9.4, Corollary, with the Iwahori hypothesis, from the one-group clauses of
corrected KP Definition 4.1.26 (`GroupAxiomsExistenceStatement`). -/
theorem standardIwahoriFixedVectorSubquotientGeneration_of_groupAxiomsExistence
    (hGroup : GroupAxiomsExistenceStatement.{uF}) :
    StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV} :=
  standardIwahoriFixedVectorSubquotientGeneration_of_availability
    (bruhatTitsAvailabilityReduction hGroup)

set_option linter.defProp false in
/-- Record entry: the implication
`RationalSpecialVertexCompactInputsStatement → StandardIwahoriFixedVectorSubquotientGenerationStatement`,
proved by `standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs`. Its type
is a proposition; it introduces no new mathematical notion. -/
def standardIwahoriFixedVectorSubquotientGenerationOfSpecialVertexInputs :
    CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{uF} →
      StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV} :=
  standardIwahoriFixedVectorSubquotientGeneration_of_specialVertexInputs

end Langlands.Jacquet
