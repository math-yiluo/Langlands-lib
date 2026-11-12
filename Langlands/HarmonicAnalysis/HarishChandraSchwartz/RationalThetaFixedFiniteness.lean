import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFixedOrbits
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Finiteness of `Θ^H` for the standard parabolic subgroups of `G(F)` (Remark VIII.1.3)

On actual rational points, for the standard parabolic subgroups `P_I(F)` of a connected reductive
group `G` over a nonarchimedean local field, with `A_{M_I}(F)` the image of a split component of
the Levi scheme:

* `finite_rationalInducedDiscreteSeriesFixedOrbits_of_statement`: for one `I`, the set of orbits
  `O` with `(O, P_I(F)) ∈ Θ^H` is finite;
* `exists_finite_rationalFourierOrbitSection_ne_zero_of_statement`: for one `I` and `f ∈ C(G)`,
  the orbits with `ψ_f[O, P_I] ≠ 0` lie in a finite set;
* `rationalThetaFixed` and `finite_rationalThetaFixed`: Waldspurger's `Θ^H` restricted to the
  standard parabolic subgroups, as a set of pairs `(I, O)`, is finite;
* `exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement`: for `f ∈ C(G)`, the
  pairs `(I, O)` with `ψ_f[O, P_I] ≠ 0` lie in a finite set;

all under the published statement of Theorem VIII.1.2 (`RationalDiscreteSeriesOrbitFinitenessStatement`),
applied to the Levi subgroups through `finite_discreteSeriesFixedOrbits_standardLevi`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

-- The Levi group scheme `L` with `L(F) ≃ M_I(F)`.
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

-- The decomposition `P_I(F) = M_I(F) ⋉ U_I(F)` and the closedness of `U_I(F)`.
set_option hygiene false in
local notation "𝐡" =>
  isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)

set_option hygiene false in
local notation "𝐡U" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)

section One

variable (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (a : T.toGrp ⟶ 𝐋) (ha : IsSplitComponent a)
  [(rationalLeviSplitCenter I a).Normal]
  [MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
  [BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
  (μM : Measure (𝐌 ⧸ rationalLeviSplitCenter I a)) [μM.IsHaarMeasure]

include hKc hPK in
/-- **Remark VIII.1.3 (i) for one standard parabolic, from Theorem VIII.1.2** (Waldspurger,
printed p. 321): given the published statement `hVIII`, for every open subgroup `H` of `G(F)` the
set of orbits `O` of discrete series of `M_I(F)` modulo `A_{M_I}(F)` with `(O, P_I(F)) ∈ Θ^H` is
finite. -/
theorem finite_rationalInducedDiscreteSeriesFixedOrbits_of_statement
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (H : OpenSubgroup (rationalPoints G)) :
    (inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U (rationalLeviSplitCenter I a)
      (rationalLeviSplitCenter_le_center I a ha) μM
      (RationalPointFamily.leviRationalNormCharacters i ν I) H.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I a)
          (rationalLeviSplitCenter_le_center I a ha) μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite :=
  finite_rationalInducedDiscreteSeriesFixedOrbits hG hi hν I hKc hPK _ _ μM H
    (fun L hL => finite_discreteSeriesFixedOrbits_standardLevi I hVIII hG hi hν a ha μM L hL)

variable [μM.IsInvInvariant] {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **Remark VIII.1.3 (ii) for one standard parabolic, from Theorem VIII.1.2** (Waldspurger,
printed p. 321): given `hVIII`, for every `f ∈ C(G)` there is a finite set of orbits of discrete
series of `M_I(F)` modulo `A_{M_I}(F)` containing the orbit of every `π` with
`ψ_f[O, P_I] ≠ 0`. -/
theorem exists_finite_rationalFourierOrbitSection_ne_zero_of_statement
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (f : RationalSchwartzSpace hKc hPK ρ) :
    ∃ T : Set (DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I a)
        (rationalLeviSplitCenter_le_center I a ha) μM
        (RationalPointFamily.leviRationalNormCharacters i ν I)), T.Finite ∧
      ∀ (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
        (hsq : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I a)
          (rationalLeviSplitCenter_le_center I a ha) π.obj.representation μM)
        (hTA : ∀ A : UnitaryOrbitRepresentative
          (RationalPointFamily.leviRationalNormCharacters i ν I) π,
            IsRationalLeviTempered hKc ρ hM A.val.obj),
        rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π
            (rationalLeviSplitCenter I a) (rationalLeviSplitCenter_le_center I a ha) μM hsq hTA
            hsw f ≠ 0 →
          Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I a)
            (rationalLeviSplitCenter_le_center I a ha) μM π hsq) ∈ T :=
  exists_finite_rationalFourierOrbitSection_ne_zero hG hi hν I hKc hPK ρ hρ hKρ hM _ _ μM hsw
    (fun L hL => finite_discreteSeriesFixedOrbits_standardLevi I hVIII hG hi hν a ha μM L hL) f

end One

section All

variable {T : Finset (RationalPointFamily.SimpleRoot i ν) → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ I, (T I).toGrp ⟶ 𝐋) (ha : ∀ I, IsSplitComponent (a I))
  [∀ I, (rationalLeviSplitCenter I (a I)).Normal]
  [∀ I, MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I (a I))]
  (mu : ∀ I, Measure (𝐌 ⧸ rationalLeviSplitCenter I (a I))) [∀ I, (mu I).IsHaarMeasure]

/-- **Waldspurger's `Θ^H` for the standard parabolic subgroups** (VIII.1, printed p. 321): the
pairs `(I, O)`, `I` a set of simple roots and `O` an orbit of `Im X(M_I)` in `E₂(M_I)` (discrete
series of `M_I(F)` modulo `A_{M_I}(F)`, the image of the split component `a I`, for the Haar
measure `mu I`), such that `I_{P_I}^G E` has a nonzero `H`-fixed vector for some `(ω, E) ∈ O`. -/
def rationalThetaFixed (H : Subgroup (rationalPoints G)) :
    Set (Σ I : Finset (RationalPointFamily.SimpleRoot i ν),
      DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
        (RationalPointFamily.leviRationalNormCharacters i ν I)) :=
  Set.univ.sigma fun I => inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U (rationalLeviSplitCenter I (a I))
    (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
    (RationalPointFamily.leviRationalNormCharacters i ν I) H

theorem mem_rationalThetaFixed {H : Subgroup (rationalPoints G)}
    (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (O : DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
      (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
      (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    (⟨I, O⟩ : Σ J : Finset (RationalPointFamily.SimpleRoot i ν),
      DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter J (a J))
        (rationalLeviSplitCenter_le_center J (a J) (ha J)) (mu J)
        (RationalPointFamily.leviRationalNormCharacters i ν J)) ∈
        rationalThetaFixed hG hi hν a ha mu H ↔
      O ∈ inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U (rationalLeviSplitCenter I (a I))
        (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
        (RationalPointFamily.leviRationalNormCharacters i ν I) H := by
  simp [rationalThetaFixed, Set.mem_sigma_iff]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- The set of simple roots is finite (from the standard cocharacters, `standardCocharacter`). -/
theorem finite_simpleRoot : Finite (RationalPointFamily.SimpleRoot i ν) :=
  (finite_simpleRelativeRoots_of_standardCocharacter_exists i ν hi.isSplitSubtorus.1
    (fun J hJ => (standardCocharacter F G hG S i hi ν hν J hJ).1)).to_subtype

variable [∀ I, BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I (a I))]

include hKc hPK in
/-- **Remark VIII.1.3 (i) for the standard parabolic subgroups, from Theorem VIII.1.2**
(Waldspurger, printed p. 321): given the published statement `hVIII`, `Θ^H` restricted to the
standard parabolic subgroups is finite for every open subgroup `H` of `G(F)`. -/
theorem finite_rationalThetaFixed (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (H : OpenSubgroup (rationalPoints G)) :
    (rationalThetaFixed.{u, uV} hG hi hν a ha mu H.toSubgroup).Finite := by
  have := finite_simpleRoot hG hi hν
  exact Set.finite_univ.sigma fun I _ =>
    finite_rationalInducedDiscreteSeriesFixedOrbits_of_statement hG hi hν hKc hPK I (a I) (ha I)
      (mu I) hVIII H

variable [∀ I, (mu I).IsInvInvariant] {N : ℕ} [Nonempty (Fin N)]
  (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν), IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **Remark VIII.1.3 (ii) for the standard parabolic subgroups, from Theorem VIII.1.2**
(Waldspurger, printed p. 321): given the published statement `hVIII`, for every `f ∈ C(G)` there
is a finite set `T` of pairs `(I, O)` containing `(I, O_π)` for every `I` and every discrete series
`π` of `M_I(F)` modulo `A_{M_I}(F)` with `ψ_f[O_π, P_I] ≠ 0`. `T` is `Θ^L`
(`rationalThetaFixed`) for a compact open subgroup `L` under which `f` is right invariant. -/
theorem exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (f : RationalSchwartzSpace hKc hPK ρ) :
    ∃ T : Set (Σ I : Finset (RationalPointFamily.SimpleRoot i ν),
        DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I (a I))
          (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I)
          (RationalPointFamily.leviRationalNormCharacters i ν I)), T.Finite ∧
      ∀ (I : Finset (RationalPointFamily.SimpleRoot i ν))
        (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
        (hsq : IsSquareIntegrableModCentralSubgroup (rationalLeviSplitCenter I (a I))
          (rationalLeviSplitCenter_le_center I (a I) (ha I)) π.obj.representation (mu I))
        (hTA : ∀ A : UnitaryOrbitRepresentative
          (RationalPointFamily.leviRationalNormCharacters i ν I) π,
            IsRationalLeviTempered hKc ρ (hM I) A.val.obj),
        rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ (hM I) π
            (rationalLeviSplitCenter I (a I)) (rationalLeviSplitCenter_le_center I (a I) (ha I))
            (mu I) hsq hTA hsw f ≠ 0 →
          (⟨I, Quotient.mk _ (discreteSeriesClass (rationalLeviSplitCenter I (a I))
              (rationalLeviSplitCenter_le_center I (a I) (ha I)) (mu I) π hsq)⟩ :
            Σ J : Finset (RationalPointFamily.SimpleRoot i ν),
              DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter J (a J))
                (rationalLeviSplitCenter_le_center J (a J) (ha J)) (mu J)
                (RationalPointFamily.leviRationalNormCharacters i ν J)) ∈ T := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  obtain ⟨L, hL⟩ := Space.exists_rightInvariant f
  refine ⟨rationalThetaFixed hG hi hν a ha mu L.1.toSubgroup,
    finite_rationalThetaFixed hG hi hν hKc hPK a ha mu hVIII L.1, fun I π hsq hTA hne => ?_⟩
  rw [mem_rationalThetaFixed]
  exact mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero hG hi hν I
    hKc hPK ρ hρ hKρ (hM I) π _ _ (mu I) hsq hTA hsw f hL hne

end All

end Langlands.HarishChandraSchwartz
