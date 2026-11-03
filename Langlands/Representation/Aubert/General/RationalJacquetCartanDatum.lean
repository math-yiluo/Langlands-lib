import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Langlands.Representation.Aubert.General.JacquetCartanDatumStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-!
# Jacquet–Cartan data on the rational points of reductive groups

For a connected reductive group `G` over a nonarchimedean local field `F`, a
maximal split torus with a generic cocharacter, an apartment vertex with the
joint special compact data, and a finite lattice transversal of the torus
centralizer define a `StandardParabolicSystem` of `G(F)` (`rationalStandardParabolicSystem`),
given the standard cocharacter statement and the standard parabolic order
statement. Hence `G(F)` carries a Jacquet–Cartan datum
(`RationalPointsJacquetCartanDatumStatement`) under these two statements and the
joint special compact basis existence statement.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.Cartan Langlands.BruhatTits.SpecialCompact
open Langlands.Geometry.Building Langlands.Plancherel.RenardCartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily

section System

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- **The standard parabolic system of `G(F)`.** For a maximal split torus
`i : S → G` with a generic cocharacter `ν`, a vertex `x` whose subgroup
`K₀ = D.specialCompactSubgroup x` has the special compact properties, the
parabolic product family, the standard Levi compatibility and a simultaneous
basis, a represented torus centralizer `j : Z → G` with `s ≫ j = i`, and a
finite lattice transversal `F₀` of `Z(F)`: the simple roots of `(i, ν)`, the
standard parabolic, Levi and unipotent subgroups, the Iwasawa decomposition
`G = P_∅ K₀`, the Cartan decompositions `M_I = (K₀ ∩ M_I) Λ_I (K₀ ∩ M_I)` with
`Λ_I = rationalCartanSet i ν j s h F₀ I`, and their wall contraction. -/
def rationalStandardParabolicSystem (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    (hstd : StandardCocharacterStatement.{u}) (hord : StandardParabolicOrderStatement.{u})
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {h : Function.Bijective (restrictionEvaluation s)}
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hsc : SpecialCompactProperties F i ν (D.specialCompactSubgroup x))
    (hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν
      (D.specialCompactSubgroup x))
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    (hbasis : SimultaneousStandardBasisAt i ν (D.specialCompactSubgroup x))
    {F0 : Set (rationalPoints Z)} (hF0 : IsFiniteLatticeTransversal s F0) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    StandardParabolicSystem.{u, u} (RationalPoint F G.X) :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  { Δ := SimpleRoot i ν
    decEq := Classical.decEq _
    parabolic := parabolic i ν
    levi := levi i ν
    unipotent := unipotent i ν
    parabolic_mono := fun _ _ hIJ => parabolic_mono hG hi hν hord hIJ
    levi_mul_unipotent := fun I _ hp => exists_mul_of_mem_parabolic hG hi hν hstd I hp
    levi_le_normalizer := levi_le_normalizer i ν
    isClosed_levi := isClosed_levi_of_isNonarchimedeanLocalField i ν
    top := (exists_unipotent_eq_bot hG hi ν).choose
    unipotent_top := (exists_unipotent_eq_bot hG hi ν).choose_spec.2
    unipotent_descent := fun _ _ hJI _ hn =>
      exists_mul_of_mem_unipotent hG hi hν hstd hord hJI hn
    iwasawa := hasCompactCosetCover_parabolic_empty_of_specialCompactProperties i ν hsc hP
    cartanCompact := fun I =>
      ((D.specialCompactSubgroup x ⊓ levi i ν I : Subgroup (rationalPoints G)) :
        Set (rationalPoints G))
    cartanSet := rationalCartanSet i ν j s h F0
    isCompact_cartanCompact := isCompact_inf_levi ν hsc.2.1.1
    cartanCompact_subset := fun _ _ hm => hm.2
    countable_cartanSet := fun _ =>
      countable_image_tildeC0Plus hi.isSplitSubtorus.1 hF0.1 _
    cartanSet_subset := fun I => image_tildeC0Plus_subset_levi D x ν hcompat F0 _ I
    cartan := exists_cartan_levi D x ν hcompat hF0
    contraction := by
      have : Smooth G.X.hom := hG.smooth
      have : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
      have : Finite (SimpleRoot i ν) := finite_simpleRoot hG hi ν
      let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
      have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp ‹_›
      have hexists : ∀ I : Finset (SimpleRoot i ν),
          ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
        fun I => (hstd F G hG S i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1
      obtain ⟨-, -, -, -, -, -, -, hlat⟩ := hcompat ∅ (Set.empty_subset _)
      exact (isCartanLatticeModel_rational i ν j s h hi hfinite hexists hrep hsj hlat.1
        hbasis hF0.1).hasWallContraction }

end System

/-- **Jacquet–Cartan data on `G(F)`, conditionally.** The standard cocharacter
statement, the standard parabolic order statement and the joint special compact
basis existence statement imply `RationalPointsJacquetCartanDatumStatement`. -/
theorem rationalPointsJacquetCartanDatum_of
    (hjoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hstd : StandardCocharacterStatement.{u})
    (hord : StandardParabolicOrderStatement.{u}) :
    RationalPointsJacquetCartanDatumStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  obtain ⟨S, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨D, x, Z, j, s, -, hrep, hsj, h, -, hsc, -, hP, -, -, hcompat, hbasis⟩ :=
    hjoint F G hG S i hi ν hν
  obtain ⟨F0, hF0⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  exact (rationalStandardParabolicSystem hG hi hν hstd hord D x hrep hsj hsc hP hcompat
    hbasis hF0).nonempty_jacquetCartanDatum

end Langlands.Aubert.General
