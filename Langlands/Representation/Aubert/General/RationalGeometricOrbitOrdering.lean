import Langlands.Representation.Aubert.General.RationalCorrectedSupportComparison
import Langlands.Representation.Aubert.General.RationalGeometricK0Target
import Langlands.Group.RelativeWeylMinimalUniqueProof
import Langlands.Group.RelativeWeylIndexingInversion
import Langlands.Representation.Geometric.OrbitRepresentatives
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering

/-!
# Ordered parabolic orbits indexed by minimal representatives

For the actual standard rational-point families, the standard-parabolic points
statement identifies `P_J \ G / P_I` with `W_J \ W / W_I`. Then the inverses of
every lift of the minimal representatives of `W_I \ W / W_J` meet every actual
parabolic double coset exactly once. Any ordered orbit cover can therefore be
re-indexed by these lifts.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

section DoubleCosets

/-- Mathlib double-coset equality is membership in the intrinsic double coset. -/
theorem doubleCoset_mk_eq_iff_mem {B : Type*} {W : Type*} [Group W] {CM : CoxeterMatrix B}
    (cs : CoxeterSystem CM W) (J I : Finset B) (a b : W) :
    DoubleCoset.mk (standardSubgroup cs J) (standardSubgroup cs I) a =
        DoubleCoset.mk (standardSubgroup cs J) (standardSubgroup cs I) b ↔
      b ∈ doubleCoset cs J I a := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩

end DoubleCosets

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

variable (hPoints : StandardParabolicPointsStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLevi : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
  [Fintype (Weyl i)]

include hPoints hG hi hν hN hZ hLevi in
/-- The inverses of the lifts of the minimal representatives of `W_I \ W / W_J`
meet every actual double coset `P_J \ G / P_I` exactly once. -/
theorem doubleCoset_inv_lift_bijective (I J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) :
    Function.Bijective (fun a : {w : Weyl i // w ∈ minimalReps cs I J} =>
      (DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
        ((lift a.val : RationalPoint k G.X))⁻¹ :
          DoubleCoset.Quotient (parabolic i ν J : Set (RationalPoint k G.X))
            (parabolic i ν I))) := by
  have hmk : ∀ a : Weyl i,
      (QuotientGroup.mk ((lift a)⁻¹) : Weyl i) = a⁻¹ := by
    intro a
    rw [QuotientGroup.mk_inv, hlift]
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
        (((lift a)⁻¹ : Group.RelativeWeyl.normalizer (torusPoints i)) : RationalPoint k G.X) =
      DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
        (((lift b)⁻¹ : Group.RelativeWeyl.normalizer (torusPoints i)) : RationalPoint k G.X) := by
      simpa only [Subgroup.coe_inv] using hab
    rw [parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints i ν hPoints hG hi hν
      hN hZ cs hLevi J I, hmk, hmk, doubleCoset_mk_eq_iff_mem] at hab'
    have hamin := isMinimal_inv cs ((mem_minimalReps cs I J a).mp ha)
    have hbmin := isMinimal_inv cs ((mem_minimalReps cs I J b).mp hb)
    have heq := minimalRepresentativeUnique_proof cs J I a⁻¹ a⁻¹ b⁻¹
      (mem_doubleCoset_self cs J I a⁻¹) hab' hamin hbmin
    exact Subtype.ext (inv_injective heq)
  · intro x
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨n₀, p, hp, q, hq, hg⟩ := Group.exists_doubleCoset_rep_of_equiv
        (QuotientGroup.mk'_surjective ((centralizerPoints i).subgroupOf (normalizerPoints i)))
        (standardParabolicDoubleCosetEquiv i ν hPoints hG hi hν J I)
        (standardParabolicDoubleCosetEquiv_mk i ν hPoints hG hi hν J I) g
      let n : Group.RelativeWeyl.normalizer (torusPoints i) :=
        ⟨n₀, normalizerPoints_le_pointNormalizer i n₀.property⟩
      let y : Weyl i := QuotientGroup.mk n
      obtain ⟨w, hw, hwmin⟩ := exists_minimal_in_doubleCoset cs I J y⁻¹
      refine ⟨⟨w, (mem_minimalReps cs I J w).mpr hwmin⟩, ?_⟩
      have hng : DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
          (n : RationalPoint k G.X) =
        DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) g :=
        DoubleCoset.eq.mpr ⟨p, hp, q, hq, hg⟩
      change DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
          ((lift w : RationalPoint k G.X))⁻¹ =
        DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) g
      rw [← hng]
      have hw' : DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
          (((lift w)⁻¹ : Group.RelativeWeyl.normalizer (torusPoints i)) : RationalPoint k G.X) =
        DoubleCoset.mk (parabolic i ν J) (parabolic i ν I)
          (n : RationalPoint k G.X) := by
        rw [parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints i ν hPoints hG hi hν
          hN hZ cs hLevi J I, hmk, doubleCoset_mk_eq_iff_mem]
        have h1 := inv_mem_doubleCoset cs hw
        rw [inv_inv] at h1
        obtain ⟨x, hx, z, hz, hxz⟩ := h1
        refine ⟨x⁻¹, (standardSubgroup cs J).inv_mem hx, z⁻¹,
          (standardSubgroup cs I).inv_mem hz, ?_⟩
        rw [hxz]
        group
        rfl
      simpa only [Subgroup.coe_inv] using hw'

include hPoints hG hi hν hN hZ hLevi in
/-- The actual parabolic double-coset space `P_J \ G / P_I` is finite. -/
theorem finite_parabolicDoubleCoset (I J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) :
    Finite (DoubleCoset.Quotient (parabolic i ν J : Set (RationalPoint k G.X))
      (parabolic i ν I)) :=
  Finite.of_surjective _
    (doubleCoset_inv_lift_bijective i ν hPoints hG hi hν hN hZ cs hLevi I J lift hlift).2

section Ordering

variable [TopologicalSpace (RationalPoint k G.X)] [NonarchimedeanGroup (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [SigmaCompactSpace (RationalPoint k G.X)]

include hPoints hG hi hν hN hZ hLevi in
/-- An ordered orbit cover of `P_J \ G` by `P_I`-orbits whose representatives
are exactly the lifts of the minimal representatives of `W_I \ W / W_J`,
each occurring once. -/
noncomputable def minimalOrbitOrdering (I J : Finset (SimpleRoot i ν))
    (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
    (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) :
    Σ m : ℕ, Σ e : Fin m ≃ {w : Weyl i // w ∈ minimalReps cs I J},
      {t : Geometric.OrderedDoubleCosets (parabolic i ν J) (parabolic i ν I) m //
        ∀ q, t.representative q = ((lift (e q).val : Group.RelativeWeyl.normalizer
          (torusPoints i)) : RationalPoint k G.X)} :=
  Classical.choice (by
    obtain ⟨m, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering (RationalPoint k G.X)
      (parabolic i ν J) (parabolic i ν I) hPJ hPI
      (finite_parabolicDoubleCoset i ν hPoints hG hi hν hN hZ cs hLevi I J lift hlift)
    exact ⟨⟨m, s.classifiedRepresentatives
      (fun a : {w : Weyl i // w ∈ minimalReps cs I J} =>
        ((lift a.val : Group.RelativeWeyl.normalizer (torusPoints i)) : RationalPoint k G.X))
      (doubleCoset_inv_lift_bijective i ν hPoints hG hi hν hN hZ cs hLevi I J lift hlift)⟩⟩)

end Ordering

end Langlands.Aubert.General.RationalPointFamily
