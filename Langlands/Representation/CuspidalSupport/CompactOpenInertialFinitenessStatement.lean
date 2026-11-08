import Langlands.Representation.CuspidalSupport.BernsteinBlock

/-! # Compact open subgroups meet finitely many Bernstein components (Renard VI.10.6)

For a compact open subgroup `K` of `G(F)`, only finitely many inertial classes are the
inertial support of an irreducible representation with nonzero `K`-fixed vectors, and the
set of cuspidal supports of such representations is a union of whole inertial classes.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.6, Theorem, "more precisely" part, for the actual standard cuspidal data
of a standard family: for every compact open subgroup `K` of `G(F)`,

* the set `B(G)_K` of inertial classes `s` such that some irreducible smooth representation
  with inertial support `s` has a nonzero `K`-fixed vector is finite; and
* `Ω(G)_K` is a union of inertial classes: if one cuspidal datum `a` supports an irreducible
  representation with a nonzero `K`-fixed vector, then so does every datum `b` inertially
  related to `a`. -/
def CompactOpenInertialFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
      let HasFixed : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) → Prop :=
        fun π => ∃ x : π, x ≠ 0 ∧ ∀ k ∈ K, π.representation k x = x
      {s : BernsteinInertialClass.{uF, max uF uV} i ν family |
          ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
            IsBernsteinInertialSupport i ν family s π ∧ HasFixed π}.Finite ∧
        ∀ a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
          IsBernsteinInertiaRelated i ν family a b →
          (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
              IsBernsteinCuspidalSupport i ν family a π ∧ HasFixed π) →
            ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
              IsBernsteinCuspidalSupport i ν family b π ∧ HasFixed π

end Langlands.CuspidalSupport
