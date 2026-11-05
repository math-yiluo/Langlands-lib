import Langlands.Group.TitsSystemBruhat
import Langlands.GroupScheme.Rational.StandardParabolicPointsStatement
import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Aubert.General.RationalLeviWeylComparison
import Langlands.Group.RelativeWeylIndexingTargets

/-! # Rational double-coset realization for corrected supports -/

noncomputable section

universe u v

namespace Langlands.Group

/-- A representative-preserving double-coset equivalence gives a cover by
actual normalizer representatives. -/
theorem exists_doubleCoset_rep_of_equiv
    {G : Type u} [Group G] {W : Type v} [Group W]
    {N P Q : Subgroup G} {H K : Subgroup W} {π : N →* W}
    (hπ : Function.Surjective π)
    (e : DoubleCoset.Quotient (H : Set W) K ≃
      DoubleCoset.Quotient (P : Set G) Q)
    (he : ∀ n : N, e (DoubleCoset.mk H K (π n)) = DoubleCoset.mk P Q (n : G))
    (g : G) : ∃ n : N, ∃ p ∈ P, ∃ q ∈ Q, g = p * (n : G) * q := by
  obtain ⟨c, hc⟩ := e.surjective (DoubleCoset.mk P Q g)
  induction c using Quotient.inductionOn with
  | h w =>
    obtain ⟨n, rfl⟩ := hπ w
    rw [he n] at hc
    obtain ⟨p, hp, q, hq, hg⟩ := DoubleCoset.eq.mp hc
    exact ⟨n, p, hp, q, hq, hg⟩

/-- The parabolic equivalence of a Tits system reflects and preserves equality
of the double cosets of every pair of normalizer representatives. -/
theorem IsTitsSystem.doubleCoset_mk_eq_iff
    {G : Type u} [Group G] {W : Type v} [Group W]
    {B N : Subgroup G} {π : N →* W} {S : Set W}
    (h : IsTitsSystem B N π S) {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S)
    {H K : Subgroup W} (hH : H = Subgroup.closure X) (hK : K = Subgroup.closure Y)
    {P Q : Subgroup G}
    (hP : (P : Set G) = TitsSystem.standardParabolic B π X)
    (hQ : (Q : Set G) = TitsSystem.standardParabolic B π Y) (n n' : N) :
    DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q (n' : G) ↔
      DoubleCoset.mk H K (π n) = DoubleCoset.mk H K (π n') := by
  obtain ⟨e, he⟩ := h.exists_doubleCoset_equiv hX hY hH hK hP hQ
  rw [← he n, ← he n']
  exact e.injective.eq_iff

/-- Multiplicative equivalences preserve double-coset equality after mapping
both subgroups. -/
theorem doubleCoset_mk_eq_map_iff
    {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) (H K : Subgroup A) (a b : A) :
    DoubleCoset.mk (H.map e.toMonoidHom) (K.map e.toMonoidHom) (e a) =
        DoubleCoset.mk (H.map e.toMonoidHom) (K.map e.toMonoidHom) (e b) ↔
      DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨x, ⟨h, hh, rfl⟩, y, ⟨k, hk, rfl⟩, hab⟩
    change e b = e h * e a * e k at hab
    exact ⟨h, hh, k, hk, e.injective (by simpa only [map_mul] using hab)⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact ⟨e h, ⟨h, hh, rfl⟩, e k, ⟨k, hk, rfl⟩, by simp only [map_mul]⟩

end Langlands.Group

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The equivalence supplied by the standard-parabolic points statement, at
exact finite subsets of the actual simple roots. -/
def standardParabolicDoubleCosetEquiv
    (hPoints : StandardParabolicPointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J I : Finset (SimpleRoot i ν)) :
    DoubleCoset.Quotient (schemeStandardWeyl i ν J : Set (relativeWeylGroup i))
        (schemeStandardWeyl i ν I) ≃
      DoubleCoset.Quotient (parabolic i ν J : Set (RationalPoint k G.X))
        (parabolic i ν I) :=
  Classical.choose ((hPoints k G hG T i hi ν hν).2.2.2
    (rootSet i ν J) (rootSet i ν I) (rootSet_subset i ν J) (rootSet_subset i ν I))

@[simp] theorem standardParabolicDoubleCosetEquiv_mk
    (hPoints : StandardParabolicPointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J I : Finset (SimpleRoot i ν))
    (n : normalizerPoints i) :
    standardParabolicDoubleCosetEquiv i ν hPoints hG hi hν J I
      (DoubleCoset.mk (schemeStandardWeyl i ν J) (schemeStandardWeyl i ν I)
        (QuotientGroup.mk n)) =
      DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) (n : RationalPoint k G.X) :=
  Classical.choose_spec ((hPoints k G hG T i hi ν hν).2.2.2
    (rootSet i ν J) (rootSet i ν I) (rootSet_subset i ν J) (rootSet_subset i ν I)) n

/-- Clause four alone supplies the Bruhat cover required by the generic support
comparison, with no endpoint or separate Bruhat statement as a premise. -/
theorem isBruhatCover_of_standardParabolicPoints
    (hPoints : StandardParabolicPointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    CorrectedFiltration.IsBruhatCover (torusPoints i) (parabolic i ν ∅)
      (parabolic i ν I) := by
  intro g
  obtain ⟨n, p, hp, q, hq, hg⟩ := Group.exists_doubleCoset_rep_of_equiv
    (QuotientGroup.mk'_surjective ((centralizerPoints i).subgroupOf (normalizerPoints i)))
    (standardParabolicDoubleCosetEquiv i ν hPoints hG hi hν ∅ I)
    (standardParabolicDoubleCosetEquiv_mk i ν hPoints hG hi hν ∅ I) g
  exact ⟨⟨n, normalizerPoints_le_pointNormalizer i n.property⟩, p, hp, q, hq, hg⟩

/-- The exact actual normalizer comparison, using full centralizers on both
sides and the supplied standard-Levi Weyl identification. -/
theorem parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints
    (hPoints : StandardParabolicPointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM)
    (hLevi : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (J I : Finset (SimpleRoot i ν))
    (n n' : Group.RelativeWeyl.normalizer (torusPoints i)) :
    DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) (n : RationalPoint k G.X) =
        DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) (n' : RationalPoint k G.X) ↔
      DoubleCoset.mk (standardSubgroup cs J) (standardSubgroup cs I)
          (QuotientGroup.mk n : Weyl i) =
        DoubleCoset.mk (standardSubgroup cs J) (standardSubgroup cs I)
          (QuotientGroup.mk n' : Weyl i) := by
  let e := standardParabolicDoubleCosetEquiv i ν hPoints hG hi hν J I
  let m := (normalizerEquiv i hN).symm n
  let m' := (normalizerEquiv i hN).symm n'
  have he (a : normalizerPoints i) :
      e (DoubleCoset.mk (schemeStandardWeyl i ν J) (schemeStandardWeyl i ν I)
        (QuotientGroup.mk a)) =
        DoubleCoset.mk (parabolic i ν J) (parabolic i ν I) (a : RationalPoint k G.X) :=
    standardParabolicDoubleCosetEquiv_mk i ν hPoints hG hi hν J I a
  have hJ : (schemeStandardWeyl i ν J).map (weylEquiv i hN hZ).toMonoidHom =
      standardSubgroup cs J :=
    (weylEquiv_map_schemeStandardWeyl i ν hN hZ J).trans (hLevi J)
  have hI : (schemeStandardWeyl i ν I).map (weylEquiv i hN hZ).toMonoidHom =
      standardSubgroup cs I :=
    (weylEquiv_map_schemeStandardWeyl i ν hN hZ I).trans (hLevi I)
  have hmap := Group.doubleCoset_mk_eq_map_iff (weylEquiv i hN hZ)
    (schemeStandardWeyl i ν J) (schemeStandardWeyl i ν I)
    (QuotientGroup.mk m) (QuotientGroup.mk m')
  rw [hJ, hI, weylEquiv_mk, weylEquiv_mk,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hmap
  have hm : (m : RationalPoint k G.X) = n := by
    simpa only [normalizerEquiv_apply] using
      congrArg (fun a : Group.RelativeWeyl.normalizer (torusPoints i) =>
        (a : RationalPoint k G.X)) ((normalizerEquiv i hN).apply_symm_apply n)
  have hm' : (m' : RationalPoint k G.X) = n' := by
    simpa only [normalizerEquiv_apply] using
      congrArg (fun a : Group.RelativeWeyl.normalizer (torusPoints i) =>
        (a : RationalPoint k G.X)) ((normalizerEquiv i hN).apply_symm_apply n')
  have hem := he m
  have hem' := he m'
  rw [hm] at hem
  rw [hm'] at hem'
  rw [hmap, ← hem, ← hem']
  exact e.injective.eq_iff

end Langlands.Aubert.General.RationalPointFamily
