import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociation
import Mathlib.GroupTheory.Coset.Card

/-! # Weyl orbit stabilizer for an actual semistandard spectral index -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

variable {a ha mu}

/-- The Weyl group inside the literal Levi fixes its discrete-series constituent classes. -/
theorem WeylTransports.self_of_mem {t : Θ} {w : relativeWeylGroup i}
    (hw : w ∈ semistandardLeviRelativeWeylSubgroup i t.1.toLevi) :
    WeylTransports a ha mu w t t := by
  obtain ⟨n, hn, rfl⟩ := (mem_semistandardLeviRelativeWeylSubgroup i t.1.toLevi w).mp hw
  exact ⟨n, rfl, OrbitConjugates.self_of_mem hn⟩

/-- The orbit transport condition is constant on left target-Weyl classes. -/
theorem weylTransports_mul_left_iff {t t' : Θ} {v w : relativeWeylGroup i}
    (hv : v ∈ semistandardLeviRelativeWeylSubgroup i t'.1.toLevi) :
    WeylTransports a ha mu (v * w) t t' ↔ WeylTransports a ha mu w t t' := by
  constructor
  · intro h
    have hinv := (semistandardLeviRelativeWeylSubgroup i t'.1.toLevi).inv_mem hv
    simpa only [inv_mul_cancel_left] using h.mul (WeylTransports.self_of_mem hinv)
  · exact fun h => h.mul (WeylTransports.self_of_mem hv)

variable (a ha mu)

/-- Actual spectral transport tested on the source's left target-Weyl quotient. -/
def quotientWeylTransports (t t' : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    SemistandardWeylTransporterQuotient i t.1.toLevi t'.1.toLevi hM → Prop :=
  Quotient.lift (fun w : semistandardWeylTransporterSet i t.1.toLevi t'.1.toLevi hM =>
    WeylTransports a ha mu w.val t t') (by
      intro w v h
      have hv : v.val * w.val⁻¹ ∈ semistandardLeviRelativeWeylSubgroup i t'.1.toLevi :=
        QuotientGroup.rightRel_apply.mp h
      apply propext
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using (weylTransports_mul_left_iff
        (t := t) (t' := t') (w := w.val) hv).symm)

@[simp] theorem quotientWeylTransports_mk (t t' : Θ) (hM : torusCentralizer i ≤ t.1.levi)
    (w : semistandardWeylTransporterSet i t.1.toLevi t'.1.toLevi hM) :
    quotientWeylTransports a ha mu t t' hM (Quotient.mk _ w) ↔
      WeylTransports a ha mu w.val t t' := Iff.rfl

/-- Waldspurger's `Stab(O,M)` as a subtype of the literal `W(G|M)`. -/
abbrev WeylOrbitStabilizer (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) : Type u :=
  {w : SemistandardWeylTransporterQuotient i t.1.toLevi t.1.toLevi hM //
    quotientWeylTransports a ha mu t t hM w}

/-- The lift of the stabilizer to the full relative Weyl group. -/
def weylOrbitStabilizerSubgroup (t : Θ) : Subgroup (relativeWeylGroup i) where
  carrier := {w | WeylTransports a ha mu w t t}
  one_mem' := WeylTransports.one t
  mul_mem' hw hv := hv.mul hw
  inv_mem' hw := hw.inv

theorem leviWeyl_le_weylOrbitStabilizerSubgroup (t : Θ) :
    semistandardLeviRelativeWeylSubgroup i t.1.toLevi ≤
      weylOrbitStabilizerSubgroup a ha mu t :=
  fun _ hw => WeylTransports.self_of_mem hw

variable {a ha mu}

private def ofWeyl (t : Θ) (hM : torusCentralizer i ≤ t.1.levi)
    (w : weylOrbitStabilizerSubgroup a ha mu t) : WeylOrbitStabilizer a ha mu t hM :=
  ⟨Quotient.mk _ ⟨w.val, le_of_eq (WeylTransports.levi_eq w.property hM)⟩, w.property⟩

private theorem ofWeyl_eq_iff (t : Θ) (hM : torusCentralizer i ≤ t.1.levi)
    (w v : weylOrbitStabilizerSubgroup a ha mu t) :
    ofWeyl t hM w = ofWeyl t hM v ↔
      v.val * w.val⁻¹ ∈ semistandardLeviRelativeWeylSubgroup i t.1.toLevi := by
  unfold ofWeyl
  rw [Subtype.ext_iff, Quotient.eq]
  exact QuotientGroup.rightRel_apply

private theorem ofWeyl_surjective (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    Function.Surjective (ofWeyl t hM) := by
  intro q
  have hq : WeylTransports a ha mu q.val.out.val t t :=
    (quotientWeylTransports_mk a ha mu t t hM q.val.out).mp
      (by rw [Quotient.out_eq]; exact q.property)
  exact ⟨⟨q.val.out.val, hq⟩, Subtype.ext (Quotient.out_eq q.val)⟩

variable (a ha mu)

instance (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) [Finite (relativeWeylGroup i)] :
    Finite (WeylOrbitStabilizer a ha mu t hM) := inferInstance

instance (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    Nonempty (WeylOrbitStabilizer a ha mu t hM) :=
  ⟨ofWeyl t hM 1⟩

/-- The subgroup of all stabilizing Weyl elements modulo left multiplication by `W^M`. -/
def weylOrbitStabilizerEquiv (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    Quotient (QuotientGroup.rightRel
      ((semistandardLeviRelativeWeylSubgroup i t.1.toLevi).subgroupOf
        (weylOrbitStabilizerSubgroup a ha mu t))) ≃
          WeylOrbitStabilizer a ha mu t hM := by
  let W := (semistandardLeviRelativeWeylSubgroup i t.1.toLevi).subgroupOf
    (weylOrbitStabilizerSubgroup a ha mu t)
  let f := Quotient.lift (s := QuotientGroup.rightRel W) (ofWeyl t hM) fun w v h =>
    (ofWeyl_eq_iff t hM w v).mpr ((QuotientGroup.rightRel_apply (s := W)).mp h)
  apply Equiv.ofBijective f
  refine ⟨?_, ?_⟩
  · intro x y
    induction x using Quotient.inductionOn with
    | h w =>
      induction y using Quotient.inductionOn with
      | h v =>
        intro hv
        exact Quotient.sound ((QuotientGroup.rightRel_apply (s := W)).mpr
          ((ofWeyl_eq_iff t hM w v).mp hv))
  · intro q
    obtain ⟨w, hw⟩ := ofWeyl_surjective t hM q
    exact ⟨Quotient.mk _ w, hw⟩

/-- The source denominator counts genuine Weyl classes and is positive. -/
theorem card_weylOrbitStabilizer_pos (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    0 < Nat.card (WeylOrbitStabilizer a ha mu t hM) := by
  have := hG.finite_relativeWeylGroup i hi
  exact Nat.card_pos

/-- Each stabilizer class consists of `|W^M|` full Weyl elements. -/
theorem card_weylOrbitStabilizerSubgroup (t : Θ) (hM : torusCentralizer i ≤ t.1.levi) :
    Nat.card (weylOrbitStabilizerSubgroup a ha mu t) =
      Nat.card (WeylOrbitStabilizer a ha mu t hM) *
        Nat.card (semistandardLeviRelativeWeylSubgroup i t.1.toLevi) := by
  let W := (semistandardLeviRelativeWeylSubgroup i t.1.toLevi).subgroupOf
    (weylOrbitStabilizerSubgroup a ha mu t)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W]
  congr 1
  · exact Nat.card_congr ((QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := W)).symm.trans
      (weylOrbitStabilizerEquiv a ha mu t hM))
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (leviWeyl_le_weylOrbitStabilizerSubgroup a ha mu t)).toEquiv

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
