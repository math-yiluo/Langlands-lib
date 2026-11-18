import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.GroupScheme.Rational.SemistandardWeylTransporters
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.Representation.CuspidalSupport.NormKernelSummandPullback

/-! # Association and finite saturation of actual semistandard spectral indices -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

section SmoothDual

variable {X Y Z : Type u} [Group X] [Group Y] [Group Z]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private theorem pullback_refl :
    SmoothDualClass.pullback.{u, u, uV} (ContinuousMulEquiv.refl X) = id := by
  funext w
  induction w using Quotient.inductionOn with
  | h pi =>
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
      (SmoothRep.mkIso (equivOfRepresentationEq rfl))⟩

private theorem pullback_trans (e : X ≃ₜ* Y) (f : Y ≃ₜ* Z) :
    SmoothDualClass.pullback.{u, u, uV} e ∘ SmoothDualClass.pullback f =
      SmoothDualClass.pullback (e.trans f) := by
  funext w
  induction w using Quotient.inductionOn with
  | h pi =>
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
      (SmoothRep.mkIso (equivOfRepresentationEq rfl))⟩

private theorem pullback_inner [IsTopologicalGroup X] (g : X) :
    SmoothDualClass.pullback.{u, u, uV} (CuspidalSupport.inverseConjugation g) = id := by
  funext w
  induction w using Quotient.inductionOn with
  | h pi =>
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
      (CuspidalSupport.pullbackInverseConjugationIso g pi.obj)⟩

end SmoothDual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

section LeviConjugation

/-- The forward rational conjugation of the two literal Levis on all test schemes. -/
def ConjugatesLevi (g : rationalPoints G) (p q : SemistandardSpectralIndex i) : Prop :=
  p.levi = q.levi.comap (G.innerIso g).hom

variable {g h : rationalPoints G} {p q r : SemistandardSpectralIndex i}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem ConjugatesLevi.inv (hc : ConjugatesLevi g p q) : ConjugatesLevi g⁻¹ q p := by
  change q.levi = p.levi.comap (G.innerIso g⁻¹).hom
  rw [innerIso_inv_hom]
  exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp hc).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem ConjugatesLevi.mul (hg : ConjugatesLevi g p q) (hh : ConjugatesLevi h q r) :
    ConjugatesLevi (h * g) p r := by
  change p.levi = q.levi.comap (G.innerIso g).hom at hg
  change q.levi = r.levi.comap (G.innerIso h).hom at hh
  change p.levi = r.levi.comap (G.innerIso (h * g)).hom
  rw [innerIso_mul_hom, SubgroupFunctor.comap_comp, ← hh, ← hg]

/-- The actual group homeomorphism `m ↦ g m g⁻¹` induced by all-test conjugation. -/
def leviPointConjugation (hc : ConjugatesLevi g p q) : levi p ≃ₜ* levi q := by
  apply GroupTransport.subgroupEquiv (rationalPointsConjHomeomorph G g)
  have hp := congrArg SubgroupFunctor.rationalPoints hc
  rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom] at hp
  intro x
  exact Iff.of_eq (congrArg (fun L : Subgroup (rationalPoints G) => x ∈ L) hp)

@[simp] theorem leviPointConjugation_apply (hc : ConjugatesLevi g p q) (x : levi p) :
    (leviPointConjugation hc x : rationalPoints G) = g * x * g⁻¹ := rfl

@[simp] theorem leviPointConjugation_symm_apply (hc : ConjugatesLevi g p q) (x : levi q) :
    ((leviPointConjugation hc).symm x : rationalPoints G) = g⁻¹ * x * g := rfl

private theorem leviPointConjugation_inv (hc : ConjugatesLevi g p q) :
    leviPointConjugation hc.inv = (leviPointConjugation hc).symm := by
  ext x
  simp

private theorem leviPointConjugation_mul (hg : ConjugatesLevi g p q)
    (hh : ConjugatesLevi h q r) :
    (leviPointConjugation (hg.mul hh)).symm =
      (leviPointConjugation hh).symm.trans (leviPointConjugation hg).symm := by
  ext x
  simp only [ContinuousMulEquiv.trans_apply, leviPointConjugation_symm_apply, mul_inv_rev]
  group

end LeviConjugation

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

/-- The actual smooth-dual classes belonging to the orbit of a full index. -/
def orbitConstituents (t : Θ) : Set (SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi t.1)) :=
  {w | ∃ d : DiscreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1),
    d.val = w ∧ (Quotient.mk _ d : OrbitClass (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1)) = t.2}

/-- At a fixed parabolic the actual constituent set determines the orbit. -/
theorem orbitClass_eq_of_constituents_eq (p : SemistandardSpectralIndex i)
    {O O' : OrbitClass.{u, uV} (chosenLeviModel p) (a p) (ha p) (mu p)}
    (h : orbitConstituents a ha mu (⟨p, O⟩ : Θ) =
      orbitConstituents a ha mu (⟨p, O'⟩ : Θ)) : O = O' := by
  have hw : O.out.val ∈ orbitConstituents a ha mu ⟨p, O⟩ :=
    ⟨O.out, rfl, Quotient.out_eq O⟩
  rw [h] at hw
  obtain ⟨d, he, hd⟩ := hw
  rw [Subtype.ext he, Quotient.out_eq O] at hd
  exact hd

/-- A rational normalizer lift carries the actual Levi and the full constituent orbit.
On a constituent `ω`, transport acts by `ω ∘ Int(g)⁻¹`. -/
def OrbitConjugates (g : rationalPoints G) (t t' : Θ) : Prop :=
  ∃ hc : ConjugatesLevi g t.1 t'.1,
    SmoothDualClass.pullback (leviPointConjugation hc).symm '' orbitConstituents a ha mu t =
      orbitConstituents a ha mu t'

variable {a ha mu}

/-- Conjugation by a point of the literal Levi preserves every constituent class. -/
theorem OrbitConjugates.self_of_mem {g : rationalPoints G} {t : Θ}
    (hg : g ∈ levi t.1) : OrbitConjugates a ha mu g t t := by
  let hg' : levi t.1 := ⟨g, hg⟩
  let hc : ConjugatesLevi g t.1 t.1 :=
    (t.1.levi.comap_innerIso_hom_eq_of_mem hg).symm
  have he : (leviPointConjugation hc).symm = CuspidalSupport.inverseConjugation hg' := by
    ext x
    rfl
  exact ⟨hc, by rw [he, pullback_inner, Set.image_id]⟩

private theorem OrbitConjugates.inv {g : rationalPoints G} {t t' : Θ}
    (h : OrbitConjugates a ha mu g t t') : OrbitConjugates a ha mu g⁻¹ t' t := by
  obtain ⟨hc, ho⟩ := h
  refine ⟨hc.inv, ?_⟩
  rw [leviPointConjugation_inv, ContinuousMulEquiv.symm_symm, ← ho, Set.image_image]
  change (SmoothDualClass.pullback (leviPointConjugation hc) ∘
    SmoothDualClass.pullback (leviPointConjugation hc).symm) '' orbitConstituents a ha mu t = _
  rw [pullback_trans, ContinuousMulEquiv.self_trans_symm, pullback_refl, Set.image_id]

private theorem OrbitConjugates.mul {g h : rationalPoints G} {t t' t'' : Θ}
    (hg : OrbitConjugates a ha mu g t t') (hh : OrbitConjugates a ha mu h t' t'') :
    OrbitConjugates a ha mu (h * g) t t'' := by
  obtain ⟨hgL, hgO⟩ := hg
  obtain ⟨hhL, hhO⟩ := hh
  refine ⟨hgL.mul hhL, ?_⟩
  rw [leviPointConjugation_mul hgL hhL, ← pullback_trans]
  calc
    _ = SmoothDualClass.pullback (leviPointConjugation hhL).symm ''
        (SmoothDualClass.pullback (leviPointConjugation hgL).symm ''
          orbitConstituents a ha mu t) := (Set.image_image _ _ _).symm
    _ = orbitConstituents a ha mu t'' := by rw [hgO, hhO]

variable (a ha mu)

/-- The exact transport relation at an element of the actual relative Weyl quotient. -/
def WeylTransports (w : relativeWeylGroup i) (t t' : Θ) : Prop :=
  ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
    OrbitConjugates a ha mu (n : rationalPoints G) t t'

variable {a ha mu}

private theorem orbitConjugates_of_same_weyl {t t' : Θ} (hM : torusCentralizer i ≤ t.1.levi)
    {n m : normalizerPoints i} (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m)
    (hn : OrbitConjugates a ha mu (n : rationalPoints G) t t') :
    OrbitConjugates a ha mu (m : rationalPoints G) t t' := by
  have hz : (n : rationalPoints G)⁻¹ * (m : rationalPoints G) ∈ levi t.1 := by
    apply hM (Over.mk (𝟙 _))
    change (n : rationalPoints G)⁻¹ * (m : rationalPoints G) ∈
      (torusCentralizer i).carrier (Over.mk (𝟙 _))
    rw [torusCentralizer_carrier_base]
    exact (QuotientGroup.eq.mp hnm : n⁻¹ * m ∈
      (centralizerPoints i).subgroupOf (normalizerPoints i))
  have hzO : OrbitConjugates a ha mu ((n : rationalPoints G)⁻¹ * (m : rationalPoints G)) t t :=
    OrbitConjugates.self_of_mem hz
  simpa only [mul_inv_cancel_left] using hzO.mul hn

/-- When the actual Levi contains the full centralizer, every lift gives the same transport relation. -/
theorem weylTransports_mk_iff {t t' : Θ} (hM : torusCentralizer i ≤ t.1.levi)
    (n : normalizerPoints i) :
    WeylTransports a ha mu (QuotientGroup.mk n) t t' ↔
      OrbitConjugates a ha mu (n : rationalPoints G) t t' := by
  refine ⟨?_, fun hn => ⟨n, rfl, hn⟩⟩
  rintro ⟨m, hmn, hm⟩
  exact orbitConjugates_of_same_weyl hM hmn hm

/-- Spectral transport entails the all-test equality of the Levi functors. -/
theorem WeylTransports.levi_eq {t t' : Θ} {w : relativeWeylGroup i}
    (hw : WeylTransports a ha mu w t t') (hM : torusCentralizer i ≤ t.1.levi) :
    relativeWeylConjugateSubgroupFunctor i t.1.levi hM w = t'.1.levi := by
  obtain ⟨n, rfl, hc, _⟩ := hw
  rw [relativeWeylConjugateSubgroupFunctor_mk]
  exact (SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mp hc

theorem WeylTransports.one (t : Θ) : WeylTransports a ha mu 1 t t := by
  refine ⟨1, rfl, ?_⟩
  exact OrbitConjugates.self_of_mem (t := t) ((levi t.1).one_mem)

theorem WeylTransports.inv {t t' : Θ} {w : relativeWeylGroup i}
    (hw : WeylTransports a ha mu w t t') : WeylTransports a ha mu w⁻¹ t' t := by
  obtain ⟨n, rfl, hn⟩ := hw
  exact ⟨n⁻¹, rfl, hn.inv⟩

theorem WeylTransports.mul {t t' t'' : Θ} {w v : relativeWeylGroup i}
    (hw : WeylTransports a ha mu w t t') (hv : WeylTransports a ha mu v t' t'') :
    WeylTransports a ha mu (v * w) t t'' := by
  obtain ⟨n, rfl, hn⟩ := hw
  obtain ⟨m, rfl, hm⟩ := hv
  exact ⟨m * n, rfl, hn.mul hm⟩

variable (a ha mu)

/-- Waldspurger VII.2.4 association of actual full indices `(O,P)` and `(O',P')`. -/
def Associated (t t' : Θ) : Prop := ∃ w : relativeWeylGroup i, WeylTransports a ha mu w t t'

/-- The source equivalence relation, using identity, inverse and composition of the literal transports. -/
def associationSetoid : Setoid Θ where
  r := Associated a ha mu
  iseqv := ⟨fun t => ⟨1, WeylTransports.one t⟩,
    fun ⟨w, hw⟩ => ⟨w⁻¹, hw.inv⟩,
    fun ⟨w, hw⟩ ⟨v, hv⟩ => ⟨v * w, hw.mul hv⟩⟩

/-- All association classes of the actual full index type. -/
abbrev AssociationClass : Type _ := Quotient (associationSetoid a ha mu)

/-- The literal members of the association class of `t`. -/
def associatedIndices (t : Θ) : Set Θ := {t' | Associated a ha mu t t'}

/-- The union of the actual association classes meeting a set of indices. -/
def associationSaturation (s : Set Θ) : Set Θ := ⋃ t ∈ s, associatedIndices a ha mu t

@[simp] theorem mem_associationSaturation (s : Set Θ) (t' : Θ) :
    t' ∈ associationSaturation a ha mu s ↔ ∃ t ∈ s, Associated a ha mu t t' := by
  simp [associationSaturation, associatedIndices]

variable {a ha mu}

/-- With Weyl class and target parabolic fixed, there is at most one target full index. -/
theorem WeylTransports.eq_of_same_parabolic {t t' t'' : Θ} {w : relativeWeylGroup i}
    (hw : WeylTransports a ha mu w t t') (hv : WeylTransports a ha mu w t t'')
    (hM : torusCentralizer i ≤ t.1.levi) (hp : t'.1 = t''.1) : t' = t'' := by
  obtain ⟨p, O⟩ := t'
  obtain ⟨q, O'⟩ := t''
  change p = q at hp
  subst q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨hc, ho⟩ := (weylTransports_mk_iff hM n).mp hw
  obtain ⟨_, ho'⟩ := (weylTransports_mk_iff hM n).mp hv
  have he : O = O' := orbitClass_eq_of_constituents_eq a ha mu p (ho.symm.trans ho')
  cases he
  rfl

variable (a ha mu)

/-- A class is finite by finite relative Weyl and finite actual `P(M')`, using
at most one orbit per target parabolic for each Weyl element. -/
theorem finite_associatedIndices (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hfinite : SemistandardSpectralFiberFinitenessStatement.{u}) (t : Θ)
    (hM : torusCentralizer i ≤ t.1.levi) : (associatedIndices a ha mu t).Finite := by
  have := hG.finite_relativeWeylGroup i hi
  have hfiniteW (w : relativeWeylGroup i) : {t' | WeylTransports a ha mu w t t'}.Finite := by
    let Iw := {t' // WeylTransports a ha mu w t t'}
    change Finite Iw
    by_cases h : Nonempty Iw
    · obtain ⟨q⟩ := h
      have := (hfinite F G hG S i hi q.val.1.toLevi).1
      let f (x : Iw) : SemistandardSpectralParabolicFiber i q.val.1.toLevi :=
        ⟨x.val.1, (x.property.levi_eq hM).symm.trans (q.property.levi_eq hM)⟩
      have hf : Function.Injective f := fun x y hxy => Subtype.ext
        (x.property.eq_of_same_parabolic y.property hM (congrArg Subtype.val hxy))
      exact Finite.of_injective f hf
    · have : IsEmpty Iw := not_nonempty_iff.mp h
      infer_instance
  have hu := Set.finite_iUnion hfiniteW
  convert hu using 1
  ext q
  simp [associatedIndices, Associated]

/-- Finite input support gives a finite association-saturated support bound. -/
theorem finite_associationSaturation (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hcontain : SemistandardLeviCentralizerContainmentStatement.{u})
    (hfinite : SemistandardSpectralFiberFinitenessStatement.{u}) {s : Set Θ} (hs : s.Finite) :
    (associationSaturation a ha mu s).Finite :=
  hs.biUnion fun t _ => finite_associatedIndices a ha mu hG hi hfinite t
    (hcontain F G hG S i hi t.1.toLevi)

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
