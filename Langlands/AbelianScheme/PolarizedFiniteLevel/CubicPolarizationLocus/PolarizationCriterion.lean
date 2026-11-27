import Langlands.AbelianScheme.PolarizedFiniteLevel.AlgebraicallyClosedFieldPolarizationDivisionStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.MumfordLaws
import Langlands.AbelianScheme.BaseChangeCoherence
import Langlands.AbelianScheme.FiberwiseIsogeny
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordMapIsogeny

/-! # Recognition of the descended polarization by its geometric Mumford maps -/

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} (A : AbelianScheme S)

/-- Ampleness on every algebraically closed field-valued fibre. -/
def GeometricallyAmpleBundle (L : LineBundle A.X.left) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
    ((LineBundle.pullback (pullback.fst A.X.hom t)).obj L).IsAmple

private lemma fieldMumford_isogeny (K : Type u) [Field K] [IsAlgClosed K]
    (A₀ : AbelianScheme (Spec (CommRingCat.of K))) (W : DualWitness A₀)
    (f : A₀ ⟶ W.dual P)
    (h : HasAmpleMumfordPresentation P.preservation P.square A₀ W.hasDual
      (W.parameterMap P f)) : IsIsogeny f := by
  let P₀ : Rosati.Prerequisites.{u} :=
    ⟨P.preservation, P.composition, P.unitCoherence, P.associativity, P.comparison,
      P.symmetry, P.stability, P.square, P.universality⟩
  let W₀ : Rosati.DualData A₀ := ⟨W.hasDual, W.geometry, W.inverseBundle, W.evaluation⟩
  obtain ⟨L, M, evM, N, evN, ham, hmap⟩ := h
  exact AmpleMumfordIsogeny.isIsogeny P₀ K A₀ W₀ f L M evM N evN ham hmap

private lemma isIsogeny_of_fpqcBaseChange (b : T ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    {A₀ B₀ : AbelianScheme S} (f : A₀ ⟶ B₀)
    (h : IsIsogeny ((baseChange b).map f)) : IsIsogeny f := by
  let g := pullback.fst B₀.X.hom b
  have hg : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    ⟨⟨inferInstanceAs (Surjective (pullback.fst B₀.X.hom b)),
      inferInstanceAs (Flat (pullback.fst B₀.X.hom b))⟩,
      inferInstanceAs (QuasiCompact (pullback.fst B₀.X.hom b))⟩
  have sq := (hom_baseChange_isPullback b f).flip
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite) sq hg h.1,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) sq hg h.2.1,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) sq hg h.2.2⟩

private lemma isIsogeny_of_geometricFibre {A₀ B₀ : AbelianScheme S} (f : A₀ ⟶ B₀)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
      IsIsogeny ((baseChange s).map f)) : IsIsogeny f := by
  apply GroupScheme.fiberwiseIsogeny S A₀.toGrp B₀.toGrp A₀.smooth B₀.smooth A₀.proper B₀.proper
    (groupHom f)
  intro x
  let r := S.fromSpecResidueField x
  let K := AlgebraicClosure (S.residueField x)
  let φ : CommRingCat.of (S.residueField x) ⟶ CommRingCat.of K := CommRingCat.ofHom
    (algebraMap (S.residueField x) (AlgebraicClosure (S.residueField x)))
  let b := Spec.map φ
  have hb : Flat b ∧ Surjective b := (flat_and_surjective_SpecMap_iff φ).2
    (RingHom.faithfullyFlat_algebraMap_iff.2
      (inferInstanceAs (Module.FaithfullyFlat (S.residueField x) (AlgebraicClosure (S.residueField x)))))
  let := hb.1
  let := hb.2
  have : QuasiCompact b := inferInstanceAs (QuasiCompact (Spec.map φ))
  change IsIsogeny ((baseChange r).map f)
  apply isIsogeny_of_fpqcBaseChange b
  let eA := baseChangeCompIso r b A₀
  let eB := baseChangeCompIso r b B₀
  have hn : (baseChange (b ≫ r)).map f ≫ eB.hom = eA.hom ≫ (baseChange b).map ((baseChange r).map f) :=
    (baseChangeCompNatIso r b).hom.naturality f
  change IsIsogeny ((baseChange b).map ((baseChange r).map f))
  have he : eA.inv ≫ (baseChange (b ≫ r)).map f ≫ eB.hom =
      (baseChange b).map ((baseChange r).map f) := by
    rw [hn, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (isIsogeny_of_iso eA.symm).comp ((h K (b ≫ r)).comp (isIsogeny_of_iso eB))

/-- A map whose positive multiple is the Mumford map of a geometrically ample bundle
    is a polarization if positive-multiple descent holds on geometric fibres. -/
lemma isPolarization_of_nsmul_mumford [QuasiSeparatedSpace S]
    (division : AlgebraicallyClosedFieldPolarizationDivisionStatement.{u}) (W : DualWitness A)
    (f : A ⟶ W.dual P) (n : ℕ) (hn : 0 < n) (L : LineBundle A.X.left)
    (hL : GeometricallyAmpleBundle A L) (hf : n • f = lineBundleMumford P A W L) :
    W.IsPolarization P f := by
  have geom (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
      let W' := W.pullback P s
      HasAmpleMumfordPresentation P.preservation P.square ((baseChange s).obj A) W'.hasDual
        (W'.parameterMap P (W.pullbackMap P s W' f)) := by
    let W' := W.pullback P s
    let L' := (LineBundle.pullback (pullback.fst A.X.hom s)).obj L
    let f' := W.pullbackMap P s W' f
    have hm := lineBundleMumford_pullback P A W L s W'
    rw [← hf] at hm
    have hmf : n • f' = lineBundleMumford P ((baseChange s).obj A) W' L' := by
      rw [← hm, DualWitness.pullbackMap, Functor.map_nsmul, Preadditive.nsmul_comp]
      rfl
    refine division P K _ W' f' n hn ?_
    rw [hmf]
    exact hasAmpleMumfordPresentation_lineBundleMumford P _ W' L' (hL K s)
  refine ⟨isIsogeny_of_geometricFibre f (fun K _ _ s ↦ ?_), fun K _ _ s ↦ ?_⟩
  · let W' := W.pullback P s
    let e := W.baseChangeIso P s W'
    have hs := fieldMumford_isogeny P K _ W' (W.pullbackMap P s W' f) (geom K s)
    have hh := hs.comp (isIsogeny_of_iso e.symm)
    change IsIsogeny (((baseChange s).map f ≫ e.hom) ≫ e.inv) at hh
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
  · let W' := W.pullback P s
    have h := geom K s
    change HasAmpleMumfordPresentation P.preservation P.square ((baseChange s).obj A) W'.hasDual
      (W'.parameterMap P (W.pullbackMap P s W' f)) at h
    rw [DualWitness.parameterMap_pullbackMap] at h
    refine ⟨K, ‹Field K›, RingHom.id K, ?_⟩
    exact hasAmpleMumfordPresentation_baseChange (Spec.map (CommRingCat.ofHom (RingHom.id K)))
      _ P.preservation P.square P.universality W'.hasDual _ h

end Langlands.AbelianScheme.PolarizedFiniteLevel
