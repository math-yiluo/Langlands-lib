import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertAbelianPresentation
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertNormalization
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingFrameLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.MarkedFullLevelLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocusStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.DatumTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.QuasiSeparatedDualWitness
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

/-! # Reduction of the frame Hilbert locus to the abelian and polarization loci -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace FrameHilbert

variable {P : Prerequisites.{u}} {S T R : Scheme.{u}} {g d n m : ℕ}
  {I : (RelativeProjectiveSpace S m).IdealSheafData}
  {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}
  {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}

private def RealizedAfter (P : Prerequisites.{u}) (d : ℕ)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) (t : T ⟶ S) : Prop :=
  ∃ (a : Datum P T g d n) (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace T m),
    a.IsFrameEmbedding ρ ψ ∧
      a.Realizes ψ (I.comap (RelativeProjectiveSpace.map m t)) (fun r => t ≫ σ r)

private theorem realizedAfter_comp_iff (b : R ⟶ S) (t : T ⟶ R) :
    RealizedAfter P d ρ (I.comap (RelativeProjectiveSpace.map m b)) (fun r => b ≫ σ r) t ↔
      RealizedAfter P d ρ I σ (t ≫ b) := by
  simp only [RealizedAfter, RelativeProjectiveSpace.map_comp, Scheme.IdealSheafData.comap_comp,
    Category.assoc]

private theorem normalizedMarks_comp (h : NormalizedMarks ρ σ) (t : T ⟶ S) :
    NormalizedMarks ρ (fun r => t ≫ σ r) := by
  obtain ⟨f, hf⟩ := (factorsThrough_normalization_iff ρ σ (𝟙 S)).mpr (by
    simpa only [Category.id_comp] using h)
  exact (factorsThrough_normalization_iff ρ σ t).mp
    ⟨t ≫ f, by rw [Category.assoc, hf, Category.comp_id]⟩

private theorem factorsThrough_subscheme (J : S.IdealSheafData) (t : T ⟶ S) :
    (∃ f : T ⟶ J.subscheme, f ≫ J.subschemeι = t) ↔ J ≤ t.ker := by
  rw [← FlatEquivalenceRelation.ker_le_ker_iff_exists, Scheme.IdealSheafData.ker_subschemeι]

private theorem range_subset_basicOpen_natCast_iff (t : T ⟶ S) (n : ℕ) :
    Set.range t ⊆ S.basicOpen (n : Γ(S, ⊤)) ↔ IsUnit (n : Γ(T, ⊤)) := by
  have he : t ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤)) = T.basicOpen (n : Γ(T, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, map_natCast]
  have ht : Set.range t ⊆ S.basicOpen (n : Γ(S, ⊤)) ↔
      t ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤)) = ⊤ := by
    constructor
    · intro h
      apply top_unique
      intro x _
      exact h ⟨x, rfl⟩
    · intro h
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ t ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤)) := by rw [h]; trivial
      exact hx
  rw [ht, he]
  exact ⟨ProjectiveSpace.CoordinateLines.isUnit_of_basicOpen_eq_top T _ , T.basicOpen_of_isUnit⟩

private theorem exists_incidentNormalizedLocus (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m))
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) :
    ∃ (S₀ : Scheme.{u}) (j₀ : S₀ ⟶ S), IsImmersion j₀ ∧ IsUnit (n : Γ(S₀, ⊤)) ∧
      NormalizedMarks ρ (fun r => j₀ ≫ σ r) ∧
      (∀ r, ∃ s : S₀ ⟶ (I.comap (RelativeProjectiveSpace.map m j₀)).subscheme,
        s ≫ (I.comap (RelativeProjectiveSpace.map m j₀)).subschemeι =
          RelativeProjectiveSpace.lift m (𝟙 S₀) (j₀ ≫ σ r)) ∧
      ∀ (T : Scheme.{u}) (t : T ⟶ S), IsUnit (n : Γ(T, ⊤)) →
        RealizedAfter P d ρ I σ t → ∃ l : T ⟶ S₀, l ≫ j₀ = t := by
  let J := incidenceIdeal I σ ⊔ normalizationIdeal ρ σ
  let U := J.subscheme.basicOpen (n : Γ(J.subscheme, ⊤))
  let j := U.ι ≫ J.subschemeι
  have hJ : J ≤ j.ker := J.ker_subschemeι.ge.trans (U.ι.le_ker_comp _)
  have hu : IsUnit (n : Γ(U, ⊤)) := (range_subset_basicOpen_natCast_iff U.ι n).mp (by
    rw [Scheme.Opens.range_ι])
  have hi : incidenceIdeal I σ ≤ j.ker := le_sup_left.trans hJ
  have hz : normalizationIdeal ρ σ ≤ j.ker := le_sup_right.trans hJ
  refine ⟨U, j, inferInstanceAs (IsImmersion (U.ι ≫ J.subschemeι)), hu,
    (factorsThrough_normalization_iff ρ σ j).mp ((factorsThrough_subscheme _ _).mpr hz),
    (factorsThrough_incidence_iff I σ j).mp ((factorsThrough_subscheme _ _).mpr hi), ?_⟩
  intro T t ht
  rintro ⟨a, ψ, he, hr⟩
  let := he.isClosedImmersion
  have hi' : incidenceIdeal I σ ≤ t.ker := (factorsThrough_subscheme _ _).mp
    ((factorsThrough_incidence_iff I σ t).mpr fun r =>
      ⟨a.torsionPoint r ≫ hr.subschemeIso.hom, (Category.assoc _ _ _).trans
        (hr.torsionPoint_subschemeIso he r)⟩)
  have hz' : normalizationIdeal ρ σ ≤ t.ker := (factorsThrough_subscheme _ _).mp
    ((factorsThrough_normalization_iff ρ σ t).mpr (he.normalizedMarks hr))
  obtain ⟨f, hf⟩ := (factorsThrough_subscheme J t).mpr (sup_le hi' hz')
  let l := IsOpenImmersion.lift U.ι f (by
    rw [Scheme.Opens.range_ι]
    exact (range_subset_basicOpen_natCast_iff f n).mpr ht)
  refine ⟨l, ?_⟩
  change l ≫ U.ι ≫ J.subschemeι = t
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hf]

private theorem realizedAfter_iff_polarization_and_level (B : AbelianPresentation I σ)
    (t : T ⟶ S) [IsLocallyNoetherian T] (hnorm : NormalizedMarks ρ (fun r => t ≫ σ r)) :
    RealizedAfter P d ρ I σ t ↔
      ExistsCubicPolarization P d ((baseChange t).obj B.abelian)
        ((LineBundle.pullback (pullback.fst B.abelian.X.hom t ≫ B.embedding)).obj
          (RelativeProjectiveSpace.twistOne S m)) ∧
      (∃ v : FullLevel ((baseChange t).obj B.abelian) g n,
        ∀ r, (Additive.toMul (enumerateTuple v.sections r)).val.left ≫
          pullback.fst B.abelian.X.hom t = t ≫ B.marks r) := by
  let B' := B.pullback t
  constructor
  · rintro ⟨a, ψ, he, hr⟩
    obtain ⟨e, hψ, hmarks⟩ := B'.exists_iso_of_realizes he hr
    let W := DualWitness.ofQuasiSeparated B'.abelian
    let a' := a.transport e W
    let iso := a.transportIso e W
    have he' : a'.IsFrameEmbedding ρ B'.embedding :=
      Eq.mp (congrArg (fun f : B'.abelian.X.left ⟶ RelativeProjectiveSpace T m =>
        a'.IsFrameEmbedding ρ f) hψ) (he.ofPolarizedIso iso)
    obtain ⟨N, ⟨hL⟩⟩ := he'.cubic
    refine ⟨⟨W, a'.polarization, a'.polarized, a'.degree, N,
      ⟨(B.pullbackTwistIso t).symm ≪≫ hL⟩⟩, ⟨a'.level, ?_⟩⟩
    intro r
    have hm : a'.torsionPoint r = B'.marks r := by
      apply (cancel_mono (hom e.hom)).mp
      exact (iso.torsionPoint_hom r).trans (hmarks r).symm
    change a'.torsionPoint r ≫ pullback.fst B.abelian.X.hom t = t ≫ B.marks r
    rw [hm]
    exact B.pullback_marks_fst t r
  · rintro ⟨⟨W, lam, hpol, hdeg, N, ⟨hL⟩⟩, ⟨v, hv⟩⟩
    let a : Datum P T g d n :=
      ⟨B'.abelian, B'.dimension, W, lam, hpol, hdeg, v⟩
    let ψ := B'.embedding
    have hm (r : Fin (2 * g) → ZMod n) : a.torsionPoint r = B'.marks r := by
      apply pullback.hom_ext
      · exact (hv r).trans (B.pullback_marks_fst t r).symm
      · exact (a.torsionPoint_hom r).trans (B'.marks_overBase r).symm
    have hr : a.Realizes ψ (I.comap (RelativeProjectiveSpace.map m t)) (fun r => t ≫ σ r) := by
      refine ⟨B'.embedding_ker, fun r => ?_⟩
      rw [hm, B'.marks_embedding_assoc, RelativeProjectiveSpace.lift_toIntegral]
    obtain ⟨hb, hu⟩ := hr.normalizedMarks_iff.mp hnorm
    exact ⟨a, ψ, ⟨B'.embedding_toBase, inferInstanceAs (IsClosedImmersion B'.embedding),
      ⟨N, ⟨B.pullbackTwistIso t ≪≫ hL⟩⟩, hb, hu⟩, hr⟩

private theorem exists_locus_of_abelianPresentation [IsLocallyNoetherian S]
    (Hpol : CubicPolarizationLocusStatement.{u}) (B : AbelianPresentation I σ)
    (hd : 0 < d) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hnorm : NormalizedMarks ρ σ) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
        (∃ l : T ⟶ Z, l ≫ j = t) ↔ RealizedAfter P d ρ I σ t := by
  obtain ⟨Zp, jp, hp, hpol⟩ := Hpol P S B.abelian m d hd B.embedding inferInstance B.embedding_toBase
  obtain ⟨Zl, jl, hl, hlevel⟩ := exists_closed_markedFullLevelLocus B.abelian g n hn hu B.markedSection
  let j := pullback.fst jp jl ≫ jp
  refine ⟨pullback jp jl, j, inferInstanceAs (IsImmersion (pullback.fst jp jl ≫ jp)), fun T _ t => ?_⟩
  have hlevel' : (∃ l : T ⟶ Zl, l ≫ jl = t) ↔
      ∃ v : FullLevel ((baseChange t).obj B.abelian) g n,
        ∀ r, (Additive.toMul (enumerateTuple v.sections r)).val.left ≫
          pullback.fst B.abelian.X.hom t = t ≫ B.marks r := hlevel T t
  rw [realizedAfter_iff_polarization_and_level B t (normalizedMarks_comp hnorm t),
    ← hpol T t, ← hlevel']
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f ≫ pullback.fst jp jl, (Category.assoc _ _ _).trans hf⟩,
      ⟨f ≫ pullback.snd jp jl, by rw [Category.assoc, ← pullback.condition]; exact hf⟩⟩
  · rintro ⟨⟨fp, hfp⟩, ⟨fl, hfl⟩⟩
    let f := pullback.lift fp fl (hfp.trans hfl.symm)
    exact ⟨f, (pullback.lift_fst_assoc _ _ _ _).trans hfp⟩

end FrameHilbert

open FrameHilbert

set_option linter.defProp false in
/-- The pointed projective abelian locus and the cubic polarization locus suffice to
construct the frame-normalized Hilbert locus of the published statement. -/
def frameHilbertLocus_of_pointedAbelian_and_cubicPolarization
    (Hab : PointedProjectiveAbelianLocusStatement.{0})
    (Hpol : CubicPolarizationLocusStatement.{0}) : FrameHilbertLocusStatement := by
  intro P g d n hd hn ρ S _ I σ hflat hfp
  let m := cubicProjectiveDimension g d
  have hn' : 0 < n := by omega
  obtain ⟨S₀, j₀, hj₀, hu₀, hnorm₀, hs₀, hfactor₀⟩ :=
    exists_incidentNormalizedLocus (P := P) (d := d) I σ ρ
  let I₀ := I.comap (RelativeProjectiveSpace.map m j₀)
  let σ₀ r := j₀ ≫ σ r
  choose s hs using hs₀
  let : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian j₀
  have hFlat₀ : Flat (projection I₀) :=
    MorphismProperty.of_isPullback (isPullback_subschemeBaseChange I j₀) hflat
  have hFp₀ : LocallyOfFinitePresentation (projection I₀) :=
    MorphismProperty.of_isPullback (isPullback_subschemeBaseChange I j₀) hfp
  have hzero : s 0 ≫ projection I₀ = 𝟙 S₀ := by
    rw [← Category.assoc, hs, RelativeProjectiveSpace.lift_toBase]
  obtain ⟨U, hU⟩ := Hab S₀ I₀.subscheme m g I₀.subschemeι inferInstance (s 0) hzero hFlat₀ hFp₀
  obtain ⟨A, e, hdim, hbase, hunit⟩ := (hU U U.ι).mp (by
    rw [Scheme.Opens.range_ι])
  let B := AbelianPresentation.ofPointedPullback U.ι s hs A e hdim hbase hunit
  have huU : IsUnit (n : Γ(U, ⊤)) := Tate.isUnit_natCast_pullback U.ι n hu₀
  obtain ⟨Z, j, hj, hZ⟩ := exists_locus_of_abelianPresentation (P := P) Hpol B hd hn' huU
    (normalizedMarks_comp hnorm₀ U.ι)
  let k := j ≫ U.ι ≫ j₀
  have hk : IsImmersion k := inferInstanceAs (IsImmersion (j ≫ U.ι ≫ j₀))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian k
  let Z' := LevelBase.ofScheme Z (Tate.isUnit_natCast_pullback (j ≫ U.ι) n hu₀)
  refine ⟨Z', k, hk, ?_, ?_⟩
  · have hW := (hZ Z j).mp ⟨𝟙 Z, Category.id_comp j⟩
    have hW₀ := (realizedAfter_comp_iff (I := I₀) (σ := σ₀) U.ι j).mp hW
    obtain ⟨a, ψ, he, hr⟩ := (realizedAfter_comp_iff (I := I) (σ := σ) j₀ (j ≫ U.ι)).mp hW₀
    exact ⟨a, ψ, he.frameLocus_eq_top hd, he, by simpa only [k, Category.assoc] using hr⟩
  · intro T t a ψ _ he hr
    obtain ⟨l₀, hl₀⟩ := hfactor₀ T.obj t T.level_isUnit ⟨a, ψ, he, hr⟩
    have hr₀ : RealizedAfter P d ρ I₀ σ₀ l₀ :=
      (realizedAfter_comp_iff (I := I) (σ := σ) j₀ l₀).mpr (by rw [hl₀]; exact ⟨a, ψ, he, hr⟩)
    obtain ⟨a₀, ψ₀, he₀, hr₀'⟩ := hr₀
    let lU := IsOpenImmersion.lift U.ι l₀ (by
      rw [Scheme.Opens.range_ι]
      exact (hU T.obj l₀).mpr (hasPointedAbelianPullback_of_realizes (s 0) (hs 0) l₀ he₀ hr₀'))
    have hlU : lU ≫ U.ι = l₀ := IsOpenImmersion.lift_fac _ _ _
    have hreal := (realizedAfter_comp_iff (I := I₀) (σ := σ₀) U.ι lU).mpr
      (by rw [hlU]; exact ⟨a₀, ψ₀, he₀, hr₀'⟩)
    obtain ⟨l, hl⟩ := (hZ T.obj lU).mpr hreal
    exact ⟨l, by change l ≫ j ≫ U.ι ≫ j₀ = t
                 rw [← Category.assoc, hl, ← Category.assoc, hlU, hl₀]⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
