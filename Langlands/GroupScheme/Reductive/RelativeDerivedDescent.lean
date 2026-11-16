import Langlands.GroupScheme.Reductive.RelativeDerivedReduction
import Langlands.GroupScheme.NormalQuotientReductiveGluing
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalGluing
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching
import Langlands.GroupScheme.Torus.Locality
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Étale descent of admissible relative derived subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Semisimplicity of the geometric fibre can be reflected from any point
above the base point. -/
theorem isSemisimple_geometricFiber_of_baseChange_at
    {S T : Scheme.{u}} (D : GroupScheme S) (b : T ⟶ S)
    (hss : ∀ t : T, IsSemisimple (geometricFiber ((baseChange b).obj D) t))
    (t : T) : IsSemisimple (geometricFiber D (b t)) := by
  let k := S.residueField (b t)
  let K := T.residueField t
  let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
  let c := algebraicClosureBaseMap k K
  have hcomp : c ≫ geometricPoint S (b t) = geometricPoint T t ≫ b := by
    change (c ≫ toAlgebraicClosure k) ≫ S.fromSpecResidueField (b t) =
      (toAlgebraicClosure K ≫ T.fromSpecResidueField t) ≫ b
    rw [algebraicClosureBaseMap_comp]
    change (toAlgebraicClosure K ≫ Spec.map (b.residueFieldMap t)) ≫
      S.fromSpecResidueField (b t) = _
    rw [Category.assoc, b.SpecMap_residueFieldMap_fromSpecResidueField]
    exact (Category.assoc _ _ _).symm
  let e : GroupScheme.baseChange (geometricPoint S (b t)) ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange (geometricPoint T t) :=
    (Functor.mapGrpNatIso (Over.pullbackComp c (geometricPoint S (b t))) ≪≫
      Functor.mapGrpCompIso).symm ≪≫
    eqToIso (congrArg (fun f => GroupScheme.baseChange f) hcomp) ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp (geometricPoint T t) b) ≪≫
      Functor.mapGrpCompIso
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  exact IsSemisimple.of_fieldExtension ((hss t).of_iso (e.app D))

namespace RelativeDerived

variable {S : Scheme.{u}} {G D D' : GroupScheme S}

/-- Admissibility is preserved by an isomorphism of the source. -/
theorem IsAdmissible.iso_comp {d : D ⟶ G} (hd : IsAdmissible d) (e : D' ≅ D) :
    IsAdmissible (e.hom ≫ d) := by
  refine ⟨(IsClosedSubgroup.of_iso e).comp hd.1, ?_,
    hd.2.2.1.of_iso e, ?_, ?_⟩
  · rw [SubgroupFunctor.range_iso_comp]
    exact hd.2.1
  · intro s
    exact (hd.2.2.2.1 s).of_iso
      ((GroupScheme.baseChange (geometricPoint S s)).mapIso e)
  · rw [SubgroupFunctor.range_iso_comp]
    exact hd.2.2.2.2

/-- Any closed representative of an admissible all-test range is admissible. -/
theorem IsAdmissible.of_range_eq {d : D ⟶ G} (hd : IsAdmissible d)
    {d' : D' ⟶ G} (hd' : IsClosedSubgroup d')
    (heq : SubgroupFunctor.range d' = SubgroupFunctor.range d) :
    IsAdmissible d' := by
  let e := hd'.sourceIsoOfRangeEq hd.1 heq
  have he : e.hom ≫ d = d' := hd'.sourceIsoOfRangeEq_hom_comp hd.1 heq
  rw [← he]
  exact hd.iso_comp e

/-- The intrinsic commutator description identifies ranges across an ambient
isomorphism, without choosing an isomorphism between their sources. -/
theorem IsAdmissible.range_comp_iso_eq
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    {d : D ⟶ G} (hd : IsAdmissible d)
    {G' D' : GroupScheme S} {d' : D' ⟶ G'} (hd' : IsAdmissible d')
    (e : G' ≅ G) :
    SubgroupFunctor.range (d' ≫ e.hom) = SubgroupFunctor.range d := by
  ext T x
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    apply (hd.range_iff_locallyCommutator hperf T _).mpr
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      ((hd'.range_iff_locallyCommutator hperf T _).mp
        (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)).map e.hom
  · intro hx
    have hx' : x ≫ e.inv.hom.hom ∈ (SubgroupFunctor.range d').carrier T :=
      (hd'.range_iff_locallyCommutator hperf T _).mpr
        (((hd.range_iff_locallyCommutator hperf T x).mp hx).map e.inv)
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx'
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- Local admissible subgroups agree on every relative test over an étale
cover, assuming relative semisimple fppf-perfectness. -/
theorem isMatching_of_isAdmissible
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (D : ∀ i, GroupScheme (𝒰.X i))
    (d : ∀ i, D i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G)
    (hd : ∀ i, IsAdmissible (d i)) :
    SubgroupFunctor.CoverDescent.IsMatching 𝒰
      (fun i => SubgroupFunctor.range (d i)) := by
  apply SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq 𝒰 D d
  intro i j
  exact ((hd i).baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).range_comp_iso_eq
    hperf ((hd j).baseChange (pullback.snd (𝒰.f i) (𝒰.f j)))
    (SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 i j G).symm |>.symm

/-- Effective descent of admissible closed subgroup schemes, retaining
relative semisimple fppf-perfectness as an explicit input. -/
def admissibleRepresentativeEtale
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u}) (hG : IsReductive G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (D : ∀ i, GroupScheme (𝒰.X i))
    (d : ∀ i, D i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G)
    (hd : ∀ i, IsAdmissible (d i)) :
    {R : SubgroupFunctor.ClosedRepresentative
      (SubgroupFunctor.CoverDescent.subgroup 𝒰
        (fun i => SubgroupFunctor.range (d i))) // IsAdmissible R.hom} := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let F := fun i => SubgroupFunctor.range (d i)
  have hmatch := isMatching_of_isAdmissible hperf 𝒰 D d hd
  have hc : ∀ i, (F i).IsClosedRepresentable := by
    intro i
    let : IsClosedImmersion (d i).hom.hom.left := (hd i).1
    exact ⟨D i, d i, ⟨Over.mono_of_mono_left _, rfl⟩, (hd i).1⟩
  let R := SubgroupFunctor.CoverDescent.closedRepresentativeEtale 𝒰 F hmatch hc
  have hlocal (i : 𝒰.I₀) :
      IsAdmissible ((GroupScheme.baseChange (𝒰.f i)).map R.hom) := by
    apply (hd i).of_range_eq (R.closed.baseChange (𝒰.f i))
    rw [SubgroupFunctor.range_baseChangeHom, R.represents.2,
      SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 F hmatch i]
  have hsmooth : Smooth R.group.X.hom :=
    RelativeLevi.smooth_of_etaleCover 𝒰 R.group (fun i => (hlocal i).2.2.1.smooth)
  have haffine : IsAffineHom R.group.X.hom := by
    let : IsClosedImmersion R.hom.hom.hom.left := R.closed
    rw [← Over.w R.hom.hom.hom]
    infer_instance
  have hss (s : S) : IsSemisimple (geometricFiber R.group s) := by
    obtain ⟨i, t, rfl⟩ := 𝒰.exists_eq s
    exact isSemisimple_geometricFiber_of_baseChange_at R.group (𝒰.f i)
      (hlocal i).2.2.2.1 t
  have hn : (SubgroupFunctor.range R.hom).IsNormal := by
    rw [R.represents.2]
    exact SubgroupFunctor.CoverDescent.isNormal_subgroup 𝒰 F (fun i => (hd i).2.1)
  refine ⟨R, R.closed, hn, ⟨hsmooth, haffine, fun s =>
    (hss s).isConnectedReductive.isPseudoReductive⟩, hss, ?_⟩
  have : Mono R.hom.hom.hom := R.represents.1
  choose Q q hQ hq using (fun i => (hlocal i).2.2.2.2)
  obtain ⟨M, r, hM, hr⟩ :=
    NormalQuotient.exists_affine_fppfQuotient_of_etaleCover R.hom hsmooth hn 𝒰 Q q
      (fun i => (hQ i).isAffineHom) hq
  let : IsAffineHom M.X.hom := hM
  have htorus : RelativeTorus.IsTorus M := by
    apply RelativeTorus.IsTorus.of_etaleCover 𝒰
    intro i
    let b := 𝒰.f i
    have : IsAffineHom ((baseChange b).obj G).X.hom :=
      MorphismProperty.pullback_snd G.X.hom b inferInstance
    have : IsAffineHom ((baseChange b).obj M).X.hom :=
      MorphismProperty.pullback_snd M.X.hom b inferInstance
    have : IsAffineHom (Q i).X.hom := (hQ i).isAffineHom
    have : QuasiCompact ((q i).hom.hom.left ≫ (Q i).X.hom) := by
      rw [Over.w (q i).hom.hom]
      infer_instance
    have : QuasiCompact (q i).hom.hom.left :=
      QuasiCompact.of_comp _ (Q i).X.hom
    let r' := (GroupScheme.baseChange b).map r
    have : QuasiCompact (r'.hom.hom.left ≫ ((baseChange b).obj M).X.hom) := by
      rw [Over.w r'.hom.hom]
      infer_instance
    have : QuasiCompact r'.hom.hom.left :=
      QuasiCompact.of_comp _ ((baseChange b).obj M).X.hom
    have hr' : RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange b).map R.hom)) r' := by
      simpa only [SubgroupFunctor.range_baseChangeHom] using hr.baseChange b
    exact RelativeTorus.IsTorus.of_iso (FppfQuotientComparison.iso hr' (hq i)) (hQ i)
  exact ⟨M, r, htorus, hr⟩

end RelativeDerived

/-- Étale-local existence descends under relative semisimple perfectness. -/
def RelativeDerivedAdmissibleEtaleDescentStatement : Prop :=
  RelativeSemisimpleFppfPerfectStatement.{u} →
    ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
      ∀ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S),
        (∀ i, ∃ (D : GroupScheme (𝒰.X i))
          (d : D ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G),
          RelativeDerived.IsAdmissible d) →
        ∃ (D : GroupScheme S) (d : D ⟶ G), RelativeDerived.IsAdmissible d

/-- Proof of the conditional étale descent statement on arbitrary bases. -/
theorem relativeDerivedAdmissibleEtaleDescent :
    RelativeDerivedAdmissibleEtaleDescentStatement.{u} := by
  intro hperf S G hG 𝒰 hlocal
  choose D d hd using hlocal
  let R := RelativeDerived.admissibleRepresentativeEtale hperf hG 𝒰 D d hd
  exact ⟨R.1.group, R.1.hom, R.2⟩

end Langlands.GroupScheme
