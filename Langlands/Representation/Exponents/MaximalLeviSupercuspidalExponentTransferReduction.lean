import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviExponentStatements
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Exponents.FullParabolicExponentCone
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.GroupScheme.Rational.MaximalLeviContainmentStatement
import Langlands.Representation.Geometric.RepresentedCuspidalLength
import Langlands.Representation.Filtration.NonzeroMapGradedPiece
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # The exponent-transfer step of Renard VII.1.3 from the geometric lemma

For an actual maximal proper parabolic `P = MN`, an irreducible supercuspidal `ρ` of `M(F)`
and a subrepresentation or quotient `W` of `i_P^G ρ`, the exponents of `W` along an
arbitrary parabolic `Q = LU` are controlled by those along the parabolics with Levi source
`M`. If `Q = G`, the unitary central character forces zero real parts. If `Q` is proper and
`r_Q W ≠ 0`, then `r_Q i_P ρ ≠ 0`; the geometric lemma gives a nonzero piece, supercuspidality
makes its source parabolic full, so `M ⊆ zLz⁻¹`, and maximality gives `M = zLz⁻¹`. Inner
conjugation and Levi reparametrization then turn `Q` into a parabolic with Levi source `M`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Support

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance maximalLeviTransferSupportPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- If the source parabolic `P' = M ∩ zQz⁻¹` of a geometric-lemma datum is full, then the
Levi image of `M` lies in the conjugate `zLz⁻¹` of the Levi image of `L`. -/
theorem GeometricLemmaIntersectionDatum.range_le_of_isIso_p'
    {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
    {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
    {hmul : IsIso (subgroupMultiplication l r)}
    {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
    {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
    {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    [IsIso D.p'] :
    SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q ≫ (G.innerIso z).hom) := by
  have : IsIso D.l' := D.hl'.isIso_of_isIso_parabolic (p := D.p') hl.isConnectedReductive
  have hfull : SubgroupFunctor.range (D.l' ≫ D.p' ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) := by
    simpa only [asIso_hom, Category.assoc] using
      SubgroupFunctor.range_iso_comp (asIso (D.l' ≫ D.p')) (l ≫ p)
  rw [← hfull, D.levi_eq, SubgroupFunctor.le_def]
  intro T x hx
  rw [SubgroupFunctor.inf_carrier] at hx
  exact (Subgroup.mem_inf.mp hx).2

/-- Support of `r_Q i_P ρ` for supercuspidal `ρ`, from the geometric lemma: if the normalized
Jacquet module of `i_P^G ρ` along `Q` is nontrivial, the Levi image of `M` lies in a
`G(F)`-conjugate of the Levi image of `L`. -/
theorem exists_range_le_innerIso_of_nontrivial_jacquet
    (hgeo : RepresentedGeometricLemmaStatement.{u, v}) (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    (hne : letI := leviPointTopology l hl
      Nontrivial ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) :
    ∃ z : rationalPoints G,
      SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q ≫ (G.innerIso z).hom) := by
  let := leviPointTopology l hl
  obtain ⟨m, c, z, -, D, hglue⟩ :=
    hgeo k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  let F := leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
  have hF : Nontrivial (F.obj ρ) := hne
  have hid : Representation.IntertwiningMap.id (F.obj ρ).ρ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : F.obj ρ)
    apply hx
    simpa using congrArg (fun f : (F.obj ρ).ρ.IntertwiningMap (F.obj ρ).ρ => f x) h0
  obtain ⟨i, h, hh⟩ := hglue.exists_piece_intertwiningMap_ne_zero ρ _ hid
  have hpi : IsIso (D i).p' := by
    by_contra hproper
    have := (D i).pieceFunctor_subsingleton_of_proper ρ hc hproper
    apply hh
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  exact ⟨z i, (D i).range_le_of_isIso_p'⟩

end Support

/-- Renard VII.1.3, transfer step, as a conditional statement: the represented geometric
lemma and the containment of maximal Levi subgroups give the exponent-transfer statement. -/
def MaximalLeviSupercuspidalExponentTransferReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    MaximalLeviContainmentStatement.{u} →
      MaximalLeviSupercuspidalExponentTransferStatement.{u, v}

/-- Renard VII.1.3, transfer step: the represented geometric lemma and the containment of
maximal Levi subgroups give the exponent-transfer statement. -/
theorem maximalLeviSupercuspidalExponentTransfer_of_geometricLemma :
    MaximalLeviSupercuspidalExponentTransferReductionStatement.{u, v} := by
  intro hgeo hS2 k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hpne hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ _ hc hunit W hWπ hW
  obtain ⟨cπ⟩ := hunit
  intro Q L UQ A q lQ rQ a hq hlQ hrQ hmulQ ha pres χ hχ
  by_cases hqIso : IsIso q
  · have : IsIso lQ := hlQ.isIso_of_isIso_parabolic (p := q) hG
    have hcW : Nonempty (UnitaryCentralCharacter W.representation) := by
      rcases hWπ with ⟨f, hf⟩ | ⟨f, hf⟩
      · exact ⟨unitaryCentralCharacterOfInjective cπ f hf⟩
      · exact ⟨unitaryCentralCharacterOfSurjective cπ f hf⟩
    obtain ⟨cW⟩ := hcW
    exact normalizedJacquetExponent_mem_positiveCone_of_isIso q lQ rQ hq hlQ hrQ hmulQ ha pres
      W cW χ hχ
  · have hJW := nontrivial_jacquet_of_isNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha
      W χ hχ
    have hJπ : Nontrivial ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) := by
      rcases hWπ with ⟨f, hf⟩ | ⟨f, hf⟩
      · exact nontrivial_jacquet_of_injective q lQ rQ hq hlQ hrQ hmulQ f hf
      · exact nontrivial_jacquet_of_surjective q lQ rQ hq hlQ hrQ hmulQ f hf
    obtain ⟨z, hle⟩ := exists_range_le_innerIso_of_nontrivial_jacquet hgeo hG p l r hp hl hr
      hmul q lQ rQ hq hlQ hrQ hmulQ ρ hc hJπ
    have hq' : IsParabolicSubgroup (q ≫ (G.innerIso z).hom) := hq.comp_iso (G.innerIso z)
    have hq'ne : ¬ IsIso (q ≫ (G.innerIso z).hom) := by
      intro h
      exact hqIso (IsIso.of_isIso_comp_right q (G.innerIso z).hom)
    have heq := hS2 k G hG P M Q L p l (q ≫ (G.innerIso z).hom) lQ hp hl hpne hmax hq' hlQ
      hq'ne hle
    have hcM : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
    have hcL : IsClosedSubgroup (lQ ≫ q ≫ (G.innerIso z).hom) :=
      hlQ.isClosedSubgroup.comp hq'.isClosedSubgroup
    have : IsClosedImmersion (l ≫ p).hom.hom.left := hcM
    have : IsClosedImmersion (lQ ≫ q ≫ (G.innerIso z).hom).hom.hom.left := hcL
    have hrepM : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    have hrepL : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy
        (lQ ≫ q ≫ (G.innerIso z).hom) :=
      ⟨Over.mono_of_mono_left _, heq.symm⟩
    let e : M ≅ L := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hrepM hrepL
    have he : e.hom ≫ lQ ≫ q ≫ (G.innerIso z).hom = l ≫ p :=
      SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hrepM hrepL
    have hlQ' : IsRationalLeviSubgroup (e.hom ≫ lQ) := hlQ.iso_comp e
    have hmulQ' : IsIso (subgroupMultiplication (e.hom ≫ lQ) rQ) :=
      isIso_subgroupMultiplication_iso_comp e hmulQ
    have ha' : IsSplitComponent (a ≫ e.inv) := ha.comp_iso e.symm
    have hχ' : IsNormalizedJacquetExponent (q ≫ (G.innerIso z).hom) (e.hom ≫ lQ) rQ hq' hlQ'
        hrQ hmulQ' ha' W χ :=
      (isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff q lQ rQ hq hlQ hrQ hmulQ z e hq'
        hlQ' hmulQ' ha ha' W χ).mpr hχ
    have hpos := hW Q UQ A (q ≫ (G.innerIso z).hom) (e.hom ≫ lQ) rQ (a ≫ e.inv) hq' hlQ' hrQ
      hmulQ' ha' ((pres.compAmbientIso (G.innerIso z)).leviIsoComp e) χ
      (by simpa only [Category.assoc] using he) hχ'
    rwa [ParabolicRootPresentation.positiveCone_leviIsoComp,
      ParabolicRootPresentation.positiveCone_compAmbientIso] at hpos

end Langlands.Aubert.General.RepresentedParabolic
