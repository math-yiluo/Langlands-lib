import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Exponents.LeviJacquetInductionVanishingStatement
import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.GroupScheme.Rational.FullParabolicLevi

/-! # Cuspidal vanishing from the represented geometric lemma -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Intersections

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviJacquetCuspidalPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

omit [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- A full source intersection parabolic identifies `M` with the actual target
intersection Levi by conjugation by `z⁻¹`. -/
theorem GeometricLemmaIntersectionDatum.conjugateLevi_of_isIso
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    [IsIso D.p'] :
    ∃ φ : M ≅ D.L',
      φ.hom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso z⁻¹).hom := by
  let α := D.hl'.isoOfIsIsoParabolic (p := D.p') hl.isConnectedReductive
  refine ⟨α.symm ≪≫ D.φ.symm, ?_⟩
  apply (cancel_epi α.hom).mp
  have hφ : D.φ.hom ≫ α.hom ≫ l ≫ p =
      D.lQ' ≫ D.q' ≫ lQ ≫ q ≫ (G.innerIso z).hom := D.φ_comp
  have h := congrArg
    (fun f : D.L' ⟶ G => D.φ.inv ≫ f ≫ (G.innerIso z).inv) hφ
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id,
    G.innerIso_inv_hom] using h.symm

end Intersections

/-- The explicit consumer implication from the full represented geometric lemma
to the unchanged vanishing target. -/
def LeviJacquetInductionVanishingGeometricReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    LeviJacquetInductionVanishingStatement.{u, v}

/-- The exact represented geometric lemma implies Renard VI.5.3(i).
This is a conditional deduction, not an unconditional proof of either statement. -/
theorem leviJacquetInductionVanishing_of_geometricLemma
    (hgeom : RepresentedGeometricLemmaStatement.{u, v}) :
    LeviJacquetInductionVanishingStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hnone
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) :=
    leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro ρ hρ
  obtain ⟨m, c, z, hz, D, e, s, hs⟩ :=
    hgeom k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hpiece : ∀ i, Subsingleton (((D i).pieceFunctor).obj ρ) := by
    intro i
    have hproper : ¬ IsIso (D i).p' := by
      intro hfull
      have := hfull
      obtain ⟨φ, hφ⟩ := (D i).conjugateLevi_of_isIso
      exact hnone ⟨(D i).Q', (D i).L', (D i).q', (D i).lQ',
        (D i).hq', (D i).hlQ', (z i)⁻¹, φ, hφ⟩
    have hJ := hρ (D i).P' (D i).M' (D i).N'
      (D i).p' (D i).l' (D i).r' (D i).hp' (D i).hl' (D i).hr' (D i).hmul' hproper
    change Subsingleton (Induction.SmoothFunctions _ _)
    constructor
    intro f g
    apply Subtype.ext
    apply Subtype.ext
    exact funext (fun _ => hJ.elim _ _)
  have htotal := s.subsingleton_atObject ρ (fun i => by
    obtain ⟨f⟩ := hs i
    refine ⟨fun a b => (Representation.equivOfIso (f.app ρ)).injective ?_⟩
    exact (hpiece (e i)).elim _ _)
  exact htotal

end Langlands.Aubert.General.RepresentedParabolic
