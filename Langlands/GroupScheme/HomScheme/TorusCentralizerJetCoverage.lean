import Langlands.GroupScheme.HomScheme.TorusCentralizerOpenNormalizer
import Langlands.GroupScheme.HomScheme.TorusCentralizerResidueLocus
import Langlands.GroupScheme.IdentityJetNormalizer
import Langlands.GroupScheme.IdentityJetOpenSubgroup
import Langlands.GroupScheme.IdentityJetSmoothUnitAffineChart
import Langlands.GroupScheme.IdentityJetStabilizerOpenLocus
import Langlands.GroupScheme.Torus.RelativeCommutativity

/-! # Local detection of torus centralizers by a finite identity jet -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open IdentityJet SubgroupFunctor

private theorem exists_openInStabilizer_overField {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hc : IsTorusCentralizer (range i)) :
    ∃ n, OpenInStabilizer i n := by
  obtain ⟨K, t, _, hK, he⟩ := hc
  let T := hK.commGroupScheme
  have he' : range i = torusCentralizer (T := T) t := by
    rw [torusCentralizer_eq_centralizer_range]
    exact he
  obtain ⟨⟨N, j, hrep, hj⟩, n, hn⟩ := identityJetNormalizer (CommRingCat.of k) H G i hi
  obtain ⟨a, ha, hopen⟩ :=
    torusCentralizerOpenNormalizer k G H N T t hK.isTorus i hi he' j hj hrep
  refine ⟨n, N, j, hj, ?_, a, ha, hopen⟩
  rw [hn n le_rfl]
  exact hrep

/-- For a smooth separated group, the rank of the first jet determines the
open locus for fixed-rank smoothness of that group on every test. -/
theorem exists_smoothGroupFixedRankOpen {S : Scheme.{u}} (H : GroupScheme S)
    [Smooth H.X.hom] [IsSeparated H.X.hom] (r : ℕ) :
    ∃ U : S.Opens, ∀ (T : Scheme.{u}) (b : T ⟶ S),
      Set.range b ⊆ U ↔ SmoothUnitRankTest H r b := by
  let p := projection H 1
  obtain ⟨hfinite, hflat, hfp⟩ := projection_geometry H 1
  let : IsFinite p := hfinite
  let : Flat p := hflat
  let : LocallyOfFinitePresentation p := hfp
  let U : S.Opens := ⟨{s | p.finrank s = 1 + r}, p.isLocallyConstant_finrank.isOpen_fiber _⟩
  refine ⟨U, fun T b => ?_⟩
  let H' := (baseChange b).obj H
  have : Smooth H'.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsSeparated H'.X.hom := inferInstanceAs (IsSeparated (pullback.snd H.X.hom b))
  have hs : SmoothAlongUnit H' := by
    intro s
    apply Scheme.Hom.mem_smoothLocus.mp
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have hr (s : T) : (projection H' 1).finrank s = p.finrank (b s) :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (baseChange_isPullback H b 1) s
  constructor
  · intro h
    exact ⟨hs, (projection_geometry H' 1).2.1, fun s => (hr s).trans (h ⟨s, rfl⟩)⟩
  · intro h
    rintro _ ⟨s, rfl⟩
    exact (hr s).symm.trans (h.2.2 s)

/-- Every point of an arbitrary test with an actual smooth connected closed
subgroup that is a torus centralizer in each residue fibre has an open
neighborhood of fixed rank on which one finite jet stabilizer contains it openly. -/
def TorusCentralizerJetCoverageStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    HasAffineResidueFibers G → ∀ (T : Over (Spec R)) (H : GroupScheme T.left)
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ (baseChange T.hom).obj G), IsClosedSubgroup i → HasTorusCentralizerResidueFibres i →
    ∀ t : T.left, ∃ (n r : ℕ) (V : T.left.Opens), t ∈ V ∧
      SmoothUnitRankTest H r V.ι ∧
      OpenInStabilizer (familyHom i (Over.homMk (V := T) (U := Over.mk (V.ι ≫ T.hom)) V.ι rfl)) n

set_option maxHeartbeats 900000 in
theorem torusCentralizerJetCoverage : TorusCentralizerJetCoverageStatement.{u} := by
  intro R G _ _ _ hG T H _ _ i hi hc t
  let G' := (baseChange T.hom).obj G
  let b := T.left.fromSpecResidueField t
  let K := (baseChange b).obj H
  let L := (baseChange b).obj G'
  let j : K ⟶ L := (baseChange b).map i
  have : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom T.hom))
  have : IsSeparated G'.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom T.hom))
  have : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom T.hom))
  have : Smooth L.X.hom := inferInstanceAs (Smooth (pullback.snd G'.X.hom b))
  have : IsSeparated L.X.hom := inferInstanceAs (IsSeparated (pullback.snd G'.X.hom b))
  have : QuasiCompact L.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G'.X.hom b))
  have : IsAffineHom L.X.hom := (hG.baseChange T.hom) t
  have : Smooth K.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : GeometricallyConnected K.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))
  obtain ⟨n, hn⟩ := exists_openInStabilizer_overField j (hi.baseChange b) (hc t)
  obtain ⟨D, hD⟩ := identityJetStabilizerParameter R G n
  obtain ⟨W, hW⟩ := exists_open_of_openInStabilizer_familyHom n D hD i hi
  let e : Over.mk (b ≫ T.hom) ⟶ T := Over.homMk b rfl
  have htW : t ∈ W := by
    have h := (hW _ e).1.mpr hn
    apply h
    change t ∈ Set.range (T.left.fromSpecResidueField t)
    rw [Scheme.range_fromSpecResidueField]
    exact Set.mem_singleton _
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  obtain ⟨U, r, htU, hU⟩ := exists_smoothAlongUnitOfRank_open H t
  let V := U ⊓ W
  refine ⟨n, r, V, ⟨htU, htW⟩, ?_, ?_⟩
  · have h := SmoothUnitRankTest.comp H (show SmoothUnitRankTest H r U.ι from hU)
      (T.left.homOfLE (show V ≤ U from inf_le_left))
    rwa [Scheme.homOfLE_ι] at h
  · let v : Over.mk (V.ι ≫ T.hom) ⟶ T := Over.homMk V.ι rfl
    exact (hW _ v).2.mp (by
      intro x hx
      change x ∈ Set.range V.ι at hx
      have hx' : x ∈ (V : Set T.left) := (Scheme.Opens.range_ι V) ▸ hx
      exact hx'.2)

end Langlands.GroupScheme.TorusSubgroupModuli
