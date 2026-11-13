import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityProof
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.Torus.ClosedImmersionLocus
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-! # Split rank under Henselian specialization -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme
open HomScheme

/-- A closed standard split torus in a quotient-field fibre of a smooth affine
Henselian group lifts to a closed standard split torus of the same rank. -/
theorem exists_closed_splitTorus_of_residue
    {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (I : Type u) [Finite I]
    (i₀ : splitTorus (Spec (CommRingCat.of k)) I ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj G)
    (hi₀ : IsClosedSubgroup i₀) :
    ∃ i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G, IsClosedSubgroup i := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let H := splitTorus (Spec (CommRingCat.of R)) I
  let j₀ : RelativeHom H G (Over.mk c) := (splitTorus.baseChangeIso c I).hom ≫ i₀
  have hj₀ : IsClosedSubgroup j₀ := hi₀.iso_comp (splitTorus.baseChangeIso c I)
  obtain ⟨M, i, hi, hM⟩ :=
    smoothSplitSourceRepresentability _ H G (isSplitTorus_splitTorus I)
  obtain ⟨x, hx⟩ := (hi (Over.mk c)).surjective j₀
  change evaluate x i = j₀ at hx
  have hxclosed : IsClosedImmersion ((baseChange x.left).map i).hom.hom.left := by
    apply (isClosedImmersion_evaluate_iff x i).mp
    rw [hx]
    exact hj₀
  have : IsAffineHom ((baseChange M.hom).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom M.hom)
    exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  obtain ⟨V, q, hq, bx, hbx, hqclosed⟩ :=
    exists_open_isClosedImmersion_baseChange ((isSplitTorus_splitTorus I).baseChange M.hom)
      i k x.left hxclosed
  let v : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ M.hom)
  let vM : v ⟶ M := Over.homMk q rfl
  have hvclosed : IsClosedSubgroup (evaluate vM i) :=
    (isClosedImmersion_evaluate_iff vM i).mpr hqclosed
  have hvSmooth : Smooth v.hom := by
    dsimp [v]
    infer_instance
  have hbxc : bx ≫ v.hom = c := by
    dsimp [v]
    rw [← Category.assoc, hbx]
    exact Over.w x
  obtain ⟨σ, hσ, -⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk v.hom bx hbxc
  let A := sectionPullbackIso v.hom σ hσ H
  let B := sectionPullbackIso v.hom σ hσ G
  refine ⟨A.inv ≫ (baseChange σ).map (evaluate vM i) ≫ B.hom, ?_⟩
  exact ((hvclosed.baseChange σ).comp_iso B).iso_comp A.symm

/-- A choice of a closed standard split torus of the prescribed residue rank.
Only its rank and closedness are specified. -/
def henselianClosedSplitTorusLift
    {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (I : Type u) [Finite I]
    (i₀ : splitTorus (Spec (CommRingCat.of k)) I ⟶
      (baseChange (Spec.algebraMap R k)).obj G) (hi₀ : IsClosedSubgroup i₀) :
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G // IsClosedSubgroup i} :=
  ⟨(exists_closed_splitTorus_of_residue hk G I i₀ hi₀).choose,
    (exists_closed_splitTorus_of_residue hk G I i₀ hi₀).choose_spec⟩

/-- The split rank of a residue fibre is bounded by that of any field fibre. -/
theorem splitRank_residue_le
    {R k K : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [Field K] [Algebra R K]
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    splitRank ((baseChange (Spec.algebraMap R k)).obj G) ≤
      splitRank ((baseChange (Spec.algebraMap R K)).obj G) := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i₀ => iSup_le fun hi₀ => ?_
  obtain ⟨i, hi⟩ := exists_closed_splitTorus_of_residue hk G I i₀ hi₀
  exact card_le_splitRank I
    ((splitTorus.baseChangeIso (Spec.algebraMap R K) I).inv ≫
      (baseChange (Spec.algebraMap R K)).map i)
    ((hi.baseChange (Spec.algebraMap R K)).iso_comp
      (splitTorus.baseChangeIso (Spec.algebraMap R K) I).symm)

/-- A closed split torus attaining the ambient split rank is maximal. -/
theorem IsSplitSubtorus.isMaximal_of_card_eq_splitRank
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsSplitSubtorus i) (I : Type u) [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (hrank : (Nat.card I : ℕ∞) = splitRank G) : IsMaximalSplitTorus i := by
  refine ⟨hi, ?_⟩
  intro T' i' hi' f hf
  obtain ⟨J, hJ, ⟨e'⟩⟩ := hi'.1
  let d : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J := e.inv ≫ f ≫ e'.hom
  let : IsClosedImmersion i.hom.hom.left := hi.2
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono f.hom.hom := mono_of_mono_fac
    (congrArg (fun b => b.hom.hom) hf)
  let : Mono d.hom.hom := by
    change Mono (e.inv.hom.hom ≫ f.hom.hom ≫ e'.hom.hom.hom)
    infer_instance
  have hle : Nat.card J ≤ Nat.card I := by
    have h := hi'.card_le_splitRank J e'
    rw [← hrank] at h
    exact_mod_cast h
  have hge : Nat.card I ≤ Nat.card J := splitTorus.card_le_card_of_mono I J d
  let : IsIso d := splitTorus.isIso_of_mono_of_card_eq I J d (le_antisymm hge hle)
  have hd : IsIso (e.inv ≫ f ≫ e'.hom) := inferInstanceAs (IsIso d)
  exact (isIso_comp_left_iff e.inv (f ≫ e'.hom)).mp hd |>
    (isIso_comp_right_iff f e'.hom).mp

/-- A closed integral split torus with maximal generic fibre has maximal residue
fibre when the integral ambient group is smooth affine and its generic fibre
is connected reductive. -/
theorem isMaximalSplitTorus_residue_of_generic
    {R k K : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [Field K] [Algebra R K]
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive ((baseChange (Spec.algebraMap R K)).obj G))
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (hiK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      ((baseChange (Spec.algebraMap R K)).map i)) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eK := (baseChange (Spec.algebraMap R K)).mapIso e ≪≫
    splitTorus.baseChangeIso (Spec.algebraMap R K) I
  let ek := (baseChange (Spec.algebraMap R k)).mapIso e ≪≫
    splitTorus.baseChangeIso (Spec.algebraMap R k) I
  have hrank := (maximalSplitTorusConjugacy K _ hG).2 _ _ hiK I eK
  have hik : IsSplitSubtorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i) :=
    ⟨(show IsSplitTorus T.toGrp from ⟨I, hI, ⟨e⟩⟩).baseChange _, hi.baseChange _⟩
  apply hik.isMaximal_of_card_eq_splitRank I ek
  apply le_antisymm (hik.card_le_splitRank I ek)
  rw [hrank]
  exact splitRank_residue_le hk G

end Langlands.GroupScheme
