import Langlands.GroupScheme.Torus.HenselianSplitRank
import Langlands.GroupScheme.HomScheme.HenselianSplitSourceLifting
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Descent.SemilinearDatum
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Exact lifting of closed split subgroups over Henselian rings -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A relative torus over a local ring is smooth. -/
theorem RelativeTorus.IsTorus.smooth_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {T : GroupScheme (Spec (CommRingCat.of R))} (hT : RelativeTorus.IsTorus T) :
    Smooth T.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint R)
  obtain ⟨j, z, hz⟩ := (𝒰.X i).affineCover.exists_eq y
  let p := (𝒰.X i).affineCover.f j ≫ 𝒰.f i
  let : Etale (𝒰.f i) := 𝒰.map_prop i
  let : Etale p := by dsimp [p]; infer_instance
  have hp : Surjective p := by
    constructor
    intro x
    apply (IsLocalRing.specializes_closedPoint (R := R) x).mem_open
      (p.isOpenMap.isOpen_range)
    exact ⟨z, by simpa only [p, Scheme.Hom.comp_apply, hz] using hy⟩
  have hs : IsSplitTorus ((GroupScheme.baseChange p).obj T) := by
    exact IsSplitTorus.of_iso
      (baseChangeCompIso (𝒰.f i) ((𝒰.X i).affineCover.f j) T)
      ((h𝒰 i).baseChange _)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := T.X.hom) (g := p) ⟨⟨hp, inferInstance⟩, inferInstance⟩ hs.smooth


/-- A closed homomorphism from the residue of a given split torus lifts with
its actual residue map unchanged. -/
theorem exists_closed_splitHom_lift
    {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    (H G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : IsSplitTorus H)
    (i₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶
      (baseChange (Spec.algebraMap R k)).obj G)
    (hi₀ : IsClosedSubgroup i₀) :
    ∃ i : H ⟶ G, IsClosedSubgroup i ∧ (baseChange (Spec.algebraMap R k)).map i = i₀ := by
  let c := Spec.algebraMap R k
  obtain ⟨M, j, hj, hM⟩ :=
    HomScheme.smoothSplitSourceRepresentability _ H G hH
  obtain ⟨x, hx⟩ := (hj (Over.mk c)).surjective i₀
  change HomScheme.evaluate x j = i₀ at hx
  have hxclosed : IsClosedImmersion ((baseChange x.left).map j).hom.hom.left := by
    apply (HomScheme.isClosedImmersion_evaluate_iff x j).mp
    rw [hx]
    exact hi₀
  have : IsAffineHom ((baseChange M.hom).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom M.hom)
    exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  obtain ⟨V, q, hq, bx, hbx, hqclosed⟩ :=
    exists_open_isClosedImmersion_baseChange (hH.baseChange M.hom) j k x.left hxclosed
  let v : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ M.hom)
  let vM : v ⟶ M := Over.homMk q rfl
  let jv := HomScheme.evaluate vM j
  have hjv : IsClosedSubgroup jv :=
    (HomScheme.isClosedImmersion_evaluate_iff vM j).mpr hqclosed
  have hvSmooth : Smooth v.hom := by dsimp [v]; infer_instance
  have hbxc : bx ≫ v.hom = c := by
    dsimp [v]
    rw [← Category.assoc, hbx]
    exact Over.w x
  obtain ⟨σ, hσ, hσbx⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk v.hom bx hbxc
  let s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ v := Over.homMk σ hσ
  let b : Over.mk c ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk c (Category.comp_id _)
  let i := (baseChangeIdIso H).inv ≫ HomScheme.evaluate s jv ≫
    (baseChangeIdIso G).hom
  have hsclosed : IsClosedSubgroup (HomScheme.evaluate s jv) :=
    (HomScheme.isClosedImmersion_evaluate_iff s jv).mpr (hjv.baseChange σ)
  have hi : IsClosedSubgroup i :=
    (hsclosed.comp_iso (baseChangeIdIso G)).iso_comp (baseChangeIdIso H).symm
  refine ⟨i, hi, ?_⟩
  have heval : HomScheme.evaluate b (HomScheme.evaluate s jv) =
      (baseChange c).map i :=
    HomScheme.evaluate_identityBase (HomScheme.evaluate s jv) (Over.mk c)
  rw [← heval]
  rw [← HomScheme.evaluate_comp, ← HomScheme.evaluate_comp]
  have hbs : (b ≫ s) ≫ vM = x := by
    apply Over.OverMorphism.ext
    change (c ≫ σ) ≫ q = x.left
    rw [hσbx, hbx]
  rw [hbs]
  exact hx

/-- A certified choice of a closed split-source homomorphism with the prescribed
residue homomorphism. -/
def henselianClosedSplitHomLift
    {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    (H G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : IsSplitTorus H)
    (i₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶
      (baseChange (Spec.algebraMap R k)).obj G)
    (hi₀ : IsClosedSubgroup i₀) :
    {i : H ⟶ G // IsClosedSubgroup i ∧ (baseChange (Spec.algebraMap R k)).map i = i₀} :=
  ⟨(exists_closed_splitHom_lift hk H G hH i₀ hi₀).choose,
    (exists_closed_splitHom_lift hk H G hH i₀ hi₀).choose_spec⟩

end Langlands.GroupScheme
