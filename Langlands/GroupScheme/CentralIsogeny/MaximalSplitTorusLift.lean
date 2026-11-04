import Langlands.GroupScheme.Torus.FiniteHomRigidity
import Langlands.GroupScheme.CentralIsogeny.SplitParametrization
import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Rational.CentralIsogenyMaximalSplitTorusLiftStatement
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.Torus.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Lifting maximal split tori through a central isogeny, given a kernel exponent -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSplitTorusLift

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A surjective map of split tori between smooth affine groups is flat and locally of finite
presentation. -/
theorem flat_and_locallyOfFinitePresentation (hG : IsConnectedReductive G)
    (hH : IsConnectedReductive H) {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ G} {i : S.toGrp ⟶ H} (f : T ⟶ S)
    (hj : IsSplitSubtorus j) (hi : IsSplitSubtorus i)
    (hf : Surjective (CommGroupScheme.groupHom f).hom.hom.left) :
    Flat (CommGroupScheme.groupHom f).hom.hom.left ∧
      LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left := by
  let φ := CommGroupScheme.groupHom f
  have : Smooth G.X.hom := hG.smooth
  have : Smooth H.X.hom := hH.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsClosedImmersion j.hom.hom.left := hj.2
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have : LocallyOfFiniteType T.toGrp.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType S.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom T.toGrp.X.hom := IsClosedSubgroup.isAffineHom hj.2
  have : IsAffineHom S.toGrp.X.hom := IsClosedSubgroup.isAffineHom hi.2
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  have : IsLocallyNoetherian S.toGrp.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian S.toGrp.X.hom
  have : IsIntegral S.toGrp.X.left := hi.1.isIntegral
  have : LocallyOfFiniteType φ.hom.hom.left := by
    have : LocallyOfFiniteType (φ.hom.hom.left ≫ S.toGrp.X.hom) := by
      rw [Over.w φ.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp φ.hom.hom.left S.toGrp.X.hom
  have : Surjective φ.hom.hom.left := hf
  have : Flat φ.hom.hom.left := DominantHomFlat.flat_of_isDominant φ
  exact ⟨inferInstance, inferInstance⟩

/-- **Maximality.** Let `π` be a finite homomorphism of connected reductive groups, `i` a
maximal split torus of `H` and `j` a split subtorus of `G`. If a surjective `f` satisfies
`j ≫ π = f ≫ i`, then `j` is a maximal split torus of `G`. -/
theorem isMaximalSplitTorus_of_surjective (hG : IsConnectedReductive G)
    (hH : IsConnectedReductive H) (π : G ⟶ H) [IsFinite π.hom.hom.left]
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (i : S.toGrp ⟶ H) (f : T ⟶ S)
    (hj : IsSplitSubtorus j) (hi : IsMaximalSplitTorus i)
    (hf : Surjective (CommGroupScheme.groupHom f).hom.hom.left)
    (hcomm : j ≫ π = CommGroupScheme.groupHom f ≫ i) :
    IsMaximalSplitTorus j := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hH.isAffineHom
  let g := CommGroupScheme.groupHom f
  have : Surjective g.hom.hom.left := hf
  have : IsIntegral S.toGrp.X.left := hi.1.1.isIntegral
  have : IsSchemeTheoreticallyDominant g.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  refine ⟨hj, ?_⟩
  intro M m hm a ha
  obtain ⟨Z, p, z, hz, hp, -, -⟩ := hm.1.exists_dominant_factor_isSplitSubtorus (m ≫ π)
  have : IsClosedImmersion z.hom.hom.left := hz.2
  have he : g.hom.hom ≫ i.hom.hom = (a ≫ p).hom.hom ≫ z.hom.hom := by
    change (g ≫ i).hom.hom = ((a ≫ p) ≫ z).hom.hom
    rw [Category.assoc, hp, ← Category.assoc, ha, hcomm]
  obtain ⟨s, hs⟩ := exists_over_factor_of_schematic_precomp
    z.hom.hom g.hom.hom i.hom.hom (a ≫ p).hom.hom he
  let hzrep : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range z := by
    intro U x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨t ≫ s, by rw [Category.assoc, hs]⟩
  let b := hzrep.factorHom i hle
  have hb : b ≫ z = i := hzrep.factorHom_comp i hle
  have : IsIso b := hi.2 Z z hz b hb
  let q : M.toGrp ⟶ S.toGrp := p ≫ inv b
  have hq : q ≫ i = m ≫ π := by
    dsimp [q]
    rw [← hb, Category.assoc, IsIso.inv_hom_id_assoc, hp]
  have : IsClosedImmersion i.hom.hom.left := hi.1.2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have haq : a ≫ q = g := by
    apply Grp.hom_ext
    apply (cancel_mono i.hom.hom).mp
    change ((a ≫ q) ≫ i).hom.hom = (g ≫ i).hom.hom
    rw [Category.assoc, hq, ← Category.assoc, ha, hcomm]
  have : IsClosedImmersion m.hom.hom.left := hm.2
  have : IsFinite q.hom.hom.left := by
    have heq : q.hom.hom.left ≫ i.hom.hom.left = m.hom.hom.left ≫ π.hom.hom.left :=
      congrArg (fun t => t.hom.hom.left) hq
    have : IsFinite (q.hom.hom.left ≫ i.hom.hom.left) := by
      rw [heq]
      infer_instance
    exact IsFinite.of_comp _ i.hom.hom.left
  have hac : IsClosedSubgroup a := IsClosedSubgroup.of_comp hm.2 (by rw [ha]; exact hj.2)
  have : IsClosedImmersion a.hom.hom.left := hac
  have : IsAffineHom M.toGrp.X.hom := IsClosedSubgroup.isAffineHom hm.2
  have : IsAffineHom S.toGrp.X.hom := IsClosedSubgroup.isAffineHom hi.1.2
  have : IsAffine M.toGrp.X.left := isAffine_of_isAffineHom M.toGrp.X.hom
  have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  have : IsIntegral M.toGrp.X.left := hm.1.isIntegral
  have : IsSchemeTheoreticallyDominant (a.hom.hom.left ≫ q.hom.hom.left) := by
    change IsSchemeTheoreticallyDominant (a ≫ q).hom.hom.left
    rw [haq]
    infer_instance
  have : IsIso a.hom.hom.left :=
    isIso_of_closedImmersion_finite_comp_schematic a.hom.hom.left q.hom.hom.left
  have : IsIso a.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp (show IsIso a.hom.hom.left from inferInstance)
  have : IsIso a.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp (show IsIso a.hom.hom from inferInstance)
  exact (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp (show IsIso a.hom from inferInstance)

/-- **Lift with a kernel exponent.** Let `π` be a central isogeny of connected reductive groups
over a field whose kernel is killed by `N > 0`. Every maximal split torus `i : S ⟶ H` admits a
maximal split torus `j : T ⟶ G` and a flat, surjective homomorphism `f : T ⟶ S`, locally of
finite presentation, with `j ≫ π = f ≫ i`. -/
theorem exists_lift_of_kernel_pow_eq_one (hG : IsConnectedReductive G)
    (hH : IsConnectedReductive H) {π : G ⟶ H} (hπ : IsCentralIsogeny π)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ H}
    (hi : IsMaximalSplitTorus i) {N : ℕ} (hN0 : 0 < N)
    (hN : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (kernel π).X), x ^ N = 1) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G) (f : T ⟶ S),
      IsMaximalSplitTorus j ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i ∧
        Flat (CommGroupScheme.groupHom f).hom.hom.left ∧
        Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left := by
  obtain ⟨Φ, hΦ⟩ := hπ.exists_comp_eq_multiplication_comp i hN
  let b : S ⟶ S := Additive.ofMul (multiplication S.toGrp (2 * N : ℕ))
  have hb : Surjective (CommGroupScheme.groupHom b).hom.hom.left :=
    (hi.1.1.flat_and_surjective_multiplication (by omega)).2
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsFinite π.hom.hom.left := hπ.isFinite
  obtain ⟨T, j, f, hj, hf, hcomm⟩ := exists_splitSubtorus_lift_of_surjective_splitParametrization π Φ b i hi.1.1 hi.1.2 hb hΦ
  obtain ⟨hflat, hlfp⟩ := flat_and_locallyOfFinitePresentation hG hH f hj hi.1 hf
  exact ⟨T, j, f, isMaximalSplitTorus_of_surjective hG hH π j i f hj hi hf hcomm, hcomm,
    hflat, hf, hlfp⟩

/-- The target statement follows once every central isogeny of connected reductive groups
over a field has a kernel killed by some positive integer. -/
theorem statement_of_kernel_exponent
    (hexp : ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → IsConnectedReductive H → ∀ (π : G ⟶ H), IsCentralIsogeny π →
        ∃ N : ℕ, 0 < N ∧
          ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (kernel π).X), x ^ N = 1) :
    CentralIsogenyMaximalSplitTorusLiftStatement.{u} := by
  intro k _ G H hG hH π hπ S i hi
  obtain ⟨N, hN0, hN⟩ := hexp k G H hG hH π hπ
  exact exists_lift_of_kernel_pow_eq_one hG hH hπ hi hN0 hN

end Langlands.GroupScheme.CentralSplitTorusLift
