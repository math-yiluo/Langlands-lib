import Langlands.GroupScheme.SimplyConnected.CoverPreimageCharacters
import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Torus.FiniteHomRigidity
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Derived subgroups of the preimage of a subgroup in a central cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoverPreimage

section General

variable {S : Scheme.{u}}

/-- Flatness together with surjectivity, as a single morphism property. -/
abbrev flatSurjectiveProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @Surjective

/-- Central factors do not contribute to a commutator. -/
theorem commutator_central_mul {Γ : Type*} [Group Γ] (a b c d : Γ) (ha : ∀ y, Commute a y)
    (hc : ∀ y, Commute c y) :
    a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = b * d * b⁻¹ * d⁻¹ := by
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * (b * c * d * b⁻¹) * a⁻¹ * (d⁻¹ * c⁻¹) := by
        group
    _ = b * c * d * b⁻¹ * (d⁻¹ * c⁻¹) := by rw [(ha _).eq, mul_inv_cancel_right]
    _ = c * (b * d * b⁻¹ * d⁻¹) * c⁻¹ := by
        rw [show b * c = c * b from (hc b).eq.symm]
        group
    _ = b * d * b⁻¹ * d⁻¹ := by rw [(hc _).eq, mul_inv_cancel_right]

/-- Every homomorphism carries the derived subgroup into the derived subgroup. -/
theorem range_derived_comp_le {H G DH DG : GroupScheme S} (φ : H ⟶ G) {dH : DH ⟶ H}
    (hdH : IsDerivedSubgroup dH) {dG : DG ⟶ G} (hdG : IsDerivedSubgroup dG) :
    SubgroupFunctor.range (dH ≫ φ) ≤ SubgroupFunctor.range dG := by
  have hrep := hdG.isRepresentedBy.comap_subgroupIntersectionFst hdG.1 φ
  have hcl : IsClosedSubgroup (subgroupIntersectionFst φ dG) :=
    isClosedSubgroup_subgroupIntersectionFst φ hdG.1
  have hcomm : (SubgroupFunctor.range (subgroupIntersectionFst φ dG)).ContainsCommutators := by
    rw [hrep.2]
    intro T x y
    rw [SubgroupFunctor.mem_comap, MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, GrpObj.inv_comp]
    exact derivedSubgroup_containsCommutators G T _ _
  have hle := hdH.range_le _ hcl hcomm
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy := hle T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  rw [hrep.2, SubgroupFunctor.mem_comap, ← hdG.2] at hy
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact hy

end General

section Field

variable {k : Type u} [Field k]

/-- A smooth connected affine group over a field is integral. -/
theorem isIntegral_of_smooth_connected (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] : IsIntegral H.X.left := by
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : IrreducibleSpace H.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.X.hom
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ H.X.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A group scheme over a field has a point. -/
theorem nonempty_groupScheme (H : GroupScheme (Spec (CommRingCat.of k))) :
    Nonempty H.X.left :=
  ⟨(η[H.X]).left.base (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))⟩

/-- If `a ≫ q` and `q` are central isogenies between smooth connected affine groups, then so is
`a`. -/
theorem isCentralIsogeny_of_comp {CM D' DM : GroupScheme (Spec (CommRingCat.of k))}
    (a : CM ⟶ D') (q : D' ⟶ DM) (hq : IsCentralIsogeny q) (haq : IsCentralIsogeny (a ≫ q))
    [Smooth CM.X.hom] [IsAffineHom CM.X.hom] [ConnectedSpace CM.X.left]
    [Smooth D'.X.hom] [IsAffineHom D'.X.hom] [ConnectedSpace D'.X.left]
    [Smooth DM.X.hom] [IsAffineHom DM.X.hom] :
    IsCentralIsogeny a := by
  have : IsFinite q.hom.hom.left := hq.isFinite
  have : IsFinite (a.hom.hom.left ≫ q.hom.hom.left) := haq.isFinite
  have : IsFinite a.hom.hom.left := IsFinite.of_comp _ q.hom.hom.left
  obtain ⟨I, inc, fac, hinc, hfac, hf, hs, hqc, hl, -, -, -⟩ := HomImage.exists_image a
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Surjective (a.hom.hom.left ≫ q.hom.hom.left) := haq.surjective
  have hcomp : a.hom.hom.left = fac.hom.hom.left ≫ inc.hom.hom.left := by
    rw [← hfac]
    rfl
  have : Surjective (fac.hom.hom.left ≫ inc.hom.hom.left ≫ q.hom.hom.left) := by
    rw [← Category.assoc, ← hcomp]
    infer_instance
  have : Surjective (inc.hom.hom.left ≫ q.hom.hom.left) :=
    Surjective.of_comp fac.hom.hom.left _
  have : IsReduced DM.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ DM.X.hom
  have : IsSchemeTheoreticallyDominant (inc.hom.hom.left ≫ q.hom.hom.left) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsAffine D'.X.left := isAffine_of_isAffineHom D'.X.hom
  have : IsAffine DM.X.left := isAffine_of_isAffineHom DM.X.hom
  have : IsIntegral D'.X.left := isIntegral_of_smooth_connected D'
  have : Nonempty DM.X.left := nonempty_groupScheme DM
  have : IsIso inc.hom.hom.left :=
    isIso_of_closedImmersion_finite_comp_schematic inc.hom.hom.left q.hom.hom.left
  have : Flat fac.hom.hom.left := hf
  have : Surjective fac.hom.hom.left := hs
  have : LocallyOfFinitePresentation fac.hom.hom.left := hl
  refine ⟨⟨inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · rw [hcomp]
    infer_instance
  · rw [hcomp]
    infer_instance
  · rw [hcomp]
    infer_instance
  · apply (isCentral_kernelι_iff a).mpr
    intro T x hx
    apply haq.mem_center_of_comp_eq_one
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]

variable {G D C M : GroupScheme (Spec (CommRingCat.of k))}
  {Z : CommGroupScheme (Spec (CommRingCat.of k))}

set_option backward.isDefEq.respectTransparency false in
/-- The restriction to derived subgroups of the projection from the preimage `C ×_G M`
to `M` is a central isogeny onto the derived subgroup of `M`. -/
theorem isCentralIsogeny_derivedLift (hG : IsConnectedReductive G) {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) {π : C ⟶ D} (hπ : IsCentralIsogeny π) {i : Z.toGrp ⟶ G}
    (hic : IsCentral i) (hm : IsCentralFppfCover (centralProduct i d hic)) {j : M ⟶ G}
    (hj : IsClosedSubgroup j) (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (hM : IsConnectedReductive M) (hM' : IsConnectedReductive (subgroupIntersection (π ≫ d) j))
    {DM : GroupScheme (Spec (CommRingCat.of k))} {dM : DM ⟶ M} (hdM : IsDerivedSubgroup dM)
    {D' : GroupScheme (Spec (CommRingCat.of k))} {d' : D' ⟶ subgroupIntersection (π ≫ d) j}
    (hd' : IsDerivedSubgroup d') :
    IsCentralIsogeny (hdM.isRepresentedBy.liftOfLE (d' ≫ subgroupIntersectionSnd (π ≫ d) j)
      ((range_derived_comp_le _ hd' hdM).trans hdM.2.le)) := by
  let M' := subgroupIntersection (π ≫ d) j
  let j' := subgroupIntersectionFst (π ≫ d) j
  let p := subgroupIntersectionSnd (π ≫ d) j
  let q := hdM.isRepresentedBy.liftOfLE (d' ≫ p) ((range_derived_comp_le _ hd' hdM).trans hdM.2.le)
  have hq : q ≫ dM = d' ≫ p := SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _
  -- instances
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth M.X.hom := hM.smooth
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion dM.hom.hom.left := hdM.1
  have : Mono dM.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion d'.hom.hom.left := hd'.1
  have : Mono d'.hom.hom := Over.mono_of_mono_left _
  have : Mono j'.hom.hom := (subgroupIntersection_isPullback (π ≫ d) j).mono_fst_of_mono
  obtain ⟨hD's, hD'c, hD'a⟩ := derivedSubgroup_smooth_connected_affine hM' hd'
  obtain ⟨hDMs, hDMc, hDMa⟩ := derivedSubgroup_smooth_connected_affine hM hdM
  have : IsFinite π.hom.hom.left := hπ.isFinite
  -- finiteness
  have hpfin : IsFinite p.hom.hom.left := by
    have : IsFinite (π ≫ d).hom.hom.left := by
      change IsFinite (π.hom.hom.left ≫ d.hom.hom.left)
      infer_instance
    exact MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme (π ≫ d) j)
      this
  have : IsFinite (q.hom.hom.left ≫ dM.hom.hom.left) := by
    change IsFinite (q ≫ dM).hom.hom.left
    rw [hq]
    change IsFinite (d'.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have hqfin : IsFinite q.hom.hom.left := IsFinite.of_comp _ dM.hom.hom.left
  -- image of q
  obtain ⟨I, inc, fac, hinc, hfac, hf, hs, hqc, hl, -, -, -⟩ := HomImage.exists_image q
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  -- the commutator morphism of `M` factors through the image
  let e := toDerivedPart π d j
  have he := isCentralFppfCover_toDerivedPart (isCentralFppfCover_of_isCentralIsogeny hπ) d (j := j)
  let hicM := isCentral_of_comp_mono hic j iM hiM
  let ρ := restrictedProduct d j iM hicM
  have hρ := isCentralFppfCover_restrictedProduct i d hic hm j iM hiM
  let Ψ : Z.toGrp ⊗ M' ⟶ M := (Z.toGrp ◁ e) ≫ ρ
  have hΨ : ∀ {V : Over (Spec (CommRingCat.of k))} (w : V ⟶ (Z.toGrp ⊗ M').X),
      w ≫ Ψ.hom.hom = (w ≫ fst Z.X M'.X ≫ iM.hom.hom) * (w ≫ snd Z.X M'.X ≫ p.hom.hom) := by
    intro V w
    have hw : Ψ.hom.hom = (Z.X ◁ e.hom.hom) ≫
        (centralProduct iM (subgroupIntersectionSnd d j) hicM).hom.hom := rfl
    rw [hw, ← Category.assoc, comp_centralProduct]
    simp only [Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc]
    rw [← Grp.comp_hom_hom e (subgroupIntersectionSnd d j), toDerivedPart_snd]
  have := he.flat
  have := he.surjective
  have := hρ.flat
  have := hρ.surjective
  have hΨfs : flatSurjectiveProperty Ψ.hom.hom.left := by
    have hw : flatSurjectiveProperty
        (Z.X ◁ e.hom.hom).left :=
      MorphismProperty.pullbackMap (P := flatSurjectiveProperty)
        (by change flatSurjectiveProperty (𝟙 Z.X.left)
            exact ⟨inferInstance, inferInstance⟩)
        ⟨inferInstance, inferInstance⟩ (by simp) (Over.w e.hom.hom).symm
    obtain ⟨hw1, hw2⟩ := hw
    have : Flat (Z.X ◁ e.hom.hom).left := hw1
    have : Surjective (Z.X ◁ e.hom.hom).left := hw2
    change flatSurjectiveProperty
      ((Z.X ◁ e.hom.hom).left ≫ ρ.hom.hom.left)
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨hΨf, hΨs⟩ := hΨfs
  have : Flat Ψ.hom.hom.left := hΨf
  have : Surjective Ψ.hom.hom.left := hΨs
  let w := Ψ.hom.hom ⊗ₘ Ψ.hom.hom
  have hwfs : flatSurjectiveProperty w.left :=
    MorphismProperty.pullbackMap (P := flatSurjectiveProperty)
      ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩
      (Over.w Ψ.hom.hom).symm (Over.w Ψ.hom.hom).symm
  obtain ⟨-, hws⟩ := hwfs
  have : Surjective w.left := hws
  have : Smooth (M.X ⊗ M.X).hom := smooth_tensor M.X M.X inferInstance inferInstance
  have : IsReduced (M.X ⊗ M.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
      (M.X ⊗ M.X).hom
  have : IsSchemeTheoreticallyDominant w.left := IsSchemeTheoreticallyDominant.of_isDominant _
  let c : M.X ⊗ M.X ⟶ M.X :=
    fst M.X M.X * snd M.X M.X * (fst M.X M.X)⁻¹ * (snd M.X M.X)⁻¹
  let W := (Z.toGrp ⊗ M').X ⊗ (Z.toGrp ⊗ M').X
  let m₁ : W ⟶ M'.X := fst _ _ ≫ snd Z.X M'.X
  let m₂ : W ⟶ M'.X := snd _ _ ≫ snd Z.X M'.X
  obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp
    (hd'.containsCommutators W m₁ m₂)
  have hwc : w ≫ c = u ≫ (fac ≫ inc ≫ dM).hom.hom := by
    have h1 : w ≫ fst M.X M.X = fst _ _ ≫ Ψ.hom.hom := tensorHom_fst _ _
    have h2 : w ≫ snd M.X M.X = snd _ _ ≫ Ψ.hom.hom := tensorHom_snd _ _
    have hcent : ∀ (r : W ⟶ (Z.toGrp ⊗ M').X) (y : W ⟶ M.X),
        Commute (r ≫ fst Z.X M'.X ≫ iM.hom.hom) y := by
      intro r y
      rw [← Category.assoc]
      exact commute_of_mem_center (hicM W _) y
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, h2, hΨ]
    rw [commutator_central_mul _ _ _ _ (hcent _) (hcent _)]
    rw [← Category.assoc fac inc dM, hfac, hq, Grp.comp_hom_hom, ← Category.assoc u, hu]
    simp only [m₁, m₂, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  have : IsClosedImmersion (inc ≫ dM).hom.hom.left := by
    change IsClosedImmersion (inc.hom.hom.left ≫ dM.hom.hom.left)
    infer_instance
  have hwc' : (u ≫ fac.hom.hom) ≫ (inc ≫ dM).hom.hom = w ≫ c := by
    rw [hwc, Category.assoc, ← Grp.comp_hom_hom]
  obtain ⟨f', hf'⟩ := exists_lift_of_isSchemeTheoreticallyDominant
    (inc ≫ dM).hom.hom.left c.left w.left (u ≫ fac.hom.hom).left
    (congrArg (fun r => r.left) hwc')
  let f : M.X ⊗ M.X ⟶ I.X := Over.homMk f' (by
    rw [← Over.w inc.hom.hom, ← Over.w dM.hom.hom, ← Over.w c]
    change f' ≫ (inc ≫ dM).hom.hom.left ≫ M.X.hom = c.left ≫ M.X.hom
    rw [← Category.assoc, hf'])
  have hfc : f ≫ (inc ≫ dM).hom.hom = c := Over.OverMorphism.ext hf'
  have hcomm : (SubgroupFunctor.range (inc ≫ dM)).ContainsCommutators := by
    intro T x y
    refine SubgroupFunctor.mem_range.mpr ⟨lift x y ≫ f, ?_⟩
    rw [Category.assoc, hfc]
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  have hincl : IsClosedSubgroup (inc ≫ dM) := by
    change IsClosedImmersion (inc.hom.hom.left ≫ dM.hom.hom.left)
    infer_instance
  have hle := hdM.range_le _ hincl hcomm
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    (hle DM.X (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩))
  have hyinc : y ≫ inc.hom.hom = 𝟙 _ := by
    apply (cancel_mono dM.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hy, Category.id_comp]
  have : IsSplitEpi inc.hom.hom := ⟨⟨y, hyinc⟩⟩
  have : IsIso inc.hom.hom := isIso_of_mono_of_isSplitEpi _
  have : IsIso inc.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map inc.hom.hom))
  have hqcomp : q.hom.hom.left = fac.hom.hom.left ≫ inc.hom.hom.left := by
    rw [← hfac]
    rfl
  have : Flat fac.hom.hom.left := hf
  have : Surjective fac.hom.hom.left := hs
  have : LocallyOfFinitePresentation fac.hom.hom.left := hl
  refine ⟨⟨hqfin, ?_, ?_⟩, ?_, ?_⟩
  · rw [hqcomp]
    infer_instance
  · rw [hqcomp]
    infer_instance
  · rw [hqcomp]
    infer_instance
  · apply (isCentral_kernelι_iff q).mpr
    intro T x hx
    have hdp : d'.hom.hom ≫ p.hom.hom = q.hom.hom ≫ dM.hom.hom := by
      rw [← Grp.comp_hom_hom, ← hq, Grp.comp_hom_hom]
    have h1 : x ≫ d'.hom.hom ≫ p.hom.hom = 1 := by
      rw [hdp, ← Category.assoc, hx, MonObj.one_comp]
    have hc : j'.hom.hom ≫ π.hom.hom ≫ d.hom.hom = p.hom.hom ≫ j.hom.hom := by
      have := congrArg (fun r => r.hom.hom) (subgroupIntersection_condition (π ≫ d) j)
      simpa only [Grp.comp_hom_hom] using this
    have h2 : (x ≫ d'.hom.hom ≫ j'.hom.hom) ≫ π.hom.hom = 1 := by
      apply (cancel_mono d.hom.hom).mp
      rw [MonObj.one_comp]
      simp only [Category.assoc]
      rw [hc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1, MonObj.one_comp]
    have hcen := hπ.mem_center_of_comp_eq_one h2
    intro T' a z
    change (a ≫ x) * z = z * (a ≫ x)
    apply (cancel_mono (d'.hom.hom ≫ j'.hom.hom)).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have := hcen T' a (z ≫ d'.hom.hom ≫ j'.hom.hom)
    simpa only [Category.assoc] using this.eq

/-- The derived subgroup of the preimage `C ×_G M` lifts to the simply connected cover of the
derived subgroup of `M`, provided it is simply connected. -/
theorem exists_derivedSubgroup_lift (hG : IsConnectedReductive G) {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) {π : C ⟶ D} (hπ : IsCentralIsogeny π) {i : Z.toGrp ⟶ G}
    (hic : IsCentral i) (hm : IsCentralFppfCover (centralProduct i d hic)) {j : M ⟶ G}
    (hj : IsClosedSubgroup j) (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (hM' : IsConnectedReductive (subgroupIntersection (π ≫ d) j))
    {DM CM : GroupScheme (Spec (CommRingCat.of k))} {dM : DM ⟶ M} {πM : CM ⟶ DM}
    (hcov : IsSimplyConnectedDerivedCover dM πM)
    {D' : GroupScheme (Spec (CommRingCat.of k))} {d' : D' ⟶ subgroupIntersection (π ≫ d) j}
    (hd' : IsDerivedSubgroup d') (hD'sc : IsSimplyConnected D') :
    ∃ b : D' ⟶ CM, b ≫ πM ≫ dM = d' ≫ subgroupIntersectionSnd (π ≫ d) j := by
  have hdM := hcov.isDerivedSubgroup
  have hM := hcov.isConnectedReductive
  have hq := isCentralIsogeny_derivedLift hG hd hπ hic hm hj iM hiM hM hM' hdM hd'
  let q := hdM.isRepresentedBy.liftOfLE (d' ≫ subgroupIntersectionSnd (π ≫ d) j)
    ((range_derived_comp_le _ hd' hdM).trans hdM.2.le)
  have hqc : q ≫ dM = d' ≫ subgroupIntersectionSnd (π ≫ d) j :=
    SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _
  have hcover := hcov.isSimplyConnectedCover
  let a := hcover.lift hD'sc.isSemisimple hq
  have ha : a ≫ q = πM := hcover.lift_comp hD'sc.isSemisimple hq
  have hCM := hcover.isSimplyConnected.isSemisimple.isConnectedReductive
  have hD' := hD'sc.isSemisimple.isConnectedReductive
  have hDM := hcover.isSemisimple.isConnectedReductive
  have : Smooth CM.X.hom := hCM.smooth
  have : IsAffineHom CM.X.hom := hCM.isAffineHom
  have : ConnectedSpace CM.X.left := hCM.connectedSpace
  have : Smooth D'.X.hom := hD'.smooth
  have : IsAffineHom D'.X.hom := hD'.isAffineHom
  have : ConnectedSpace D'.X.left := hD'.connectedSpace
  have : Smooth DM.X.hom := hDM.smooth
  have : IsAffineHom DM.X.hom := hDM.isAffineHom
  have haC : IsCentralIsogeny a :=
    isCentralIsogeny_of_comp a q hq (by rw [ha]; exact hcover.isCentralIsogeny)
  have : IsIso a := hD'sc.central_isogeny_isIso CM a hcover.isSimplyConnected.isSemisimple haC
  refine ⟨inv a, ?_⟩
  rw [← ha, Category.assoc, IsIso.inv_hom_id_assoc, hqc]

end Field

end Langlands.GroupScheme.CoverPreimage
