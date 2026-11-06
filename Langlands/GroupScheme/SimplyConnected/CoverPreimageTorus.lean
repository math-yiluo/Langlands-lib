import Langlands.GroupScheme.SimplyConnected.CoverPreimageCharacters
import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralizer
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageProof
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # A maximal torus of the preimage of a subgroup in a central cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoverPreimage

variable {k : Type u} [Field k] {G D C M : GroupScheme (Spec (CommRingCat.of k))}
  {Z : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Splitness of a torus passes to the target of a flat surjective homomorphism after every
field extension. -/
theorem isSplitTorus_baseChange_of_flat_surjective {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT' : IsTorus T'.toGrp) (pr : T.toGrp ⟶ T'.toGrp) [Flat pr.hom.hom.left]
    [Surjective pr.hom.hom.left] (E : Type u) [Field E] [Algebra k E]
    (hs : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T.toGrp)) :
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T'.toGrp) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E))
  have hp := (baseChange_map_isPullback b pr).flip
  have : Surjective ((GroupScheme.baseChange b).map pr).hom.hom.left :=
    MorphismProperty.of_isPullback hp inferInstance
  have hT'E : IsTorus ((GroupScheme.baseChange b).obj T'.toGrp) := hT'.baseChange
  have : Smooth ((GroupScheme.baseChange b).obj T'.toGrp).X.hom := hT'E.smooth
  have : IsAffine ((GroupScheme.baseChange b).obj T'.toGrp).X.left :=
    SplittingAssembly.isAffine_of_isTorus _ hT'E
  have : IsAffineHom ((GroupScheme.baseChange b).obj T'.toGrp).X.hom := inferInstance
  have : IsReduced ((GroupScheme.baseChange b).obj T'.toGrp).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field E _
      ((GroupScheme.baseChange b).obj T'.toGrp).X.hom
  exact hs.of_schematicallyDominant_hom ((GroupScheme.baseChange b).map pr)
    (IsSchemeTheoreticallyDominant.of_isDominant _)

/-- The preimage `C ×_G M` contains a maximal torus mapping into a given maximal torus of `M`
and split over every field extension splitting it. -/
theorem exists_maximalTorus_preimage {d : D ⟶ G} [Mono d.hom.hom] {π : C ⟶ D}
    (hπ : IsCentralIsogeny π) {i : Z.toGrp ⟶ G} (hic : IsCentral i)
    (hm : IsCentralFppfCover (centralProduct i d hic)) {j : M ⟶ G} [Mono j.hom.hom]
    (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i) (hZ : IsTorus Z.toGrp)
    (hM : IsConnectedReductive M) (hM' : IsConnectedReductive (subgroupIntersection (π ≫ d) j))
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ M} (ht : IsMaximalTorus t) :
    ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k)))
      (t' : T'.toGrp ⟶ subgroupIntersection (π ≫ d) j) (g : T' ⟶ T),
      IsMaximalTorus t' ∧
      t' ≫ subgroupIntersectionSnd (π ≫ d) j = CommGroupScheme.groupHom g ≫ t ∧
      ∀ (E : Type u) [Field E] [Algebra k E],
        IsSplitTorus ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T.toGrp) →
          IsSplitTorus ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T'.toGrp) := by
  let M' := subgroupIntersection (π ≫ d) j
  let p := subgroupIntersectionSnd (π ≫ d) j
  let MD := subgroupIntersection d j
  let md := subgroupIntersectionSnd d j
  have : Smooth M.X.hom := hM.smooth
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : Smooth M'.X.hom := hM'.smooth
  have : IsAffineHom M'.X.hom := hM'.isAffineHom
  have hT : IsTorus T.toGrp := ht.1
  have : IsClosedImmersion t.hom.hom.left := ht.2.1
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  have : IsAffineHom T.X.hom := inferInstance
  have : Smooth T.X.hom := hT.smooth
  have : ConnectedSpace T.X.left := hT.connectedSpace
  have : GeometricallyIntegral T.X.hom :=
    smoothConnectedAffineGeometry.1 k T.toGrp inferInstance inferInstance inferInstance
  -- the central torus lies in `T`
  let hicM := isCentral_of_comp_mono hic j iM hiM
  obtain ⟨zt, hzt⟩ := IsMaximalTorus.exists_factor_of_commute ht hZ iM (hicM.commute_values t)
  -- power lifts of `t` through `Z × (D ×_G M) ⟶ M` and `C ×_G M ⟶ D ×_G M`
  let e := toDerivedPart π d j
  have he := isCentralFppfCover_toDerivedPart (isCentralFppfCover_of_isCentralIsogeny hπ) d
    (j := j)
  let ρ := restrictedProduct d j iM hicM
  have hρ := isCentralFppfCover_restrictedProduct i d hic hm j iM hiM
  obtain ⟨N, hN, hNx⟩ := hρ.exponent
  obtain ⟨N₃, hN₃, hN₃x⟩ := he.exponent
  have := hρ.quasiCompact
  have := hρ.flat
  have := hρ.surjective
  obtain ⟨Φ, hΦ⟩ := CentralPowerLift.exists_comp_eq_multiplication_comp (π := ρ) t hρ.central hNx
  let Φ₂ : T.toGrp ⟶ MD := Φ ≫ snd Z.toGrp MD
  have := he.quasiCompact
  have := he.flat
  have := he.surjective
  obtain ⟨Φ', hΦ'⟩ := CentralPowerLift.exists_comp_eq_multiplication_comp (π := e) Φ₂ he.central
    hN₃x
  let n := 2 * N₃ * (2 * N)
  have hn : 0 < n := by positivity
  -- the basic identity
  have hstar : ∀ {U : Over (Spec (CommRingCat.of k))} (y : U ⟶ T.X),
      (y ^ n) ≫ t.hom.hom =
        ((y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫ fst Z.X MD.X) ≫
          iM.hom.hom) * (y ≫ Φ'.hom.hom ≫ p.hom.hom) := by
    intro U y
    have h1 : (y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom) ≫ ρ.hom.hom =
        (y ^ n) ≫ t.hom.hom := by
      rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom Φ ρ, hΦ, Grp.comp_hom_hom,
        ← Category.assoc, ← Category.assoc, points_multiplication, points_multiplication,
        zpow_natCast, zpow_natCast, ← pow_mul]
    have h3 : (y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom) ≫
        snd Z.X MD.X ≫ md.hom.hom = y ≫ Φ'.hom.hom ≫ p.hom.hom := by
      have hΦ'h : Φ'.hom.hom ≫ e.hom.hom =
          (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫ snd Z.X MD.X := by
        have := congrArg (fun r => r.hom.hom) hΦ'
        simpa only [Φ₂, Grp.comp_hom_hom, Grp.snd_hom_hom] using this
      have hp : e.hom.hom ≫ md.hom.hom = p.hom.hom := by
        rw [← Grp.comp_hom_hom, toDerivedPart_snd]
      rw [← hp, ← Category.assoc Φ'.hom.hom, hΦ'h]
      simp only [Category.assoc]
    have hρdef : ρ = centralProduct iM md hicM := rfl
    rw [← h1, hρdef, comp_centralProduct, h3]
    simp only [Category.assoc]
    rfl
  -- the torus `T'`
  have hT'torus := hT.isTorus_schematicImage Φ'
  let T' : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image Φ' with comm := hT'torus.isCommMonObj }
  let t' : T'.toGrp ⟶ M' := SchematicImage.inclusion Φ'
  let pr : T.toGrp ⟶ T'.toGrp := SchematicImage.projection Φ'
  have hpr : pr ≫ t' = Φ' := SchematicImage.projection_inclusion Φ'
  have : Flat pr.hom.hom.left := HomImage.flat_projection Φ'
  have : Surjective pr.hom.hom.left := HomImage.surjective_projection Φ'
  have ht'cl : IsClosedSubgroup t' :=
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion Φ').hom.hom.left)
  have : IsClosedImmersion t'.hom.hom.left := ht'cl
  have : Mono t'.hom.hom := Over.mono_of_mono_left _
  -- the map `g`
  have htrep : (SubgroupFunctor.range t).IsRepresentedBy t := ⟨inferInstance, rfl⟩
  have hle : SubgroupFunctor.range (t' ≫ p) ≤ SubgroupFunctor.range t := by
    rw [← SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant pr (t' ≫ p) t ht.2.1,
      ← Category.assoc, hpr]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hzi : ((y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫
        fst Z.X MD.X) ≫ zt.hom.hom) ≫ t.hom.hom =
        (y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫ fst Z.X MD.X) ≫
          iM.hom.hom := by
      rw [Category.assoc _ zt.hom.hom, ← Grp.comp_hom_hom, hzt]
    refine SubgroupFunctor.mem_range.mpr
      ⟨((y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫ fst Z.X MD.X) ≫
        zt.hom.hom)⁻¹ * y ^ n, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, hzi, hstar, inv_mul_cancel_left, Grp.comp_hom_hom]
  let g₀ := htrep.liftOfLE (t' ≫ p) hle
  have hg₀ : g₀ ≫ t = t' ≫ p := SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _
  refine ⟨T', t', Additive.ofMul g₀, ⟨hT'torus, ht'cl, ?_⟩, hg₀.symm,
    fun E _ _ hs => isSplitTorus_baseChange_of_flat_surjective hT'torus pr E hs⟩
  -- maximality
  intro T'' t'' f hT'' ht''cl hf
  have : IsClosedImmersion t''.hom.hom.left := ht''cl
  have : Mono t''.hom.hom := Over.mono_of_mono_left _
  have hΦ'f : Φ' = (pr ≫ f) ≫ t'' := by rw [Category.assoc, hf, hpr]
  -- `t'' ≫ p` commutes with `T`
  have hTn : torusCentralizer (multiplication T.toGrp n ≫ t) = torusCentralizer t := by
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have : Flat (multiplication T.toGrp n).hom.hom.left :=
      (hT.flat_and_surjective_multiplication hn').1
    have : Surjective (multiplication T.toGrp n).hom.hom.left :=
      (hT.flat_and_surjective_multiplication hn').2
    exact torusCentralizer_comp_of_fpqc (T₁ := T) (T₂ := T) _ t
  have hcomm6 : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T''.X) (y : U ⟶ T.X),
      Commute (x ≫ (t'' ≫ p).hom.hom) (y ≫ t.hom.hom) := by
    intro U x y
    have hmem : x ≫ (t'' ≫ p).hom.hom ∈ (torusCentralizer (multiplication T.toGrp n ≫ t)).carrier U := by
      intro V a s
      have hs : s ≫ (multiplication T.toGrp n ≫ t).hom.hom = (s ^ n) ≫ t.hom.hom := by
        rw [Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast]
      rw [hs, hstar]
      refine Commute.mul_right (commute_of_mem_center (hicM V _) _).symm ?_
      have hsΦ : s ≫ Φ'.hom.hom ≫ p.hom.hom = (s ≫ pr.hom.hom ≫ f.hom.hom) ≫ (t'' ≫ p).hom.hom := by
        rw [hΦ'f]
        simp only [Grp.comp_hom_hom, Category.assoc]
      rw [hsΦ, ← Category.assoc]
      exact (Commute.all (a ≫ x) (s ≫ pr.hom.hom ≫ f.hom.hom)).map
        (IsMonHom.monoidHom (t'' ≫ p).hom.hom V)
    rw [hTn] at hmem
    simpa only [Category.id_comp] using hmem U (𝟙 U) y
  obtain ⟨gam, hgam⟩ := IsMaximalTorus.exists_factor_of_commute ht hT'' (t'' ≫ p) hcomm6
  -- a power of `t''` factors through `t'`
  let K := N * N₃
  have hK : 0 < K := Nat.mul_pos hN hN₃
  have ht'rep : (SubgroupFunctor.range t').IsRepresentedBy t' := ⟨inferInstance, rfl⟩
  have hle' : SubgroupFunctor.range (multiplication T''.toGrp (n * K : ℕ) ≫ t'') ≤
      SubgroupFunctor.range t' := by
    intro U x hx
    obtain ⟨c, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let y := c ≫ gam.hom.hom
    let z := y ≫ (multiplication T.toGrp (2 * N₃ : ℕ)).hom.hom ≫ Φ.hom.hom ≫ fst Z.X MD.X
    let v := y ≫ pr.hom.hom ≫ f.hom.hom
    let w : U ⟶ M'.X := (c ^ n * v⁻¹) ≫ t''.hom.hom
    have hyt : y ≫ t.hom.hom = c ≫ t''.hom.hom ≫ p.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hgam, Grp.comp_hom_hom]
    have hst := hstar y
    rw [MonObj.pow_comp, hyt, ← MonObj.pow_comp, ← Category.assoc] at hst
    have hyΦ : y ≫ Φ'.hom.hom ≫ p.hom.hom = v ≫ t''.hom.hom ≫ p.hom.hom := by
      rw [hΦ'f]
      simp only [v, Grp.comp_hom_hom, Category.assoc]
    have hwp : w ≫ p.hom.hom = z ≫ iM.hom.hom := by
      simp only [w, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
      rw [← Category.assoc (c ^ n), hst, ← hyΦ, mul_inv_cancel_right]
    let κ : U ⟶ (Z.toGrp ⊗ MD).X := (productPointsEquiv Z.toGrp MD U).symm (z⁻¹, w ≫ e.hom.hom)
    have hκ1 : κ ≫ fst Z.X MD.X = z⁻¹ :=
      congrArg Prod.fst ((productPointsEquiv Z.toGrp MD U).apply_symm_apply (z⁻¹, w ≫ e.hom.hom))
    have hκ2 : κ ≫ snd Z.X MD.X = w ≫ e.hom.hom :=
      congrArg Prod.snd ((productPointsEquiv Z.toGrp MD U).apply_symm_apply (z⁻¹, w ≫ e.hom.hom))
    have hκρ : κ ≫ ρ.hom.hom = 1 := by
      have hρdef : ρ = centralProduct iM md hicM := rfl
      have hp : e.hom.hom ≫ md.hom.hom = p.hom.hom := by
        rw [← Grp.comp_hom_hom, toDerivedPart_snd]
      rw [hρdef, comp_centralProduct, ← Category.assoc κ (fst Z.X MD.X), hκ1,
        ← Category.assoc κ (snd Z.X MD.X), hκ2, GrpObj.inv_comp, Category.assoc w, hp, hwp,
        inv_mul_cancel]
    have hκN := hNx U κ hκρ
    have hweN : (w ^ N) ≫ e.hom.hom = 1 := by
      have := congrArg (fun r => r ≫ snd Z.X MD.X) hκN
      simp only [MonObj.pow_comp, MonObj.one_comp] at this
      rw [hκ2] at this
      rw [MonObj.pow_comp]
      exact this
    have hwK : w ^ K = 1 := by
      rw [pow_mul]
      exact hN₃x U _ hweN
    have hcv : (c ^ n * v⁻¹) ^ K = 1 := by
      apply (cancel_mono t''.hom.hom).mp
      rw [MonObj.pow_comp, MonObj.one_comp]
      exact hwK
    rw [mul_pow, inv_pow, mul_inv_eq_one, ← pow_mul] at hcv
    refine SubgroupFunctor.mem_range.mpr ⟨(y ≫ pr.hom.hom) ^ K, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast, hcv]
    simp only [v, ← MonObj.pow_comp, Category.assoc]
    rw [← Grp.comp_hom_hom f t'', hf]
  let ψ := ht'rep.liftOfLE _ hle'
  have hψ : ψ ≫ t' = multiplication T''.toGrp (n * K : ℕ) ≫ t'' :=
    SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _
  have hnK : ((n * K : ℕ) : ℤ) ≠ 0 := by
    have : 0 < n * K := Nat.mul_pos hn hK
    exact_mod_cast this.ne'
  obtain ⟨φ', hφ'⟩ := exists_factor_of_multiplication_comp hT'' hnK t' ht'cl t'' ψ hψ.symm
  refine ⟨φ', ?_, ?_⟩
  · apply Grp.hom_ext
    apply (cancel_mono t'.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hφ', hf, Category.id_comp]
  · apply Grp.hom_ext
    apply (cancel_mono t''.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hf, hφ', Category.id_comp]

end Langlands.GroupScheme.CoverPreimage
