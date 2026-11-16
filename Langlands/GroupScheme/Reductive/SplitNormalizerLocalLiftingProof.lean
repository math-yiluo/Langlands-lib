import Langlands.GroupScheme.Reductive.SplitNormalizerLocalLiftingStatement
import Langlands.GroupScheme.Torus.LocalTransporterDescent
import Langlands.GroupScheme.Torus.FieldTransporterDescent
import Langlands.GroupScheme.Torus.PointedEtaleNormalizer
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.Torus.WeylPointTransport

/-! # Zariski local lifting of geometric normalizer points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  {j₁ j₂ : T.toGrp ⟶ G} {U : Over S} {x : U ⟶ G.X}

/-- A smooth affine transporter has local sections at every point of its image
when its centralizer is a split torus. -/
theorem exists_local_transporter_of_smooth
    [Mono j₂.hom.hom.left] [IsAffineHom U.hom] [Smooth U.hom]
    (hT : IsSplitTorus T.toGrp) (hx : IsTransporter j₁ j₂ x)
    (hC : torusCentralizer j₂ = SubgroupFunctor.range j₂)
    (s : S) (hs : s ∈ Set.range U.hom) :
    ∃ V : S.Opens, s ∈ V ∧
      ∃ n : Over.mk V.ι ⟶ G.X, IsTransporter j₁ j₂ n := by
  let W : S.Opens := ⟨Set.range U.hom, U.hom.isOpenMap.isOpen_range⟩
  let q := U.hom ∣_ W
  let U' : Over W.toScheme := Over.mk q
  have : IsAffineHom U'.hom :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict U.hom W).flip
      (show IsAffineHom U.hom from inferInstance)
  have : Flat U'.hom := by change Flat (U.hom ∣_ W); infer_instance
  have : Surjective U'.hom := by
    constructor
    intro w
    obtain ⟨v, hv⟩ := w.property
    let z : U.hom ⁻¹ᵁ W := ⟨v, ⟨v, rfl⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (q ≫ W.ι) z = w.val
    rw [show q ≫ W.ι = (U.hom ⁻¹ᵁ W).ι ≫ U.hom from
      morphismRestrict_ι U.hom W]
    exact hv
  let a : (Over.map W.ι).obj U' ⟶ U :=
    Over.homMk (U.hom ⁻¹ᵁ W).ι (morphismRestrict_ι U.hom W).symm
  let x' := baseChangeTransporterPoint (g := x) W.ι a
  have hx' := hx.baseChange_point W.ι a
  have hC' : torusCentralizer
      (T := (CommGroupScheme.baseChange W.ι).obj T)
      ((GroupScheme.baseChange W.ι).map j₂) =
        SubgroupFunctor.range ((GroupScheme.baseChange W.ι).map j₂) := by
    rw [torusCentralizer_baseChange, hC, SubgroupFunctor.range_baseChangeHom]
  have : Mono ((GroupScheme.baseChange W.ι).map j₂).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := MorphismProperty.monomorphisms _) W.ι
      j₂.hom.hom inferInstance
  have : Mono ((GroupScheme.baseChange W.ι).map j₂).hom.hom := Over.mono_of_mono_left _
  obtain ⟨V, hsV, n, hn⟩ := exists_local_transporter_of_cover
    (hT.baseChange W.ι) x' hx' hC' (⟨s, hs⟩ : W)
  let V' := W.ι ''ᵁ V
  let n₀ := Langlands.GroupScheme.baseChangePointsEquiv W.ι G (Over.mk V.ι) n
  have hn₀ := hn.baseChangePointsEquiv W.ι
  let e : Over.mk V'.ι ⟶ (Over.map W.ι).obj (Over.mk V.ι) :=
    Over.homMk (W.ι.isoImage V).inv (Scheme.Hom.isoImage_inv_ι W.ι V)
  refine ⟨V', ?_, e ≫ n₀, hn₀.restrict e⟩
  exact ⟨⟨s, hs⟩, hsV, rfl⟩

end PointwiseSchemeAction

namespace PointwiseSchemeAction

/-- A field-valued transporter for a self-centralizing split torus implies an
actual transporter on a Zariski neighbourhood of the field point's image. -/
theorem exists_local_transporter_of_fieldPoint
    {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
    {j₁ j₂ : T.toGrp ⟶ G} [Mono j₂.hom.hom.left]
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp)
    (hC : torusCentralizer j₂ = SubgroupFunctor.range j₂)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec R)
    {n : Over.mk b ⟶ G.X} (hn : IsTransporter j₁ j₂ n) :
    ∃ V : (Spec R).Opens, b (IsLocalRing.closedPoint k) ∈ V ∧
      ∃ nV : Over.mk V.ι ⟶ G.X, IsTransporter j₁ j₂ nV := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨I, hI, ⟨d⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let e := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ d.symm
  let U := relativeTransporterScheme (e.hom ≫ j₁) (e.hom ≫ j₂)
  let g := relativeTransporterHom (e.hom ≫ j₁) (e.hom ≫ j₂)
  have hg : IsTransporter j₁ j₂ g := by
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
      (relativeTransporterHom_isTransporter (e.hom ≫ j₁) (e.hom ≫ j₂)).precomp e.inv
  have : Smooth U.hom :=
    smooth_relativeTransporterScheme (e.hom ≫ j₁) (e.hom ≫ j₂) hG
  have : IsAffineHom U.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  let φ : R ⟶ CommRingCat.of k := Spec.preimage b
  let : Algebra R k := φ.hom.toAlgebra
  let C : CommAlgCat.{u} R := CommAlgCat.of R k
  let c : (algSpec R).obj (op C) ⟶ Over.mk b :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ b = Spec.map (Spec.preimage b)
      rw [Category.id_comp, Spec.map_preimage])
  obtain ⟨y, -⟩ := (exists_relativeTransporter_factor_iff
    (e.hom ≫ j₁) (e.hom ≫ j₂) (c ≫ n)).mpr ((hn.restrict c).precomp e.hom)
  have hybase : y.left ≫ U.hom = b := by
    rw [Over.w y]
    exact Spec.map_preimage b
  apply exists_local_transporter_of_smooth
    (show IsSplitTorus T.toGrp from ⟨I, hI, ⟨d⟩⟩) hg hC
  exact ⟨y.left (IsLocalRing.closedPoint k),
    congrArg (fun f => f (IsLocalRing.closedPoint k)) hybase⟩

end PointwiseSchemeAction

namespace PointwiseSchemeAction

/-- An all-test transporter realizing an automorphism of the source torus
belongs to its full normalizer on the same test scheme. -/
theorem IsTransporter.mem_torusNormalizer
    {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    {t : T.toGrp ⟶ G} {U : Over S} {n : U ⟶ G.X} {σ : T ≅ T}
    (hn : IsTransporter (CommGroupScheme.groupHom σ.hom ≫ t) t n) :
    n ∈ (torusNormalizer t).carrier U := by
  rw [Langlands.GroupScheme.mem_torusNormalizer]
  intro V a z
  let f := (CommGroupScheme.groupHom σ.hom).hom.hom
  let g := (CommGroupScheme.groupHom σ.inv).hom.hom
  have hgf : g ≫ f = 𝟙 T.X :=
    congrArg (fun h => (CommGroupScheme.groupHom h).hom.hom) σ.inv_hom_id
  constructor
  · refine ⟨z ≫ f, ?_⟩
    apply mul_inv_eq_iff_eq_mul.mpr
    simpa only [Grp.comp_hom_hom, Category.assoc] using (hn V a z).symm
  · refine ⟨z ≫ g, ?_⟩
    have h := hn V a (z ≫ g)
    change (z ≫ g ≫ f ≫ t.hom.hom) * (a ≫ n) =
      (a ≫ n) * ((z ≫ g) ≫ t.hom.hom) at h
    rw [← Category.assoc g f, hgf, Category.id_comp] at h
    calc
      (a ≫ n)⁻¹ * (z ≫ t.hom.hom) * (a ≫ n) =
          (a ≫ n)⁻¹ * ((z ≫ t.hom.hom) * (a ≫ n)) := by group
      _ = (a ≫ n)⁻¹ * ((a ≫ n) * ((z ≫ g) ≫ t.hom.hom)) := by rw [h]
      _ = (z ≫ g) ≫ t.hom.hom := by group

end PointwiseSchemeAction

/-- Geometric normalizer classes of a split reductive group lift on Zariski
neighbourhoods over arbitrary commutative rings. -/
theorem splitNormalizerGeometricLocalLifting :
    SplitNormalizerGeometricLocalLiftingStatement.{u} := by
  classical
  intro R _ G hG I _ t J P ht hmax _ _ k _ _ x n hn
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I
  have hT : IsSplitTorus T.toGrp := isSplitTorus_splitTorus I
  have hn' : n ∈ (torusNormalizer (T := T) t).carrier (Over.mk x) := hn
  have hC := splitTorusCentralizer_eq_range_of_fibrewiseMaximal hG hT t ht hmax
  let B := GroupScheme.baseChange x
  let TB := (CommGroupScheme.baseChange x).obj T
  let t₀ := B.map t
  have : Mono t₀.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := MorphismProperty.monomorphisms _) x
      t.hom.hom inferInstance
  let U₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let c : (Over.map x).obj U₀ ⟶ Over.mk x :=
    Over.homMk (𝟙 _) (by simp [U₀])
  let d : Over.mk x ⟶ (Over.map x).obj U₀ :=
    Over.homMk (𝟙 _) (by simp [U₀])
  have hdc : d ≫ c = 𝟙 (Over.mk x) := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  let n₀ : U₀ ⟶ (B.obj G).X := (baseChangePointsEquiv x G U₀).symm (c ≫ n)
  have hn₀ : n₀ ∈ (torusNormalizer (T := TB) t₀).carrier U₀ := by
    apply (mem_torusNormalizer_baseChange_iff (T := T) (G := G) x t U₀ n₀).mpr
    rw [show baseChangePointsEquiv x G U₀ n₀ = c ≫ n from
      MulEquiv.apply_symm_apply _ _]
    exact (torusNormalizer (T := T) t).comp_mem c hn'
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : TB ≅ TB, IsNormalizingPoint t₀ n₀ σ₀ := by
    have h := hn₀
    rw [torusNormalizer_carrier_base] at h
    exact h
  obtain ⟨σ, hσ⟩ := hT.automorphism_fieldBaseChange_surjective x σ₀
  let j₁ := CommGroupScheme.groupHom σ.hom ≫ t
  have hn₀T : PointwiseSchemeAction.IsTransporter (B.map j₁) (B.map t) n₀ := by
    have h := hσ₀.isTransporter
    have he : B.map (CommGroupScheme.groupHom σ.hom) =
        CommGroupScheme.groupHom σ₀.hom :=
      congrArg (fun e => CommGroupScheme.groupHom e.hom) hσ
    simpa only [j₁, Functor.map_comp, he] using h
  have hnT : PointwiseSchemeAction.IsTransporter j₁ t n := by
    have h := (hn₀T.baseChangePointsEquiv x).restrict d
    rw [show baseChangePointsEquiv x G U₀ n₀ = c ≫ n from
      MulEquiv.apply_symm_apply _ _, ← Category.assoc, hdc, Category.id_comp] at h
    exact h
  obtain ⟨V, hV, nV, hnV⟩ :=
    PointwiseSchemeAction.exists_local_transporter_of_fieldPoint hG.smooth hT hC x hnT
  have hxV : Set.range x ⊆ (V : Set (Spec (CommRingCat.of R))) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint k)]
    exact hV
  let a : Over.mk x ⟶ Over.mk V.ι :=
    Over.homMk (IsOpenImmersion.lift V.ι x (by simpa using hxV))
      (IsOpenImmersion.lift_fac V.ι x (by simpa using hxV))
  refine ⟨V, hV, a, nV, hnV.mem_torusNormalizer, ?_⟩
  have hdiff := hnT.inv_mul_mem_torusCentralizer (hnV.restrict a)
  rw [hC] at hdiff
  have hconj := SubgroupFunctor.conj_mem_of_mem_normalizer hn hdiff
  simpa only [mul_inv_cancel_left] using hconj

end Langlands.GroupScheme
