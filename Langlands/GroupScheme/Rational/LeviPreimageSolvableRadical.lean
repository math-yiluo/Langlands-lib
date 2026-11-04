import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.DominantHomFaithfullyFlat
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Solvable radicals of a group with a rational Levi decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LeviPreimageRadical

section Image

variable {K : Type u} [Field K]
  {P L H : GroupScheme (Spec (CommRingCat.of K))}
  (l : L ⟶ P) (q : P ⟶ L) (h : H ⟶ P)

local instance : Subsingleton (Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

/-- The schematic image of a normal subgroup under a split homomorphism is normal. -/
theorem isNormal_range_imageInclusion [IsAffineHom L.X.hom] [IsAffineHom H.X.hom]
    (hlq : l ≫ q = 𝟙 L) (hn : (SubgroupFunctor.range h).IsNormal) :
    (SubgroupFunctor.range (SchematicImage.inclusion (h ≫ q))).IsNormal := by
  let φ := h ≫ q
  let : QuasiCompact φ.hom.hom.left := HomImage.quasiCompact_hom φ
  let i := SchematicImage.inclusionOver φ
  let p := SchematicImage.projectionOver φ
  have : IsSchemeTheoreticallyDominant (L.X ◁ p).left :=
    ImageGeneration.isSchemeTheoreticallyDominant_whiskerLeft p L.X
  let g : L.X ⊗ SchematicImage.imageOver φ ⟶ L.X :=
    fst _ _ * (snd _ _ ≫ i) * (fst _ _)⁻¹
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hn (L.X ⊗ H.X) (fst _ _ ≫ l.hom.hom)
    (snd _ _ ≫ h.hom.hom) (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨snd _ _, rfl⟩))
  have hq : (fst L.X H.X ≫ l.hom.hom) ≫ q.hom.hom = fst L.X H.X := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hlq, Grp.id_hom_hom, Category.comp_id]
  obtain ⟨a, ha⟩ := exists_over_factor_of_schematic_precomp i
    (L.X ◁ p) g (y ≫ p) (by
      have hy' := congrArg (fun z => z ≫ q.hom.hom) hy
      simp only at hy'
      rw [Category.assoc, SchematicImage.projectionOver_fac]
      change (L.X ◁ p) ≫ g = y ≫ h.hom.hom ≫ q.hom.hom
      rw [← Category.assoc, hy', MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hq]
      simp only [g, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst, whiskerLeft_snd_assoc]
      rw [show p ≫ i = h.hom.hom ≫ q.hom.hom from SchematicImage.projectionOver_fac φ,
        Category.assoc])
  intro T x z _ hz
  obtain ⟨z', rfl⟩ := SubgroupFunctor.mem_range.mp hz
  refine SubgroupFunctor.mem_range.mpr ⟨lift x z' ≫ a, ?_⟩
  change (lift x z' ≫ a) ≫ i = x * (z' ≫ i) * x⁻¹
  rw [Category.assoc, ha]
  simp only [g, MonObj.comp_mul, GrpObj.comp_inv]
  erw [lift_fst, lift_snd_assoc]

end Image

section SolvableImage

variable {K : Type u} [Field K] {H D : GroupScheme (Spec (CommRingCat.of K))}

/-- A homomorphism of groups locally of finite type that is surjective on underlying schemes
carries solvable groups to solvable groups. -/
theorem isSolvableGroupScheme_of_surjective (f : H ⟶ D)
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType D.X.hom]
    [Surjective f.hom.hom.left] (hH : IsSolvableGroupScheme H) :
    IsSolvableGroupScheme D := by
  let b := toAlgebraicClosure K
  let f' := (GroupScheme.baseChange b).map f
  have : Surjective f'.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip inferInstance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd H.X.hom b))
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj D).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd D.X.hom b))
  let V := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure K))))
  let φ : (V ⟶ ((GroupScheme.baseChange b).obj H).X) →*
      (V ⟶ ((GroupScheme.baseChange b).obj D).X) :=
    { toFun := fun x => x ≫ f'.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  let : Group.IsSolvable (V ⟶ ((GroupScheme.baseChange b).obj H).X) := hH
  change Group.IsSolvable (V ⟶ ((GroupScheme.baseChange b).obj D).X)
  refine Group.isSolvable_of_surjective (f := φ) ?_
  intro y
  obtain ⟨x, hx⟩ := DominantHom.rational_lift f' y (f'.hom.hom.left.surjective _)
  exact ⟨x, hx⟩

end SolvableImage

section Preimage

variable {K : Type u} [Field K]
  {P L C U : GroupScheme (Spec (CommRingCat.of K))}
  (l : L ⟶ P) (q : P ⟶ L) (u : U ⟶ P) (c : C ⟶ L)

/-- The inverse image of a solvable radical of `L` under a smooth geometrically connected
retraction `q` of `P` onto `L`, whose geometric kernel points come from a group with solvable
geometric points, is a solvable radical of `P`. -/
theorem isSolvableRadical_preimage
    [IsAffineHom P.X.hom] [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
    [Smooth q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (hlq : l ≫ q = 𝟙 L)
    (hker : ∀ x : algebraicClosurePoint K ⟶ P.X, x ≫ q.hom.hom = 1 →
      ∃ y : algebraicClosurePoint K ⟶ U.X, y ≫ u.hom.hom = x)
    (hU : Group.IsSolvable (algebraicClosurePoint K ⟶ U.X))
    (hc : IsSolvableRadical c) :
    IsSolvableRadical (SubgroupPreimage.inclusion q c) := by
  have : Smooth C.X.hom := hc.smooth
  have : ConnectedSpace C.X.left := hc.connectedSpace
  have : IsClosedImmersion c.hom.hom.left := hc.isClosedSubgroup
  have : IsAffineHom C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  refine ⟨SubgroupPreimage.isClosedSubgroup q c hc.isClosedSubgroup,
    SubgroupPreimage.smooth q c, SubgroupPreimage.connectedSpace q c, ?_,
    SubgroupPreimage.isNormal q c hc.isNormal, ?_⟩
  · apply isSolvableGroupScheme_of_isSolvable_points
    let T := algebraicClosurePoint K
    let i := SubgroupPreimage.inclusion q c
    let p := SubgroupPreimage.projection q c
    have : IsClosedImmersion i.hom.hom.left :=
      SubgroupPreimage.isClosedSubgroup q c hc.isClosedSubgroup
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    let g : (T ⟶ (SubgroupPreimage.groupScheme q c).X) →* (T ⟶ C.X) :=
      { toFun := fun x => x ≫ p.hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
    let inc : (T ⟶ (SubgroupPreimage.groupScheme q c).X) →* (T ⟶ P.X) :=
      { toFun := fun x => x ≫ i.hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
    let υ : (T ⟶ U.X) →* (T ⟶ P.X) :=
      { toFun := fun y => y ≫ u.hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
    have hk : ∀ x ∈ g.ker, inc x ∈ υ.range := by
      intro x hx
      have hxp : x ≫ p.hom.hom = 1 := hx
      have hxq : (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
        rw [Category.assoc, (SubgroupPreimage.isPullback q c).w, ← Category.assoc, hxp,
          MonObj.one_comp]
      obtain ⟨y, hy⟩ := hker _ hxq
      exact ⟨y, hy⟩
    let κ : g.ker →* υ.range :=
      { toFun := fun x => ⟨inc x, hk x x.property⟩
        map_one' := Subtype.ext (map_one inc)
        map_mul' := fun x y => Subtype.ext (map_mul inc x.1 y.1) }
    let : Group.IsSolvable (T ⟶ U.X) := hU
    let : Group.IsSolvable υ.range :=
      Group.isSolvable_of_surjective (f := υ.rangeRestrict) υ.rangeRestrict_surjective
    let : Group.IsSolvable g.ker :=
      Group.isSolvable_of_isSolvable_injective (f := κ) (fun x y h =>
        Subtype.ext ((cancel_mono i.hom.hom).mp (congrArg Subtype.val h)))
    let : Group.IsSolvable (T ⟶ C.X) :=
      SolvableFieldExtensionProof.allPoints_isSolvable C hc.smooth hc.isSolvableGroupScheme T
    exact Group.isSolvable_of_ker_le_range g.ker.subtype g (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  · intro H h hh hHs hHc hHsol hHn
    have : Smooth H.X.hom := hHs
    have : ConnectedSpace H.X.left := hHc
    have : IsClosedImmersion h.hom.hom.left := hh
    have : IsAffineHom H.X.hom := by
      rw [← Over.w h.hom.hom]
      infer_instance
    have : GeometricallyIntegral H.X.hom :=
      smoothConnectedAffineGeometry.1 K H inferInstance inferInstance inferInstance
    let φ := h ≫ q
    have : Surjective (SchematicImage.projection φ).hom.hom.left :=
      HomImage.surjective_projection φ
    have hD := hc.greatest (SchematicImage.image φ) (SchematicImage.inclusion φ)
      (HomImage.isClosedSubgroup_inclusion φ) (HomImage.smooth_image φ) inferInstance
      (isSolvableGroupScheme_of_surjective (SchematicImage.projection φ) hHsol)
      (isNormal_range_imageInclusion l q h hlq hHn)
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [SubgroupPreimage.range_inclusion, SubgroupFunctor.mem_comap]
    apply hD T
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (SchematicImage.projection φ).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion,
      Grp.comp_hom_hom, Category.assoc]

end Preimage

section Geometric

variable {k : Type u} [Field k]

/-- A closed smooth connected solvable subgroup with the same all-test range as a solvable
radical is itself a solvable radical. -/
theorem isSolvableRadical_of_range_eq {R R' P : GroupScheme (Spec (CommRingCat.of k))}
    {r : R ⟶ P} {r' : R' ⟶ P} (hr : IsSolvableRadical r) (hc : IsClosedSubgroup r')
    (hs : Smooth R'.X.hom) (hconn : ConnectedSpace R'.X.left)
    (hsol : IsSolvableGroupScheme R')
    (h : SubgroupFunctor.range r' = SubgroupFunctor.range r) : IsSolvableRadical r' :=
  ⟨hc, hs, hconn, hsol, h ▸ hr.isNormal,
    fun H j hj hHs hHc hHsol hHn => h ▸ hr.greatest H j hj hHs hHc hHsol hHn⟩

/-- If a rational Levi subgroup has a geometric solvable radical, then so does the ambient
group: the inverse image of the Levi radical under the Levi retraction. -/
theorem _root_.Langlands.GroupScheme.IsRationalLeviSubgroup.exists_isGeometricSolvableRadical
    {L P C : GroupScheme (Spec (CommRingCat.of k))} {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) {c : C ⟶ L} (hc : IsGeometricSolvableRadical c) :
    ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
      IsGeometricSolvableRadical r := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  let : IsAffineHom P.X.hom := hl.isAffineHom
  let : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  let : Smooth L.X.hom := hl.isConnectedReductive.smooth
  let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hr.1.smooth
  let : ConnectedSpace U.X.left := hr.1.connectedSpace
  let : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  let q := leviRetraction l r hr.1.isNormal
  let : Smooth q.hom.hom.left := smooth_leviRetraction l r hr.1.isNormal
  let : GeometricallyConnected q.hom.hom.left :=
    geometricallyConnected_leviRetraction l r hr.1.isNormal
  have hlq : l ≫ q = 𝟙 L := levi_comp_leviRetraction l r hr.1.isNormal
  have hker : ∀ {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ P.X), x ≫ q.hom.hom = 1 →
      ∃ y : T ⟶ U.X, y ≫ r.hom.hom = x := fun x hx =>
    SubgroupFunctor.mem_range.mp ((comp_leviRetraction_eq_one_iff l r hr.1.isNormal x).mp hx)
  have hA := isSolvableRadical_preimage l q r c hlq (fun x hx => hker x hx)
    (isSolvable_points_of_isUnipotent hr.1.isUnipotent _) hc.1
  refine ⟨_, SubgroupPreimage.inclusion q c, hA, ?_⟩
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : IsAffineHom (B.obj P).X.hom := inferInstanceAs (IsAffineHom (pullback.snd P.X.hom b))
  have : IsAffineHom (B.obj L).X.hom := inferInstanceAs (IsAffineHom (pullback.snd L.X.hom b))
  have : LocallyOfFiniteType (B.obj L).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd L.X.hom b))
  have : IsAffineHom (B.obj U).X.hom := inferInstanceAs (IsAffineHom (pullback.snd U.X.hom b))
  have : LocallyOfFiniteType (B.obj U).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd U.X.hom b))
  have : Smooth (B.map q).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b q).flip inferInstance
  have : GeometricallyConnected (B.map q).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b q).flip inferInstance
  have hlq' : B.map l ≫ B.map q = 𝟙 (B.obj L) := by
    rw [← B.map_comp, hlq, B.map_id]
  have hker' : ∀ x : algebraicClosurePoint (AlgebraicClosure k) ⟶ (B.obj P).X,
      x ≫ (B.map q).hom.hom = 1 →
        ∃ y : algebraicClosurePoint (AlgebraicClosure k) ⟶ (B.obj U).X,
          y ≫ (B.map r).hom.hom = x := by
    intro x hx
    have hx' : baseChangePointsEquiv b P _ x ≫ q.hom.hom = 1 := by
      rw [← baseChangePointsEquiv_comp]
      exact (congrArg (baseChangePointsEquiv b L _) hx).trans (map_one _)
    obtain ⟨y, hy⟩ := hker _ hx'
    refine ⟨(baseChangePointsEquiv b U _).symm y, ?_⟩
    apply (baseChangePointsEquiv b P _).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, hy]
  have hA' := isSolvableRadical_preimage (B.map l) (B.map q) (B.map r) (B.map c) hlq' hker'
    (isSolvable_points_of_isUnipotent hr.2.isUnipotent _) hc.2
  let R := SubgroupPreimage.groupScheme q c
  have : Smooth R.X.hom := hA.smooth
  have : ConnectedSpace R.X.left := hA.connectedSpace
  have : IsClosedImmersion (SubgroupPreimage.inclusion q c).hom.hom.left := hA.isClosedSubgroup
  have : IsAffineHom R.X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion q c).hom.hom]
    infer_instance
  refine isSolvableRadical_of_range_eq hA' (IsClosedSubgroup.baseChange b hA.isClosedSubgroup)
    (inferInstanceAs (Smooth (pullback.snd R.X.hom b)))
    (R.connectedSpace_baseChange_of_connected b)
    ((isSolvableGroupScheme_iff_isSolvable_points _).mpr hA.isSolvableGroupScheme) ?_
  rw [SubgroupPreimage.range_inclusion, SubgroupFunctor.range_baseChangeHom,
    SubgroupPreimage.range_inclusion, SubgroupFunctor.comap_baseChange,
    SubgroupFunctor.range_baseChangeHom]

end Geometric

section Levi

variable {k : Type u} [Field k] {G P : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G}

/-- Given the dynamic description of parabolics and connected reductivity of dynamic
centralizers, every parabolic of a connected reductive group has a rational Levi subgroup:
the factor of the dynamic centralizer `Z_G(χ)` through `P = P_G(χ)`. -/
theorem _root_.Langlands.GroupScheme.IsParabolicSubgroup.exists_isRationalLeviSubgroup
    (hPD : ParabolicDynamicStatement.{u}) (hCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hj : IsParabolicSubgroup j) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P), IsRationalLeviSubgroup l := by
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hj.isClosedSubgroup).mp hj
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let l := hP.factorHom (Dynamic.Affine.centralizerHom χ)
    (by rw [hZ.2]; exact Dynamic.centralizer_le_parabolic χ)
  let r := hP.factorHom (Dynamic.Affine.unipotentHom χ)
    (by rw [hU.2]; exact Dynamic.unipotent_le_parabolic χ)
  have hl : l ≫ j = Dynamic.Affine.centralizerHom χ := hP.factorHom_comp _ _
  have hr : r ≫ j = Dynamic.Affine.unipotentHom χ := hP.factorHom_comp _ _
  have hZred := hCR k G hG χ _ (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hZ
  have hrad := Dynamic.isGeometricUnipotentRadical_of_centralizer χ
    (Dynamic.Affine.centralizerHom χ) j r hP (by rw [hr]; exact hU) hZ hZred
  exact ⟨_, l, Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical hP hZ hU l r hl hr
    hZred hrad⟩

end Levi

end LeviPreimageRadical

end Langlands.GroupScheme
