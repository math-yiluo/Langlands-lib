import Langlands.GroupScheme.Torus.RelativeTransporterEtaleLift
import Langlands.GroupScheme.RelativeIdentityComponent.SectionNeighbourhood
import Langlands.AlgebraicGeometry.SmoothEtaleLocalSections

/-! # Etale local identity-component transporters from field-valued points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S S' : Scheme.{u}} {H G : GroupScheme S} {i₁ i₂ : H ⟶ G}

/-- The pullback point adjunction carries an all-test transporter back to the
original group, without any hypothesis on the base change. -/
theorem IsTransporter.baseChangePointsEquiv (b : S' ⟶ S) {T : Over S'}
    {g : T ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hg : IsTransporter ((GroupScheme.baseChange b).map i₁)
      ((GroupScheme.baseChange b).map i₂) g) :
    IsTransporter i₁ i₂ (Langlands.GroupScheme.baseChangePointsEquiv b G T g) := by
  intro V a h
  let W : Over S' := Over.mk (a.left ≫ T.hom)
  let c : (Over.map b).obj W ⟶ V := Over.homMk (𝟙 V.left) (by
    change 𝟙 V.left ≫ V.hom = (a.left ≫ T.hom) ≫ b
    rw [Category.id_comp, Category.assoc]
    exact (Over.w a).symm)
  let a' : W ⟶ T := Over.homMk a.left
  have hc : (Over.map b).map a' = c ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = 𝟙 V.left ≫ a.left
    exact (Category.id_comp _).symm
  have : Epi c.left := inferInstanceAs (Epi (𝟙 V.left))
  have : Epi c := Over.epi_of_epi_left c
  let h' := (Langlands.GroupScheme.baseChangePointsEquiv b H W).symm (c ≫ h)
  have he := congrArg (Langlands.GroupScheme.baseChangePointsEquiv b G W) (hg W a' h')
  rw [map_mul, map_mul, Langlands.GroupScheme.baseChangePointsEquiv_comp,
    Langlands.GroupScheme.baseChangePointsEquiv_comp,
    Langlands.GroupScheme.baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply, hc] at he
  apply (cancel_epi c).mp
  simpa only [MonObj.comp_mul, Category.assoc] using he

end PointwiseSchemeAction

namespace RelativeIdentityComponent

variable {S S' : Scheme.{u}} (G : GroupScheme S)

/-- Projection from any base change sends the relative identity set into the
original relative identity set. -/
theorem image_underlyingSet_baseChange (b : S' ⟶ S) :
    pullback.fst G.X.hom b '' underlyingSet ((GroupScheme.baseChange b).obj G) ⊆
      underlyingSet G := by
  rw [← componentSet_unit, ← componentSet_unit]
  apply Langlands.AlgebraicGeometry.SectionComponent.image_componentSet_subset
    (pullback.fst G.X.hom b) b pullback.condition
  change (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
    ((Over.pullback b).map η[G.X]).left ≫ pullback.fst G.X.hom b = _
  have hf : ((Over.pullback b).map η[G.X]).left ≫ pullback.fst G.X.hom b =
      pullback.fst (𝟙 S) b ≫ unitSection G :=
    pullback.lift_fst _ _ _
  rw [hf, Over.ε_pullback_left]
  have h : pullback.fst (𝟙 S) b = pullback.snd (𝟙 S) b ≫ b := by
    simpa using pullback.condition (f := 𝟙 S) (g := b)
  rw [h]
  simp

/-- For a smooth affine group over a field, its actual identity component is
contained in its relative identity set. -/
theorem identitySet_subset_underlyingSet {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    IdentityComponent.identitySet H ⊆ underlyingSet H := by
  have h := inRelativeIdentityComponent_of_geometricallyConnected H
    (identityComponentι H).hom.hom η[(identityComponent H).X]
    (IsMonHom.one_hom _)
  have hr := (inRelativeIdentityComponent_iff_range_subset H _).mp h
  rwa [IdentityComponent.range_identityComponentι] at hr

/-- A point in the identity component of any field pullback projects into the
actual relative identity open of the original smooth affine group. -/
theorem image_identitySet_baseChange [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    pullback.fst G.X.hom b '' IdentityComponent.identitySet
      ((GroupScheme.baseChange b).obj G) ⊆ underlyingSet G := by
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  rintro _ ⟨x, hx, rfl⟩
  exact image_underlyingSet_baseChange G b
    ⟨x, identitySet_subset_underlyingSet _ hx, rfl⟩

/-- The pullback point adjunction reflects relative identity membership into
any base change of a smooth group. -/
theorem inRelativeIdentityComponent_of_baseChangePointsEquiv [Smooth G.X.hom]
    (b : S' ⟶ S) {T : Over S'} (g : T ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg : InRelativeIdentityComponent G
      (Langlands.GroupScheme.baseChangePointsEquiv b G T g)) :
    InRelativeIdentityComponent ((GroupScheme.baseChange b).obj G) g := by
  obtain ⟨H, i, hi, -, -⟩ := smoothStructure.1 S G inferInstance
  obtain ⟨a, ha⟩ := (hi.factors_iff _ _).mpr hg
  have hi' := smoothStructure.2.2 S G inferInstance H i hi S' b
  apply (hi'.factors_iff T g).mp
  refine ⟨(Langlands.GroupScheme.baseChangePointsEquiv b H T).symm a, ?_⟩
  apply (Langlands.GroupScheme.baseChangePointsEquiv b G T).injective
  rw [Langlands.GroupScheme.baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, ha]

end RelativeIdentityComponent

namespace PointwiseSchemeAction

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)} (i₁ i₂ : H ⟶ G)

/-- An affine etale neighbourhood carrying an actual transporter in the
relative identity component, with its image containing the specified base point. -/
structure EtaleIdentityTransporterData (s : Spec R) where
  neighbourhoodRing : CommRingCat.{u}
  projection : Spec neighbourhoodRing ⟶ Spec R
  etale : Etale projection
  mem_range : s ∈ Set.range projection
  pointMap : Over.mk projection ⟶ G.X
  isTransporter : IsTransporter i₁ i₂ pointMap
  inIdentity : InRelativeIdentityComponent G pointMap

section Diagonalizable

variable {M : Type u} [AddCommGroup M]
  (j₁ j₂ : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- A field-valued transporter in the actual fibre identity component produces
an etale local transporter in the relative identity component. The field may be
an arbitrary extension, and the new point need not recover the original one. -/
def etaleIdentityTransporter [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (s : Spec R) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec R) (hb : b default = s)
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg₀ : IsTransporter ((GroupScheme.baseChange b).map j₁)
      ((GroupScheme.baseChange b).map j₂) g₀)
    (hidentity : Set.range g₀.left ⊆ IdentityComponent.identitySet
      ((GroupScheme.baseChange b).obj G)) : EtaleIdentityTransporterData j₁ j₂ s :=
  Classical.choice <| by
    let : Smooth G.X.hom := hG
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let z : Spec (CommRingCat.of k) := default
    let a₀ := Langlands.GroupScheme.baseChangePointsEquiv b G _ g₀
    have ha₀ : IsTransporter j₁ j₂ a₀ := hg₀.baseChangePointsEquiv b
    let φ : R ⟶ CommRingCat.of k := Spec.preimage b
    let : Algebra R k := φ.hom.toAlgebra
    let C : CommAlgCat.{u} R := CommAlgCat.of R k
    let c : (algSpec R).obj (op C) ⟶
        (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (𝟙 _ ≫ b) = Spec.map (Spec.preimage b)
        rw [Category.id_comp, Category.id_comp, Spec.map_preimage])
    obtain ⟨y, hy⟩ := (exists_relativeTransporter_factor_iff j₁ j₂ (c ≫ a₀)).mpr
      (ha₀.restrict c)
    have hybase : y.left ≫ (relativeTransporterScheme j₁ j₂).hom = b := by
      rw [Over.w y]
      change Spec.map (Spec.preimage b) = b
      exact Spec.map_preimage _
    have hyrec : y.left ≫ (relativeTransporterHom j₁ j₂).left =
        g₀.left ≫ pullback.fst G.X.hom b := by
      have hy' := congrArg Over.Hom.left hy
      change y.left ≫ (relativeTransporterHom j₁ j₂).left = (𝟙 _) ≫ a₀.left at hy'
      simpa only [a₀, Category.id_comp, baseChangePointsEquiv_left] using hy'
    let O : (relativeTransporterScheme j₁ j₂).left.Opens :=
      ⟨(relativeTransporterHom j₁ j₂).left ⁻¹' RelativeIdentityComponent.underlyingSet G,
        (RelativeIdentityComponent.isOpen_underlyingSet G).preimage
          (relativeTransporterHom j₁ j₂).left.continuous⟩
    have hyO : y.left z ∈ O := by
      change (y.left ≫ (relativeTransporterHom j₁ j₂).left) z ∈
        RelativeIdentityComponent.underlyingSet G
      rw [hyrec]
      exact RelativeIdentityComponent.image_identitySet_baseChange G b
        ⟨g₀.left z, hidentity ⟨z, rfl⟩, rfl⟩
    let w : O := ⟨y.left z, hyO⟩
    let : Smooth (relativeTransporterScheme j₁ j₂).hom :=
      smooth_relativeTransporterScheme j₁ j₂ hG
    have hw : (O.ι ≫ (relativeTransporterScheme j₁ j₂).hom) w = s := by
      change (y.left ≫ (relativeTransporterScheme j₁ j₂).hom) z = s
      rw [hybase]
      exact hb
    obtain ⟨R', e, a, he, hs, hfac⟩ :=
      Langlands.AlgebraicGeometry.exists_etale_spec_of_smooth
        (O.ι ≫ (relativeTransporterScheme j₁ j₂).hom) w
    rw [hw] at hs
    let aT : Over.mk e ⟶ relativeTransporterScheme j₁ j₂ :=
      Over.homMk (a ≫ O.ι) (by
        change (a ≫ O.ι) ≫ (relativeTransporterScheme j₁ j₂).hom = e
        simpa only [Category.assoc] using hfac)
    let g : Over.mk e ⟶ G.X := aT ≫ relativeTransporterHom j₁ j₂
    refine ⟨⟨R', e, he, hs, g,
      (relativeTransporterHom_isTransporter j₁ j₂).restrict aT, ?_⟩⟩
    apply (RelativeIdentityComponent.inRelativeIdentityComponent_iff_range_subset G g).mpr
    rintro _ ⟨v, rfl⟩
    change (relativeTransporterHom j₁ j₂).left (O.ι (a v)) ∈
      RelativeIdentityComponent.underlyingSet G
    exact (a v).property

end Diagonalizable

/-- Transfer the etale identity-transporter construction along an actual
isomorphism from a diagonalizable source. -/
def etaleIdentityTransporterOfSourceIso [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (s : Spec R) {M : Type u} [AddCommGroup M]
    (e : (Diagonalizable.groupScheme R M).toGrp ≅ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec R) (hb : b default = s)
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg₀ : IsTransporter ((GroupScheme.baseChange b).map i₁)
      ((GroupScheme.baseChange b).map i₂) g₀)
    (hidentity : Set.range g₀.left ⊆ IdentityComponent.identitySet
      ((GroupScheme.baseChange b).obj G)) : EtaleIdentityTransporterData i₁ i₂ s := by
  have hpre : IsTransporter ((GroupScheme.baseChange b).map (e.hom ≫ i₁))
      ((GroupScheme.baseChange b).map (e.hom ≫ i₂)) g₀ := by
    simpa only [Functor.map_comp] using hg₀.precomp ((GroupScheme.baseChange b).map e.hom)
  let d := etaleIdentityTransporter (e.hom ≫ i₁) (e.hom ≫ i₂) hG s b hb g₀ hpre hidentity
  refine ⟨d.neighbourhoodRing, d.projection, d.etale, d.mem_range, d.pointMap, ?_, d.inIdentity⟩
  have h := d.isTransporter.precomp e.inv
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h

/-- The construction for actual standard split-torus maps, with no change in
the supplied field transporter or its identity-component condition. -/
def etaleIdentityTransporterOfSplitTorus {I : Type u} [Fintype I] [DecidableEq I]
    (j₁ j₂ : splitTorus (Spec R) I ⟶ G) [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (s : Spec R) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec R) (hb : b default = s)
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg₀ : IsTransporter ((GroupScheme.baseChange b).map j₁)
      ((GroupScheme.baseChange b).map j₂) g₀)
    (hidentity : Set.range g₀.left ⊆ IdentityComponent.identitySet
      ((GroupScheme.baseChange b).obj G)) : EtaleIdentityTransporterData j₁ j₂ s :=
  etaleIdentityTransporterOfSourceIso j₁ j₂ hG s
    (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))) b hb g₀ hg₀ hidentity

namespace EtaleIdentityTransporterData

variable {i₁ i₂} {s : Spec R} (d : EtaleIdentityTransporterData i₁ i₂ s)

/-- Compare the mapped terminal test with the chosen etale projection. -/
def identityComparison :
    (Over.map d.projection).obj (Over.mk (𝟙 (Spec d.neighbourhoodRing))) ⟶
      Over.mk d.projection :=
  Over.homMk (𝟙 _) (by simp)

/-- The actual section of the group pulled back to the etale neighbourhood. -/
def baseChangedSection : Over.mk (𝟙 (Spec d.neighbourhoodRing)) ⟶
    ((GroupScheme.baseChange d.projection).obj G).X :=
  (Langlands.GroupScheme.baseChangePointsEquiv d.projection G _).symm
    (d.identityComparison ≫ d.pointMap)

/-- The actual pullback adjunction recovers the constructed point map. -/
theorem baseChangePointsEquiv_baseChangedSection :
    Langlands.GroupScheme.baseChangePointsEquiv d.projection G _ d.baseChangedSection =
      d.identityComparison ≫ d.pointMap :=
  MulEquiv.apply_symm_apply _ _

/-- The section satisfies the transporter equation for the actual pulled-back
maps on every refinement of every test scheme. -/
theorem baseChangedSection_isTransporter :
    IsTransporter ((GroupScheme.baseChange d.projection).map i₁)
      ((GroupScheme.baseChange d.projection).map i₂) d.baseChangedSection :=
  d.isTransporter.baseChange d.projection d.identityComparison _
    d.baseChangePointsEquiv_baseChangedSection

/-- The constructed section belongs to the actual relative identity component
after etale base change, with the all-test residue-fibre meaning. -/
theorem baseChangedSection_inIdentity [Smooth G.X.hom] :
    InRelativeIdentityComponent ((GroupScheme.baseChange d.projection).obj G)
      d.baseChangedSection := by
  apply RelativeIdentityComponent.inRelativeIdentityComponent_of_baseChangePointsEquiv
    G d.projection
  rw [d.baseChangePointsEquiv_baseChangedSection]
  exact InRelativeIdentityComponent.precomp G d.inIdentity d.identityComparison

/-- Projection from the actual pullback recovers the selected point map. -/
@[reassoc] theorem baseChangedSection_recovers :
    d.baseChangedSection.left ≫ pullback.fst G.X.hom d.projection = d.pointMap.left := by
  have he := congrArg Over.Hom.left d.baseChangePointsEquiv_baseChangedSection
  simpa only [Langlands.GroupScheme.baseChangePointsEquiv_left, Over.comp_left,
    identityComparison, Over.homMk_left, Category.id_comp] using he

end EtaleIdentityTransporterData

end PointwiseSchemeAction

end Langlands.GroupScheme
