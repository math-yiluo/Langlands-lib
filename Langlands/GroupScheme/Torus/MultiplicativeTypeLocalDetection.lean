import Langlands.AlgebraicGeometry.LocalEtaleLimit
import Langlands.AlgebraicGeometry.FlatAffineLimitModel
import Langlands.GroupScheme.Descent.AffineLimitIsomorphism
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupReduction
import Langlands.GroupScheme.Torus.DiagonalizableFppfQuotient
import Mathlib.CategoryTheory.Filtered.Final

/-! # Detecting multiplicative type on supplied local limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.LocalMultiplicativeType

open RelativeMultiplicativeType
open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.TargetLimit

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- A point of the base has an affine fppf diagonalizing piece whenever the
group is of relative multiplicative type. -/
theorem exists_affine_diagonalizing_piece
    {T : Scheme.{u}} (b : T ⟶ S)
    (hG : IsMultiplicativeType ((baseChange b).obj G)) (x : T) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (f : W ⟶ T),
      Flat f ∧ LocallyOfFinitePresentation f ∧
      ∃ w : W, f w = x ∧ IsDiagonalizable ((baseChange (f ≫ b)).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
  obtain ⟨j, w, hw⟩ := (𝒰.X i).affineCover.exists_eq z
  have hfi := 𝒰.map_prop i
  have hfj := (𝒰.X i).affineCover.map_prop j
  have : Flat (𝒰.f i) := hfi.1
  have : LocallyOfFinitePresentation (𝒰.f i) := hfi.2
  let f := (𝒰.X i).affineCover.f j ≫ 𝒰.f i
  have hdiag : IsDiagonalizable ((baseChange f).obj ((baseChange b).obj G)) :=
    IsDiagonalizable.of_iso (baseChangeCompIso (𝒰.f i) ((𝒰.X i).affineCover.f j) _)
      ((h𝒰 i).baseChange ((𝒰.X i).affineCover.f j))
  exact ⟨(𝒰.X i).affineCover.X j, inferInstance, f, inferInstance, inferInstance,
    w, by change 𝒰.f i ((𝒰.X i).affineCover.f j w) = x; rw [hw, hz],
    IsDiagonalizable.of_iso (baseChangeCompIso b f G) hdiag⟩

variable [IsAffine S] [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
  {s : S} (L : LocalEtaleLimit S s)

/-- A relative multiplicative-type presentation over a supplied local
limit spreads to an affine fppf diagonalizing neighbourhood of the point. -/
theorem exists_fppf_diagonalizing_neighbourhood
    (hG : IsMultiplicativeType ((baseChange L.baseMap).obj G)) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (b : U ⟶ S),
      Flat b ∧ LocallyOfFinitePresentation b ∧ s ∈ Set.range b ∧
        IsDiagonalizable ((baseChange b).obj G) := by
  obtain ⟨W, hW, f, hf, hfp, w, hw, hdiag⟩ :=
    exists_affine_diagonalizing_piece G L.baseMap hG (IsLocalRing.closedPoint L.ring)
  let := hW
  let := hf
  let := hfp
  let c := Cone.mk (Spec (CommRingCat.of L.ring)) L.projection
  let M := FlatAffineLimit.model f L.diagram c L.isLimit (Iso.refl _)
  have hM : IsPullback M.projection f M.map (L.projection.app M.level) := by
    have h := M.isPullback
    change IsPullback M.projection f M.map (𝟙 _ ≫ L.projection.app M.level) at h
    rw [Category.id_comp] at h
    exact h
  have : IsAffine M.source := M.affine
  have : Flat M.map := M.flat
  have : LocallyOfFinitePresentation M.map := M.finitePresentation
  let D := Over.forget M.level ⋙ L.diagram
  have : ∀ i : Over M.level, IsAffine (D.obj i) := fun i =>
    inferInstanceAs (IsAffine (L.diagram.obj i.left))
  let t : D ⟶ (Functor.const (Over M.level)).obj (L.diagram.obj M.level) :=
    { app i := L.diagram.map i.hom
      naturality := by
        intro i j r
        change L.diagram.map r.left ≫ L.diagram.map j.hom = L.diagram.map i.hom ≫ 𝟙 _
        rw [← L.diagram.map_comp, r.w, Category.comp_id] }
  let cD := c.whisker (Over.forget M.level)
  have hcD : IsLimit cD := (Functor.Initial.isLimitWhiskerEquiv _ c).symm L.isLimit
  have hpD : ∀ i, cD.π.app i ≫ t.app i = L.projection.app M.level :=
    fun i => c.w i.hom
  have : IsAffine (L.diagram.obj M.level) := L.affine M.level
  have : IsAffineHom M.map := inferInstance
  let E := diagram D t M.map
  have : ∀ i, IsAffine (E.obj i) := fun i => by
    have : IsAffine (D.obj i) := inferInstanceAs (IsAffine (L.diagram.obj i.left))
    change IsAffine (pullback (t.app i) M.map)
    infer_instance
  let cE := coneOfPullback D t M.map cD (L.projection.app M.level) hpD hM.flip
  have hcE : IsLimit cE :=
    isLimitConeOfPullback D t M.map cD (L.projection.app M.level) hpD hM.flip hcD
  let u : E ⟶ (Functor.const _).obj S :=
    comparison D t M.map ≫ (Functor.const _).map (M.map ≫ L.structural.app M.level)
  have hpu : ∀ i, cE.π.app i ≫ u.app i = f ≫ L.baseMap := by
    intro i
    change cE.π.app i ≫ pullback.snd (t.app i) M.map ≫
      M.map ≫ L.structural.app M.level = _
    rw [coneOfPullback_π_snd_assoc]
    rw [hM.w_assoc, L.compatible]
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := hdiag
  let := hΛ
  let := hfg
  let H := diagonalizable S Λ
  have hHaff : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd _ _)
    infer_instance
  have hHfp : LocallyOfFinitePresentation H.X.hom := by
    have hfpZ := Diagonalizable.locallyOfFinitePresentation (CommRingCat.of (ULift.{u} ℤ)) Λ
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let el : (baseChange (f ≫ L.baseMap)).obj G ≅
      (baseChange (f ≫ L.baseMap)).obj H :=
    e ≪≫ (diagonalizableBaseChangeIso (f ≫ L.baseMap) Λ).symm
  obtain ⟨i, ⟨ei⟩⟩ := Descent.AffineLimit.exists_level_groupIso E u cE hcE
    (f ≫ L.baseMap) hpu G H el
  have hui : u.app i = pullback.fst (t.app i) M.map ≫ L.structural.app i.left := by
    change pullback.snd (t.app i) M.map ≫ M.map ≫ L.structural.app M.level = _
    rw [← pullback.condition_assoc]
    have hi := L.structural.naturality i.hom
    change L.diagram.map i.hom ≫ L.structural.app M.level = L.structural.app i.left ≫ 𝟙 S at hi
    have hi' : L.diagram.map i.hom ≫ L.structural.app M.level = L.structural.app i.left :=
      hi.trans (Category.comp_id (L.structural.app i.left))
    change pullback.fst (t.app i) M.map ≫
      (L.diagram.map i.hom ≫ L.structural.app M.level) = _
    rw [hi']
  have huflat : Flat (u.app i) := by rw [hui]; infer_instance
  have hufp : LocallyOfFinitePresentation (u.app i) := by rw [hui]; infer_instance
  have hpoint : u.app i (cE.π.app i w) = s := by
    have he := congrArg (fun v => v w) (hpu i)
    exact he.trans (by change L.baseMap (f w) = s; rw [hw, L.closedPoint_image])
  exact ⟨E.obj i, inferInstance, u.app i, huflat, hufp, ⟨cE.π.app i w, hpoint⟩,
    IsDiagonalizable.of_iso (ei ≪≫ diagonalizableBaseChangeIso (u.app i) Λ)
      ⟨Λ, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩⟩

/-- An actual affine fppf cover on which the group is diagonalizable. -/
structure AffineDiagonalizingCover where
  cover : Scheme.Cover.{u} Scheme.fppfPrecoverage S
  affine : ∀ i, IsAffine (cover.X i)
  diagonalizable : ∀ i, IsDiagonalizable ((baseChange (cover.f i)).obj G)

/-- Choose a diagonalizing cover from multiplicative type on one supplied
local limit at each point of an affine base. -/
def diagonalizingCover
    (hG : ∀ s : S, ∃ L : LocalEtaleLimit S s,
      IsMultiplicativeType ((baseChange L.baseMap).obj G)) : AffineDiagonalizingCover G := by
  classical
  have hn (s : S) : ∃ (U : Scheme.{u}) (_ : IsAffine U) (b : U ⟶ S),
      Flat b ∧ LocallyOfFinitePresentation b ∧ s ∈ Set.range b ∧
        IsDiagonalizable ((baseChange b).obj G) := by
    obtain ⟨L, hL⟩ := hG s
    exact exists_fppf_diagonalizing_neighbourhood G L hL
  choose U hU b hbflat hbfp hbcover hbdiag using hn
  let C : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers S U b
      (fun s => by obtain ⟨w, hw⟩ := hbcover s; exact ⟨s, w, hw⟩)
      (fun s => ⟨hbflat s, hbfp s⟩)
  exact ⟨C, hU, hbdiag⟩

/-- Multiplicative type on one supplied local limit at each point
implies relative multiplicative type over the affine base. -/
theorem of_pointwise_localBaseChange
    (hG : ∀ s : S, ∃ L : LocalEtaleLimit S s,
      IsMultiplicativeType ((baseChange L.baseMap).obj G)) : IsMultiplicativeType G :=
  ⟨(diagonalizingCover G hG).cover, (diagonalizingCover G hG).diagonalizable⟩

/-- Ordinary localization at every prime detects relative multiplicative
type over an affine spectrum. -/
theorem of_localizations {R : Type u} [CommRing R]
    (H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hH : ∀ p : PrimeSpectrum R,
      IsMultiplicativeType ((baseChange
        (Spec.algebraMap R (Localization.AtPrime p.asIdeal))).obj H)) :
    IsMultiplicativeType H :=
  of_pointwise_localBaseChange H (fun p => ⟨LocalEtaleLimit.ofLocalization R p, hH p⟩)

/-- The canonical ordinary local limit through a point of an affine scheme. -/
def localLimitOfAffine (S : Scheme.{u}) [IsAffine S] (s : S) : LocalEtaleLimit S s := by
  let L := LocalEtaleLimit.ofLocalization Γ(S, ⊤) (S.isoSpec.hom s)
  exact {
    ring := L.ring
    index := L.index
    diagram := L.diagram
    structural := L.structural ≫ (Functor.const _).map S.isoSpec.inv
    etale := fun i => by
      change Etale (L.structural.app i ≫ S.isoSpec.inv)
      infer_instance
    projection := L.projection
    baseMap := L.baseMap ≫ S.isoSpec.inv
    compatible := fun i => by
      change L.projection.app i ≫ (L.structural.app i ≫ S.isoSpec.inv) = _
      rw [← Category.assoc, L.compatible]
    isLimit := L.isLimit
    closedPoint_image := by
      change S.isoSpec.inv (L.baseMap (IsLocalRing.closedPoint L.ring)) = s
      rw [L.closedPoint_image]
      change (S.isoSpec.hom ≫ S.isoSpec.inv) s = s
      rw [Iso.hom_inv_id]
      rfl }

omit [IsAffine S] in
/-- An affine locally finitely presented group is of relative multiplicative
type if all its local affine base changes are of relative multiplicative type.
No existence premise for strict henselizations is needed. -/
theorem of_all_localBaseChanges
    (hG : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
      IsMultiplicativeType ((baseChange b).obj G)) : IsMultiplicativeType G := by
  apply IsMultiplicativeType.of_openCover S.affineCover
  intro i
  have : IsAffineHom ((baseChange (S.affineCover.f i)).obj G).X.hom := by
    change IsAffineHom (pullback.snd _ _)
    infer_instance
  have : LocallyOfFinitePresentation ((baseChange (S.affineCover.f i)).obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  apply of_pointwise_localBaseChange
  intro s
  let L := localLimitOfAffine (S.affineCover.X i) s
  refine ⟨L, ?_⟩
  exact IsMultiplicativeType.of_iso
    (baseChangeCompIso (S.affineCover.f i) L.baseMap G).symm
    (hG L.ring (L.baseMap ≫ S.affineCover.f i))

end Langlands.GroupScheme.LocalMultiplicativeType
