import Langlands.Shimura.Coefficients.AssociatedComplex
import Langlands.Shimura.Coefficients.EtaleConstantAssociatedPullbackCoherence
import Langlands.Shimura.Coefficients.EtaleCrossCoverPullback
import Langlands.Shimura.Coefficients.VaryingCoverInverse
import Langlands.Geometry.EtaleCohomologyDiagram

/-! # Transport of associated coefficient sheaves along etale morphisms

An etale morphism `f : Z ⟶ X`, finite geometric torsors `Y` over `X` and `Y'` over `Z` with
module representations `M` and `M'` of their deck groups, and a common finite geometric torsor
over `Z` mapping equivariantly to the base change `f^* Y` and to `Y'`, together with an
equivariant coefficient map, give a map from the restriction along `f` of the associated sheaf
of `(Y, M)` to the associated sheaf of `(Y', M')`. The map is characterized by its effect on
sections over the common cover; it does not depend on the common cover, and it satisfies
identity and composition laws. See `EtaleAssociatedTransport.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]

set_option hygiene false in
local notation "constant" Z:max => constantSheaf (Scheme.smallEtaleTopology Z) (ModuleCat.{u} R)

/-! ## Cross-cover maps on sections over the cover -/

/-- A cross-cover map followed by the invariant inclusion: restrict sections along the cover map
and apply the coefficient map. The cover and coefficient maps are given by their underlying
morphisms `a₀` and `c₀`. -/
theorem etaleCrossCoverMap_inclusion {X : Scheme.{u}} {G H : Type u} [Group G]
    [Group H] {Y : Action X.Etale G} {Y' : Action X.Etale H} (φ : H →* G)
    (a : Y' ⟶ (Action.res X.Etale φ).obj Y) (a₀ : Y'.V ⟶ Y.V) (ha : a.hom = a₀)
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) (c₀ : M.V ⟶ N.V) (hc : c.hom = c₀) :
    etaleCrossCoverMap X φ a c ≫ etaleAssociatedInclusion X Y' N =
      etaleAssociatedInclusion X Y M ≫
        coverPullback (Scheme.smallEtaleTopology X) a₀ ((constant X).obj M.V) ≫
        (productSheaf (Scheme.smallEtaleTopology X) Y'.V).map ((constant X).map c₀) := by
  subst ha hc
  exact crossCoverMap_inclusion _ φ a _

/-- With the identity coefficient map, a cross-cover map followed by the invariant inclusion is
restriction of sections along the cover map. -/
theorem etaleCrossCoverMap_id_inclusion {X : Scheme.{u}} {G H : Type u} [Group G]
    [Group H] {Y : Action X.Etale G} {Y' : Action X.Etale H} (φ : H →* G)
    (a : Y' ⟶ (Action.res X.Etale φ).obj Y) (a₀ : Y'.V ⟶ Y.V) (ha : a.hom = a₀)
    (M : Action (ModuleCat.{u} R) G) :
    etaleCrossCoverMap X φ a (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M)) ≫
        etaleAssociatedInclusion X Y' ((Action.res (ModuleCat.{u} R) φ).obj M) =
      etaleAssociatedInclusion X Y M ≫
        coverPullback (Scheme.smallEtaleTopology X) a₀ ((constant X).obj M.V) := by
  rw [etaleCrossCoverMap_inclusion φ a a₀ ha (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M))
    (𝟙 M.V) rfl]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The same-group form of `etaleCrossCoverMap_id_inclusion`, with the identity map of `M`. -/
theorem etaleCrossCoverMap_id_inclusion_self {X : Scheme.{u}} {G : Type u} [Group G]
    {Y Y' : Action X.Etale G} (a : Y' ⟶ (Action.res X.Etale (MonoidHom.id G)).obj Y)
    (a₀ : Y'.V ⟶ Y.V) (ha : a.hom = a₀) (M : Action (ModuleCat.{u} R) G) :
    etaleCrossCoverMap X (MonoidHom.id G) a (𝟙 M) ≫ etaleAssociatedInclusion X Y' M =
      etaleAssociatedInclusion X Y M ≫
        coverPullback (Scheme.smallEtaleTopology X) a₀ ((constant X).obj M.V) :=
  etaleCrossCoverMap_id_inclusion (MonoidHom.id G) a a₀ ha M

/-! ## Base change of cover maps -/

/-- The base change along `g` of a morphism of underlying cover objects, between the underlying
objects of the base-changed covers. -/
def etaleCoverMapPullback {Z W : Scheme.{u}} (g : W ⟶ Z) {H₁ H₂ : Type u} [Group H₁] [Group H₂]
    {A : Action Z.Etale H₁} {B : Action Z.Etale H₂} (a : A.V ⟶ B.V) :
    ((etaleTorsorPullbackFunctor g H₁).obj A).V ⟶ ((etaleTorsorPullbackFunctor g H₂).obj B).V :=
  (etaleObjectPullback g).map a

/-- The underlying morphism of the comparison of base change along a composite with iterated
base change. -/
def etaleTorsorPullbackCompMap {X Z W : Scheme.{u}} (f : Z ⟶ X) (g : W ⟶ Z) {G : Type u}
    [Group G] (Y : Action X.Etale G) :
    ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y).V ⟶
      ((etaleTorsorPullbackFunctor g G).obj ((etaleTorsorPullbackFunctor f G).obj Y)).V :=
  ((etaleTorsorPullbackComp f G g).hom.app Y).hom

/-- The underlying morphism of the identification of base change along the identity. -/
def etaleTorsorPullbackIdMap (X : Scheme.{u}) {G : Type u} [Group G] (Y : Action X.Etale G) :
    ((etaleTorsorPullbackFunctor (𝟙 X) G).obj Y).V ⟶ Y.V :=
  ((etaleTorsorPullbackId X G).hom.app Y).hom

/-! ## Transport data -/

/-- A transport datum from the associated sheaf of `(Y, M)` on `X` to the associated sheaf of
`(Y', M')` on `Z`, along a morphism `f : Z ⟶ X`: a finite geometric torsor `cover` over `Z`, with
deck group mapping to both deck groups, maps from `cover` to the base change `f^* Y` and to `Y'`,
and a map between the coefficient modules, all equivariant for the deck group of `cover`. -/
structure EtaleTransportDatum {X Z : Scheme.{u}} (f : Z ⟶ X)
    {G H : Type u} [Group G] [Group H] (Y : Action X.Etale G) (Y' : Action Z.Etale H)
    (M : Action (ModuleCat.{u} R) G) (M' : Action (ModuleCat.{u} R) H) where
  /-- The deck group of the common cover. -/
  group : Type u
  [instGroup : Group group]
  /-- The deck group map to the source deck group. -/
  toSourceGroup : group →* G
  /-- The deck group map to the target deck group. -/
  toTargetGroup : group →* H
  /-- The common cover of `Z`. -/
  cover : Action Z.Etale group
  isFiniteGeometricTorsor : IsFiniteGeometricTorsor Z cover
  /-- The map to the base change of the source cover. -/
  toSource : cover.V ⟶ ((etaleTorsorPullbackFunctor f G).obj Y).V
  toSource_comm : ∀ h : group, cover.ρ h ≫ toSource =
    toSource ≫ ((etaleTorsorPullbackFunctor f G).obj Y).ρ (toSourceGroup h)
  /-- The map to the target cover. -/
  toTarget : cover.V ⟶ Y'.V
  toTarget_comm : ∀ h : group, cover.ρ h ≫ toTarget = toTarget ≫ Y'.ρ (toTargetGroup h)
  /-- The coefficient map. -/
  coefficient : M.V ⟶ M'.V
  coefficient_comm : ∀ h : group, M.ρ (toSourceGroup h) ≫ coefficient =
    coefficient ≫ M'.ρ (toTargetGroup h)

attribute [instance] EtaleTransportDatum.instGroup

namespace EtaleTransportDatum

variable {X Z : Scheme.{u}} {f : Z ⟶ X} {G H : Type u} [Group G] [Group H]
  {Y : Action X.Etale G} {Y' : Action Z.Etale H}
  {M : Action (ModuleCat.{u} R) G} {M' : Action (ModuleCat.{u} R) H}

/-- The map to the base change of the source cover, as an equivariant map. -/
def toSourceHom (t : EtaleTransportDatum (R := R) f Y Y' M M') :
    t.cover ⟶ (Action.res Z.Etale t.toSourceGroup).obj ((etaleTorsorPullbackFunctor f G).obj Y) :=
  ⟨t.toSource, t.toSource_comm⟩

/-- The map to the target cover, as an equivariant map. -/
def toTargetHom (t : EtaleTransportDatum (R := R) f Y Y' M M') :
    t.cover ⟶ (Action.res Z.Etale t.toTargetGroup).obj Y' :=
  ⟨t.toTarget, t.toTarget_comm⟩

/-- The coefficient map, as an equivariant map of restricted representations. -/
def coefficientHom (t : EtaleTransportDatum (R := R) f Y Y' M M') :
    (Action.res (ModuleCat.{u} R) t.toSourceGroup).obj M ⟶
      (Action.res (ModuleCat.{u} R) t.toTargetGroup).obj M' :=
  ⟨t.coefficient, t.coefficient_comm⟩

/-- The comparison of the target associated sheaf with the associated sheaf on the common
cover is invertible, since both covers are finite geometric torsors. -/
theorem isIso_targetComparison (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') :
    IsIso (etaleCrossCoverMap Z t.toTargetGroup t.toTargetHom
      (𝟙 ((Action.res (ModuleCat.{u} R) t.toTargetGroup).obj M'))) :=
  etaleAssociatedCoverComparison Z H t.group Y' t.cover hY' t.isFiniteGeometricTorsor
    t.toTargetGroup t.toTargetHom R M'

/-- Two maps into the target associated sheaf agree once they agree after the invariant
inclusion followed by restriction of sections to the common cover. -/
theorem hom_ext (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') {A : Sheaf (Scheme.smallEtaleTopology Z) (ModuleCat.{u} R)}
    {m₁ m₂ : A ⟶ (etaleAssociatedFunctor Z Y').obj M'}
    (h : m₁ ≫ etaleAssociatedInclusion Z Y' M' ≫
        coverPullback (Scheme.smallEtaleTopology Z) t.toTarget ((constant Z).obj M'.V) =
      m₂ ≫ etaleAssociatedInclusion Z Y' M' ≫
        coverPullback (Scheme.smallEtaleTopology Z) t.toTarget ((constant Z).obj M'.V)) :
    m₁ = m₂ := by
  have := t.isIso_targetComparison hY'
  rw [← etaleCrossCoverMap_id_inclusion t.toTargetGroup t.toTargetHom t.toTarget rfl M'] at h
  simp only [← Category.assoc] at h
  have h' := (cancel_mono (etaleAssociatedInclusion Z t.cover
    ((Action.res (ModuleCat.{u} R) t.toTargetGroup).obj M'))).1 h
  exact (cancel_mono _).1 h'

variable [Etale f]

/-- The transport map from the restriction along `f` of the associated sheaf of `(Y, M)` to the
associated sheaf of `(Y', M')`: compare the restriction with the associated sheaf of the base
change `f^* Y`, pass to the common cover applying the coefficient map, and invert the comparison
of the target associated sheaf with the common cover. -/
def sheafMap (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') :
    (EtalePullback.restriction f (ModuleCat.{u} R)).obj ((etaleAssociatedFunctor X Y).obj M) ⟶
      (etaleAssociatedFunctor Z Y').obj M' :=
  haveI := t.isIso_targetComparison hY'
  (etaleConstantAssociatedPullback f R Y).hom.app M ≫
    etaleCrossCoverMap Z t.toSourceGroup t.toSourceHom t.coefficientHom ≫
    inv (etaleCrossCoverMap Z t.toTargetGroup t.toTargetHom
      (𝟙 ((Action.res (ModuleCat.{u} R) t.toTargetGroup).obj M')))

/-- The transport map followed by the comparison of the target with the common cover is the
base-change comparison followed by the cross-cover map of the source. -/
@[reassoc] theorem sheafMap_targetComparison (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') :
    t.sheafMap hY' ≫ etaleCrossCoverMap Z t.toTargetGroup t.toTargetHom
        (𝟙 ((Action.res (ModuleCat.{u} R) t.toTargetGroup).obj M')) =
      (etaleConstantAssociatedPullback f R Y).hom.app M ≫
        etaleCrossCoverMap Z t.toSourceGroup t.toSourceHom t.coefficientHom := by
  have := t.isIso_targetComparison hY'
  simp only [sheafMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Sections over the common cover: after the invariant inclusion and restriction of sections
along the target cover map, the transport map restricts the sections of the base change along
the source cover map and applies the coefficient map. -/
@[reassoc] theorem sheafMap_inclusion (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') :
    t.sheafMap hY' ≫ etaleAssociatedInclusion Z Y' M' ≫
        coverPullback (Scheme.smallEtaleTopology Z) t.toTarget ((constant Z).obj M'.V) =
      (etaleConstantAssociatedPullback f R Y).hom.app M ≫
        etaleAssociatedInclusion Z ((etaleTorsorPullbackFunctor f G).obj Y) M ≫
        coverPullback (Scheme.smallEtaleTopology Z) t.toSource ((constant Z).obj M.V) ≫
        (productSheaf (Scheme.smallEtaleTopology Z) t.cover.V).map
          ((constant Z).map t.coefficient) := by
  rw [← etaleCrossCoverMap_id_inclusion t.toTargetGroup t.toTargetHom t.toTarget rfl M',
    sheafMap_targetComparison_assoc,
    etaleCrossCoverMap_inclusion t.toSourceGroup t.toSourceHom t.toSource rfl
      t.coefficientHom t.coefficient rfl]

/-- The transport map does not depend on the common cover: a map of covers compatible with both
cover maps, together with equal coefficient maps, gives the same transport map. -/
theorem sheafMap_eq_of_refines (t₁ t₂ : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') (w : t₁.cover.V ⟶ t₂.cover.V)
    (hs : w ≫ t₂.toSource = t₁.toSource) (ht : w ≫ t₂.toTarget = t₁.toTarget)
    (hc : t₁.coefficient = t₂.coefficient) :
    t₁.sheafMap hY' = t₂.sheafMap hY' := by
  apply t₁.hom_ext hY'
  rw [t₁.sheafMap_inclusion, ← ht, coverPullback_comp, t₂.sheafMap_inclusion_assoc,
    ← coverPullback_natural, ← coverPullback_comp_assoc, hs, hc]

/-- Scaling the coefficient map by `n` scales the transport map by `n`, also when the common
cover is changed along a compatible map of covers. -/
theorem sheafMap_eq_nsmul_of_refines (t₁ t₂ : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') (w : t₁.cover.V ⟶ t₂.cover.V)
    (hs : w ≫ t₂.toSource = t₁.toSource) (ht : w ≫ t₂.toTarget = t₁.toTarget) (n : ℕ)
    (hc : t₁.coefficient = n • t₂.coefficient) :
    t₁.sheafMap hY' = n • t₂.sheafMap hY' := by
  apply t₁.hom_ext hY'
  rw [t₁.sheafMap_inclusion, Preadditive.nsmul_comp, ← ht, coverPullback_comp,
    t₂.sheafMap_inclusion_assoc, ← coverPullback_natural, ← coverPullback_comp_assoc, hs, hc,
    Functor.map_nsmul, Functor.map_nsmul]
  simp only [Preadditive.comp_nsmul]

/-- Transport along equal morphisms: the identification of the restrictions along equal
morphisms followed by one transport map is another, when their common covers are related by a
map compatible with the cover maps and their coefficient maps agree. -/
theorem sheafMap_congr {f₁ f₂ : Z ⟶ X} [Etale f₁] [Etale f₂] (h : f₁ = f₂)
    (t₁ : EtaleTransportDatum (R := R) f₁ Y Y' M M')
    (t₂ : EtaleTransportDatum (R := R) f₂ Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') (w : t₁.cover.V ⟶ t₂.cover.V)
    (hs : w ≫ t₂.toSource = t₁.toSource ≫
      eqToHom (congrArg (fun k => ((etaleTorsorPullbackFunctor k G).obj Y).V) h))
    (ht : w ≫ t₂.toTarget = t₁.toTarget) (hc : t₁.coefficient = t₂.coefficient) :
    (EtalePullback.restrictionCongr R h).hom.app _ ≫ t₂.sheafMap hY' = t₁.sheafMap hY' := by
  subst h
  simp only [eqToHom_refl, Category.comp_id] at hs
  rw [sheafMap_eq_of_refines t₁ t₂ hY' w hs ht hc]
  simp [EtalePullback.restrictionCongr]

/-- Restricting the transport map along a further etale morphism `g`: its sections over the base
change of the common cover. -/
@[reassoc] theorem restriction_sheafMap_inclusion (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (hY' : IsFiniteGeometricTorsor Z Y') {W : Scheme.{u}} (g : W ⟶ Z) [Etale g] :
    (EtalePullback.restriction g (ModuleCat.{u} R)).map (t.sheafMap hY') ≫
        (etaleConstantAssociatedPullback g R Y').hom.app M' ≫
        etaleAssociatedInclusion W ((etaleTorsorPullbackFunctor g H).obj Y') M' ≫
        coverPullback (Scheme.smallEtaleTopology W)
          (etaleCoverMapPullback g (A := t.cover) t.toTarget) ((constant W).obj M'.V) =
      (EtalePullback.restriction g (ModuleCat.{u} R)).map
          ((etaleConstantAssociatedPullback f R Y).hom.app M) ≫
        (etaleConstantAssociatedPullback g R ((etaleTorsorPullbackFunctor f G).obj Y)).hom.app M ≫
        etaleAssociatedInclusion W
          ((etaleTorsorPullbackFunctor g G).obj ((etaleTorsorPullbackFunctor f G).obj Y)) M ≫
        coverPullback (Scheme.smallEtaleTopology W)
          (etaleCoverMapPullback g (A := t.cover) t.toSource) ((constant W).obj M.V) ≫
        (productSheaf (Scheme.smallEtaleTopology W)
          ((etaleTorsorPullbackFunctor g t.group).obj t.cover).V).map
          ((constant W).map t.coefficient) := by
  rw [← etaleCrossCoverMap_id_inclusion t.toTargetGroup
      ((etaleTorsorPullbackFunctor g t.group).map t.toTargetHom)
      (etaleCoverMapPullback g (A := t.cover) t.toTarget) rfl M',
    ← etaleConstantAssociatedPullback_crossCover_assoc g R t.toTargetGroup t.toTargetHom,
    ← CategoryTheory.Functor.map_comp_assoc, t.sheafMap_targetComparison hY',
    CategoryTheory.Functor.map_comp_assoc, etaleConstantAssociatedPullback_crossCover_assoc,
    etaleCrossCoverMap_inclusion t.toSourceGroup
      ((etaleTorsorPullbackFunctor g t.group).map t.toSourceHom)
      (etaleCoverMapPullback g (A := t.cover) t.toSource) rfl t.coefficientHom t.coefficient rfl]

/-- Identity law: a transport datum along the identity whose cover maps agree after the
identification of the base change along the identity, and whose coefficient map is the identity,
gives the identification of the restriction along the identity. -/
theorem sheafMap_id {Y : Action X.Etale G} {M : Action (ModuleCat.{u} R) G}
    (t : EtaleTransportDatum (R := R) (𝟙 X) Y Y M M) (hY : IsFiniteGeometricTorsor X Y)
    (hv : t.toSource ≫ etaleTorsorPullbackIdMap X Y = t.toTarget)
    (hc : t.coefficient = 𝟙 M.V) :
    t.sheafMap hY = (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app _ := by
  apply t.hom_ext hY
  rw [t.sheafMap_inclusion, etaleConstantAssociatedPullback_id_assoc,
    reassoc_of% etaleCrossCoverMap_id_inclusion_self (Y := Y)
      (Y' := (etaleTorsorPullbackFunctor (𝟙 X) G).obj Y) ((etaleTorsorPullbackId X G).hom.app Y)
      (etaleTorsorPullbackIdMap X Y) rfl M,
    ← hv, coverPullback_comp, hc, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Composition law: transport data along `f`, along `g` and along `g ≫ f` whose common covers
are related by maps compatible with all cover maps, and whose coefficient maps compose, give
transport maps composing through the identification of iterated restriction. -/
theorem sheafMap_comp {W : Scheme.{u}} (g : W ⟶ Z) [Etale g] {K : Type u} [Group K]
    {Y'' : Action W.Etale K} {M'' : Action (ModuleCat.{u} R) K}
    (t : EtaleTransportDatum (R := R) f Y Y' M M')
    (t' : EtaleTransportDatum (R := R) g Y' Y'' M' M'')
    (t'' : EtaleTransportDatum (R := R) (g ≫ f) Y Y'' M M'')
    (hY' : IsFiniteGeometricTorsor Z Y') (hY'' : IsFiniteGeometricTorsor W Y'')
    (w : t''.cover.V ⟶ ((etaleTorsorPullbackFunctor g t.group).obj t.cover).V)
    (w' : t''.cover.V ⟶ t'.cover.V)
    (hw : w ≫ etaleCoverMapPullback g (A := t.cover) t.toTarget = w' ≫ t'.toSource)
    (hv : w' ≫ t'.toTarget = t''.toTarget)
    (hu : w ≫ etaleCoverMapPullback g (A := t.cover) t.toSource =
      t''.toSource ≫ etaleTorsorPullbackCompMap f g Y)
    (hc : t.coefficient ≫ t'.coefficient = t''.coefficient) :
    (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app _ ≫ t''.sheafMap hY'' =
      (EtalePullback.restriction g (ModuleCat.{u} R)).map (t.sheafMap hY') ≫
        t'.sheafMap hY'' := by
  apply t''.hom_ext hY''
  simp only [Category.assoc]
  rw [t''.sheafMap_inclusion, etaleConstantAssociatedPullback_comp_assoc,
    reassoc_of% etaleCrossCoverMap_id_inclusion_self
      (Y := (etaleTorsorPullbackFunctor g G).obj ((etaleTorsorPullbackFunctor f G).obj Y))
      (Y' := (etaleTorsorPullbackFunctor (g ≫ f) G).obj Y)
      ((etaleTorsorPullbackComp f G g).hom.app Y)
      (etaleTorsorPullbackCompMap f g Y) rfl M,
    ← coverPullback_comp_assoc _ (etaleTorsorPullbackCompMap f g Y) t''.toSource, ← hu,
    ← hv, coverPullback_comp _ t'.toTarget w', t'.sheafMap_inclusion_assoc,
    ← coverPullback_natural,
    ← coverPullback_comp_assoc _ t'.toSource w', ← hw,
    coverPullback_comp_assoc _ (etaleCoverMapPullback g (A := t.cover) t.toTarget) w,
    t.restriction_sheafMap_inclusion_assoc hY' g, ← coverPullback_natural_assoc,
    ← coverPullback_comp_assoc _ (etaleCoverMapPullback g (A := t.cover) t.toSource) w,
    ← (productSheaf _ _).map_comp, ← (constantSheaf _ _).map_comp, hc]

end EtaleTransportDatum

end Langlands.Shimura.Coefficients
