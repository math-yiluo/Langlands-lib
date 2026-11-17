import Langlands.GroupScheme.DvrStableGroup
import Langlands.GroupScheme.DvrFiniteSmoothCoverStatement

/-! # Base change and composition for finite smooth DVR covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.DvrCoverAssembly

section GenericBaseChange

variable {R R' K : Type u} [CommRing R]
  [CommRing R'] [IsDomain R'] [Field K] [Algebra R K] [IsFractionRing R K]
  (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  [Flat b] [Surjective b]

theorem exists_generic_factor :
    ∃ a : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of K),
      a ≫ Spec.algebraMap R K = Spec.algebraMap R' (FractionRing R') ≫ b := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  have hφ : Function.Injective φ.hom :=
    ((flat_and_surjective_SpecMap_iff φ).mp ⟨inferInstance, inferInstance⟩).injective
  let ψ : R →+* FractionRing R' := (algebraMap R' (FractionRing R')).comp φ.hom
  have hψ : Function.Injective ψ := (IsFractionRing.injective R' (FractionRing R')).comp hφ
  let a : K →+* FractionRing R' := IsFractionRing.lift hψ
  have ha : a.comp (algebraMap R K) = ψ := by
    apply RingHom.ext
    intro r
    exact IsFractionRing.lift_algebraMap (K := K) hψ r
  refine ⟨Spec.map (CommRingCat.ofHom a), ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : R →+* FractionRing R' => Spec.map (CommRingCat.ofHom f)) ha

/-- The actual map between chosen fraction-field spectra induced by a faithfully flat base map. -/
def genericFactor : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of K) :=
  Classical.choose (exists_generic_factor (K := K) b)

@[reassoc]
theorem genericFactor_fac :
    genericFactor (K := K) b ≫ Spec.algebraMap R K =
      Spec.algebraMap R' (FractionRing R') ≫ b :=
  Classical.choose_spec (exists_generic_factor (K := K) b)

/-- Affine generic fibres remain affine after a faithfully flat domain extension. -/
theorem affine_generic (X : Over (Spec (CommRingCat.of R)))
    [IsAffineHom ((Over.pullback (Spec.algebraMap R K)).obj X).hom] :
    IsAffineHom ((Over.pullback (Spec.algebraMap R' (FractionRing R'))).obj
      ((Over.pullback b).obj X)).hom := by
  have : IsAffineHom (pullback.snd X.hom (Spec.algebraMap R K)) :=
    inferInstanceAs (IsAffineHom ((Over.pullback (Spec.algebraMap R K)).obj X).hom)
  have : IsAffineHom (pullback.snd X.hom
      (genericFactor (K := K) b ≫ Spec.algebraMap R K)) := by
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd]
    infer_instance
  rw [genericFactor_fac] at this
  change IsAffineHom (pullback.snd (pullback.snd X.hom b) _)
  rw [← pullbackLeftPullbackSndIso_hom_snd]
  infer_instance

/-- Smooth generic fibres remain smooth after a faithfully flat domain extension. -/
theorem smooth_generic (X : Over (Spec (CommRingCat.of R)))
    [Smooth ((Over.pullback (Spec.algebraMap R K)).obj X).hom] :
    Smooth ((Over.pullback (Spec.algebraMap R' (FractionRing R'))).obj
      ((Over.pullback b).obj X)).hom := by
  have : Smooth (pullback.snd X.hom (Spec.algebraMap R K)) :=
    inferInstanceAs (Smooth ((Over.pullback (Spec.algebraMap R K)).obj X).hom)
  have : Smooth (pullback.snd X.hom
      (genericFactor (K := K) b ≫ Spec.algebraMap R K)) := by
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd]
    infer_instance
  rw [genericFactor_fac] at this
  change Smooth (pullback.snd (pullback.snd X.hom b) _)
  rw [← pullbackLeftPullbackSndIso_hom_snd]
  infer_instance

end GenericBaseChange

/-- Actual witnesses for a finite smooth cover, including their DVR coefficient extension. -/
structure Cover {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) where
  ring : Type u
  [comm : CommRing ring]
  [domain : IsDomain ring]
  [dvr : IsDiscreteValuationRing ring]
  base : Spec (CommRingCat.of ring) ⟶ Spec (CommRingCat.of R)
  flat : Flat base
  surjective : Surjective base
  group : GroupScheme (Spec (CommRingCat.of ring))
  map : group ⟶ (baseChange base).obj G
  smooth : Smooth group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  separated : IsSeparated group.X.hom
  affineGeneric : IsAffineHom
    ((baseChange (Spec.algebraMap ring (FractionRing ring))).obj group).X.hom
  finite : IsFinite map.hom.hom.left
  map_surjective : Surjective map.hom.hom.left

attribute [instance] Cover.comm Cover.domain Cover.dvr

namespace Cover

/-- Compose a cover with a finite surjective group map over an earlier DVR extension. -/
def comp {R R' : Type u} [CommRing R] [CommRing R']
    {G : GroupScheme (Spec (CommRingCat.of R))}
    {P : GroupScheme (Spec (CommRingCat.of R'))}
    (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    [Flat b] [Surjective b] (q : P ⟶ (baseChange b).obj G)
    (hqfinite : IsFinite q.hom.hom.left) (hqsurjective : Surjective q.hom.hom.left)
    (D : Cover P) : Cover G := by
  let e : (baseChange (D.base ≫ b)).obj G ≅
      (baseChange D.base).obj ((baseChange b).obj G) :=
    (Functor.mapGrpNatIso (Over.pullbackComp D.base b)).app G ≪≫
      Functor.mapGrpCompIso.app G
  let q' : D.group ⟶ (baseChange (D.base ≫ b)).obj G :=
    D.map ≫ (baseChange D.base).map q ≫ e.inv
  have : Flat D.base := D.flat
  have : Surjective D.base := D.surjective
  have : IsFinite D.map.hom.hom.left := D.finite
  have : Surjective D.map.hom.hom.left := D.map_surjective
  have : IsFinite ((baseChange D.base).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) D.base q.hom.hom hqfinite
  have : Surjective ((baseChange D.base).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) D.base q.hom.hom hqsurjective
  have hfinite : IsFinite q'.hom.hom.left := by
    change IsFinite (D.map.hom.hom.left ≫
      ((baseChange D.base).map q).hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  have hsurjective : Surjective q'.hom.hom.left := by
    change Surjective (D.map.hom.hom.left ≫
      ((baseChange D.base).map q).hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  exact {
    ring := D.ring
    base := D.base ≫ b
    flat := inferInstance
    surjective := inferInstance
    group := D.group
    map := q'
    smooth := D.smooth
    quasiCompact := D.quasiCompact
    separated := D.separated
    affineGeneric := D.affineGeneric
    finite := hfinite
    map_surjective := hsurjective }

end Cover

section SmoothGeneric

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Flat G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  [IsSeparated G.X.hom]
  [Smooth ((baseChange (Spec.algebraMap R (FractionRing R))).obj G).X.hom]
  [IsAffineHom ((baseChange (Spec.algebraMap R (FractionRing R))).obj G).X.hom]

theorem nonempty_cover_of_stable
    (hStable : Langlands.AlgebraicGeometry.DvrStableNormalizationStatement.{u}) :
    Nonempty (Cover G) := by
  have : Smooth ((Over.pullback (Spec.algebraMap R (FractionRing R))).obj G.X).hom :=
    inferInstanceAs (Smooth ((baseChange (Spec.algebraMap R (FractionRing R))).obj G).X.hom)
  have : IsAffineHom ((Over.pullback (Spec.algebraMap R (FractionRing R))).obj G.X).hom :=
    inferInstanceAs (IsAffineHom ((baseChange (Spec.algebraMap R (FractionRing R))).obj G).X.hom)
  obtain ⟨R', cR', dR', hDvr, b, hbflat, hbsurj, ⟨M⟩⟩ :=
    hStable R G.X inferInstance inferInstance inferInstance inferInstance inferInstance
  let := cR'
  let := dR'
  let := hDvr
  let := hbflat
  let := hbsurj
  let G' := (baseChange b).obj G
  have : LocallyOfFiniteType G'.X.hom := by change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have : QuasiCompact G'.X.hom := by change QuasiCompact (pullback.snd _ _); infer_instance
  have : IsSeparated G'.X.hom := by change IsSeparated (pullback.snd _ _); infer_instance
  have : IsAffineHom ((baseChange (Spec.algebraMap R' (FractionRing R'))).obj G').X.hom :=
    affine_generic (K := FractionRing R) b G.X
  exact ⟨{
    ring := R'
    base := b
    flat := hbflat
    surjective := hbsurj
    group := DvrStableGroup.group G' M
    map := DvrStableGroup.map G' M
    smooth := DvrStableGroup.smooth G' M
    quasiCompact := DvrStableGroup.quasiCompact G' M
    separated := DvrStableGroup.separated G' M
    affineGeneric := DvrStableGroup.affine_baseChange G' M _
    finite := DvrStableGroup.finite_map G' M
    map_surjective := DvrStableGroup.surjective_map G' M }⟩

/-- Select the actual smooth-generic cover constructed from stable normalization. -/
def smoothGenericCover
    (hStable : Langlands.AlgebraicGeometry.DvrStableNormalizationStatement.{u}) : Cover G :=
  Classical.choice (nonempty_cover_of_stable G hStable)

end SmoothGeneric

end Langlands.GroupScheme.DvrCoverAssembly
