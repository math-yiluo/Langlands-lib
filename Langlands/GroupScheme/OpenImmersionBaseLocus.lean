import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.FlatClosedLocalIso

/-! # The base locus where a group monomorphism is an open immersion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

open SmoothMonoLocalIso Langlands.AlgebraicGeometry

variable {S T : Scheme.{u}} {H N : GroupScheme S} (f : H ⟶ N)
  [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
  [LocallyOfFiniteType N.X.hom] [Mono f.hom.hom.left]

private theorem mem_unitEtaleOpen_of_flat_fiber (s : S)
    (hf : Flat (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left)) :
    s ∈ unitEtaleOpen f := by
  let φ := f.hom.hom
  let x := η[H.X].left s
  have hx : N.X.hom (φ.left x) = s := by
    rw [← Scheme.Hom.comp_apply, Over.w φ]
    change H.X.hom (η[H.X].left s) = s
    rw [← Scheme.Hom.comp_apply, Over.w η[H.X]]
    rfl
  have : LocallyOfFinitePresentation φ.left := locallyOfFinitePresentation_hom f
  have hflat : (φ.left.stalkMap x).hom.Flat :=
    flat_stalkMap_of_flat_residueFiber_of_lft_target φ x (by rw [hx]; exact hf)
  let := (φ.left.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (N.X.left.presheaf.stalk (φ.left x))
      (H.X.left.presheaf.stalk x)) := φ.left.toLRSHom.prop x
  have : Module.Flat (N.X.left.presheaf.stalk (φ.left x))
      (H.X.left.presheaf.stalk x) := hflat
  have : Algebra.FormallyUnramified (N.X.left.presheaf.stalk (φ.left x))
      (H.X.left.presheaf.stalk x) := FormallyUnramified.stalkMap φ.left x
  exact Langlands.CommutativeAlgebra.formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation
    _ _ (stalkEssFinitePresentation _ _ φ.left x inferInstance)

private theorem isOpenImmersion_of_range_subset_unitEtaleOpen (b : T ⟶ S)
    (hb : Set.range b ⊆ unitEtaleOpen f) :
    IsOpenImmersion (((baseChange b).map f).hom.hom.left) := by
  let φ := f.hom.hom
  have : LocallyOfFinitePresentation φ.left := locallyOfFinitePresentation_hom f
  let U := schemeEtaleLocus φ.left
  let W : Over S := Over.mk (U.ι ≫ H.X.hom)
  let a : W ⟶ H.X := Over.homMk U.ι rfl
  let a' := (Over.pullback b).map a
  let f' := (baseChange b).map f
  have : Flat W.hom := inferInstanceAs (Flat (U.ι ≫ H.X.hom))
  have : Etale (a ≫ φ).left := etale_schemeEtaleLocus φ.left
  have : Flat ((Over.pullback b).obj W).hom :=
    inferInstanceAs (Flat (pullback.snd W.hom b))
  have : Surjective ((Over.pullback b).obj W).hom := by
    refine ⟨fun t => ?_⟩
    let u : U := ⟨η[H.X].left (b t), hb ⟨t, rfl⟩⟩
    have hu : W.hom u = b t := by
      change H.X.hom (η[H.X].left (b t)) = b t
      rw [← Scheme.Hom.comp_apply, Over.w η[H.X]]
      rfl
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := W.hom) (g := b) u t hu
    exact ⟨z, hz⟩
  have : Flat (a' ≫ f'.hom.hom).left := by
    change Flat (((Over.pullback b).map a) ≫ ((Over.pullback b).map φ)).left
    rw [← Functor.map_comp]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (RelativeIdentityComponent.overPullback_isPullback b (a ≫ φ)).flip inferInstance
  have : Flat ((baseChange b).obj H).X.hom :=
    inferInstanceAs (Flat (pullback.snd H.X.hom b))
  have : LocallyOfFinitePresentation f'.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (RelativeIdentityComponent.overPullback_isPullback b φ).flip inferInstance
  have : Mono f'.hom.hom.left :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms Scheme)
      (RelativeIdentityComponent.overPullback_isPullback b φ).flip inferInstance
  have : Flat f'.hom.hom.left := flat_of_flat_family f' a'
  exact IsOpenImmersion.of_flat_of_mono _

/-- A flat, locally finitely presented source and a locally finite-type target
allow open immersion of a group monomorphism to be tested at its unit.
The open obtained this way classifies all base changes making it an open immersion. -/
theorem range_subset_unitEtaleOpen_iff (b : T ⟶ S) :
    Set.range b ⊆ unitEtaleOpen f ↔
      IsOpenImmersion (((baseChange b).map f).hom.hom.left) := by
  refine ⟨isOpenImmersion_of_range_subset_unitEtaleOpen f b, ?_⟩
  rintro hb _ ⟨t, rfl⟩
  apply mem_unitEtaleOpen_of_flat_fiber f
  let e := Spec.map (b.residueFieldMap t)
  let := (b.residueFieldMap t).hom.toAlgebra
  obtain ⟨heS, heF, heQ⟩ := fieldExtension_fpqc (S.residueField (b t)) (T.residueField t)
  have h := RelativeIdentityComponent.fiberMap_isPullback b f.hom.hom t
  have hq := RelativeIdentityComponent.fiberComparison_isPullback b N.X t
  let P : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have he : P e := ⟨⟨heS, heF⟩, heQ⟩
  have hq' := MorphismProperty.of_isPullback (P := P) hq.flip he
  let : IsOpenImmersion (((Over.pullback (T.fromSpecResidueField t)).map
      ((Over.pullback b).map f.hom.hom)).left) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (RelativeIdentityComponent.overPullback_isPullback (T.fromSpecResidueField t)
        ((baseChange b).map f).hom.hom).flip hb
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Flat) (Q := P) h hq' inferInstance

/-- The condition that a group monomorphism becomes an open immersion is
represented by an actual open of the base. -/
def GroupMonomorphismOpenImmersionLocusStatement : Prop :=
  ∀ (S : Scheme.{u}) (H N : GroupScheme S) (f : H ⟶ N)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [LocallyOfFiniteType N.X.hom] [Mono f.hom.hom.left],
    ∃ U : S.Opens, ∀ (T : Scheme.{u}) (b : T ⟶ S),
      (∃ a : T ⟶ U.toScheme, a ≫ U.ι = b) ↔
        IsOpenImmersion (((baseChange b).map f).hom.hom.left)

theorem groupMonomorphismOpenImmersionLocus :
    GroupMonomorphismOpenImmersionLocusStatement.{u} := by
  intro S H N f _ _ _ _
  refine ⟨unitEtaleOpen f, fun T b => ?_⟩
  rw [← range_subset_unitEtaleOpen_iff f b, ← Scheme.Opens.range_ι]
  constructor
  · rintro ⟨a, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨a t, rfl⟩
  · intro h
    exact ⟨IsOpenImmersion.lift _ _ h, IsOpenImmersion.lift_fac _ _ _⟩

end Langlands.GroupScheme
