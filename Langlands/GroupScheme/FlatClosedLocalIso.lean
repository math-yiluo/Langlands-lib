import Langlands.GroupScheme.SmoothMonoLocalIso
import Mathlib.Topology.Connected.Clopen

/-! # Isomorphisms near a fibre for flat closed group inclusions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- The fibrewise flatness criterion at one specified source point. -/
theorem flat_stalkMap_of_flat_residueFiber_of_lft_target
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [LocallyOfFiniteType Y.hom] (x : X.left)
    (hf : Flat ((Over.pullback (S.fromSpecResidueField (Y.hom (f.left x)))).map f).left) :
    (f.left.stalkMap x).hom.Flat := by
  let R : Type u := S.presheaf.stalk (Y.hom (f.left x))
  let A : Type u := Y.left.presheaf.stalk (f.left x)
  let B : Type u := X.left.presheaf.stalk x
  let g : R →+* A := (Y.hom.stalkMap (f.left x)).hom
  let h : A →+* B := (f.left.stalkMap x).hom
  let : Algebra R A := g.toAlgebra
  let : Algebra A B := h.toAlgebra
  let : Algebra R B := (h.comp g).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Flat (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have hcomp : ((f.left ≫ Y.hom).stalkMap x).hom = h.comp g := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hEB : Langlands.Algebra.EssFinitePresentation R B := by
    have hp := stalkEssFinitePresentation X.left S (f.left ≫ Y.hom) x inferInstance
    change @Langlands.Algebra.EssFinitePresentation R B _ _
      ((f.left ≫ Y.hom).stalkMap x).hom.toAlgebra at hp
    rw [hcomp] at hp
    exact hp
  have hRA : _root_.Algebra.EssFiniteType R A :=
    LocallyOfFiniteType.stalkMap Y.hom (f.left x)
  have hRB : Module.Flat R B := by
    have hp := Flat.stalkMap (f.left ≫ Y.hom) x
    rw [hcomp] at hp
    exact hp
  have hF := fiberStalkFlatness S X Y f x hf
  have : IsLocalHom (algebraMap R A) :=
    inferInstanceAs <| IsLocalHom (Y.hom.stalkMap (f.left x)).hom
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs <| IsLocalHom (f.left.stalkMap x).hom
  exact (Langlands.Algebra.localFiberwiseFlatness.{u, u, u, u}
    R A B B hEB hRA inferInstance inferInstance hF hRB).2.2

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.FlatClosedLocalIso

open SmoothMonoLocalIso

/-- A flat closed group monomorphism of local finite presentation into a
group with geometrically connected fibres is an isomorphism. -/
theorem isIso_of_flat_of_closed {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]
    [IsClosedImmersion f.hom.hom.left] [GeometricallyConnected K.X.hom] :
    IsIso f.hom.hom.left := by
  have : IsOpenImmersion f.hom.hom.left := IsOpenImmersion.of_flat_of_mono _
  have hfiber (s : S) :
      Surjective (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) := by
    let b := S.fromSpecResidueField s
    let fs := (baseChange b).map f
    let : IsOpenImmersion fs.hom.hom.left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (RelativeIdentityComponent.overPullback_isPullback b f.hom.hom).flip inferInstance
    let : IsClosedImmersion fs.hom.hom.left := IsClosedSubgroup.baseChange b
        (show IsClosedSubgroup f from ‹IsClosedImmersion f.hom.hom.left›)
    let : ConnectedSpace ((baseChange b).obj K).X.left :=
      inferInstanceAs (ConnectedSpace (K.X.hom.fiber s))
    let : Nonempty ((baseChange b).obj H).X.left :=
      ⟨η[((baseChange b).obj H).X].left (IsLocalRing.closedPoint (S.residueField s))⟩
    have hcl : IsClopen (Set.range fs.hom.hom.left) :=
      ⟨fs.hom.hom.left.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range _⟩
    exact ⟨Set.range_eq_univ.mp (hcl.eq_univ (Set.range_nonempty _))⟩
  have hsurj : Surjective f.hom.hom.left := by
    refine ⟨fun y => ?_⟩
    let s : S := K.X.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := K.X.hom) (g := S.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (S.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    have := hfiber s
    obtain ⟨x', hx'⟩ :=
      (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left).surjective y'
    have key : pullback.fst H.X.hom (S.fromSpecResidueField s) ≫ f.hom.hom.left =
        (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) ≫
          pullback.fst K.X.hom (S.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst H.X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    exact congrArg (fun z => z x') key
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩

/-- An isomorphic residue fibre puts the source unit in the etale locus
for a flat finitely presented source and a locally finite-type target. -/
theorem mem_unitEtaleOpen_of_residueFiber_of_closed
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [LocallyOfFiniteType K.X.hom] [IsClosedImmersion f.hom.hom.left]
    (s : S)
    (hs : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left)) :
    s ∈ unitEtaleOpen f := by
  let φ := f.hom.hom
  have : LocallyOfFinitePresentation φ.left := locallyOfFinitePresentation_hom f
  let x : H.X.left := η[H.X].left s
  have hx : K.X.hom (φ.left x) = s := by
    rw [← Scheme.Hom.comp_apply, Over.w φ]
    change H.X.hom (η[H.X].left s) = s
    rw [← Scheme.Hom.comp_apply, Over.w η[H.X]]
    rfl
  have hflat : (φ.left.stalkMap x).hom.Flat :=
    Langlands.AlgebraicGeometry.flat_stalkMap_of_flat_residueFiber_of_lft_target φ x (by
      rw [hx]
      let := hs
      exact inferInstanceAs
        (Flat (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left)))
  have het : (φ.left.stalkMap x).hom.FormallyEtale := by
    let := (φ.left.stalkMap x).hom.toAlgebra
    have : IsLocalHom (algebraMap (K.X.left.presheaf.stalk (φ.left x))
        (H.X.left.presheaf.stalk x)) := φ.left.toLRSHom.prop x
    have : Module.Flat (K.X.left.presheaf.stalk (φ.left x))
        (H.X.left.presheaf.stalk x) := hflat
    have : Algebra.FormallyUnramified (K.X.left.presheaf.stalk (φ.left x))
        (H.X.left.presheaf.stalk x) := FormallyUnramified.stalkMap φ.left x
    exact Langlands.CommutativeAlgebra.formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation
      (K.X.left.presheaf.stalk (φ.left x)) (H.X.left.presheaf.stalk x)
      (Langlands.AlgebraicGeometry.stalkEssFinitePresentation
        H.X.left K.X.left φ.left x inferInstance)
  exact het

/-- On the unit-etale open, a closed group inclusion with flat finitely
presented source and geometrically connected target fibres is an isomorphism. -/
theorem isIso_unitEtaleOpen_of_closed
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [LocallyOfFiniteType K.X.hom] [IsClosedImmersion f.hom.hom.left]
    [GeometricallyConnected K.X.hom] :
    IsIso (((baseChange (unitEtaleOpen f).ι).map f).hom.hom.left) := by
  let φ := f.hom.hom
  have : LocallyOfFinitePresentation φ.left := locallyOfFinitePresentation_hom f
  let U := Langlands.AlgebraicGeometry.schemeEtaleLocus φ.left
  let V := unitEtaleOpen f
  let W : Over S := Over.mk (U.ι ≫ H.X.hom)
  let a : W ⟶ H.X := Over.homMk U.ι rfl
  have : Flat W.hom := by
    change Flat (U.ι ≫ H.X.hom)
    infer_instance
  have : Etale (a ≫ φ).left :=
    Langlands.AlgebraicGeometry.etale_schemeEtaleLocus φ.left
  let HV := (baseChange V.ι).obj H
  let KV := (baseChange V.ι).obj K
  let fV : HV ⟶ KV := (baseChange V.ι).map f
  let WV := (Over.pullback V.ι).obj W
  let aV : WV ⟶ HV.X := (Over.pullback V.ι).map a
  have : Flat HV.X.hom := inferInstanceAs (Flat (pullback.snd H.X.hom V.ι))
  have : Flat WV.hom := inferInstanceAs (Flat (pullback.snd W.hom V.ι))
  have : Surjective WV.hom := by
    refine ⟨fun v => ?_⟩
    let u : U := ⟨η[H.X].left v.val, v.property⟩
    have hu : W.hom u = V.ι v := by
      change H.X.hom (η[H.X].left v.val) = v.val
      rw [← Scheme.Hom.comp_apply, Over.w η[H.X]]
      rfl
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := W.hom) (g := V.ι) u v hu
    exact ⟨z, hz⟩
  have : Flat (aV ≫ fV.hom.hom).left := by
    change Flat
      (((Over.pullback V.ι).map a) ≫ ((Over.pullback V.ι).map φ)).left
    rw [← Functor.map_comp]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (RelativeIdentityComponent.overPullback_isPullback V.ι (a ≫ φ)).flip inferInstance
  have : Flat fV.hom.hom.left := flat_of_flat_family fV aV
  have : GeometricallyConnected KV.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd K.X.hom V.ι))
  have : Mono fV.hom.hom.left :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms Scheme)
      (RelativeIdentityComponent.overPullback_isPullback V.ι φ).flip inferInstance
  have : LocallyOfFinitePresentation fV.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (RelativeIdentityComponent.overPullback_isPullback V.ι φ).flip inferInstance
  have : IsClosedImmersion fV.hom.hom.left :=
    IsClosedSubgroup.baseChange V.ι
      (show IsClosedSubgroup f from ‹IsClosedImmersion f.hom.hom.left›)
  exact isIso_of_flat_of_closed fV

/-- An isomorphism on one residue fibre of a closed group inclusion spreads
to an open neighbourhood. The source is flat and locally finitely presented;
the target is locally of finite type with geometrically connected fibres.
No smoothness or affine hypothesis is needed. -/
theorem isIsoNear_of_residueFiber
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [LocallyOfFiniteType K.X.hom] [IsClosedImmersion f.hom.hom.left]
    [GeometricallyConnected K.X.hom] (s : S)
    (hs : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left)) :
    SmoothMonoLocalIso.IsIsoNear f s :=
  ⟨unitEtaleOpen f, mem_unitEtaleOpen_of_residueFiber_of_closed f s hs,
    isIso_unitEtaleOpen_of_closed f⟩

end Langlands.GroupScheme.FlatClosedLocalIso
