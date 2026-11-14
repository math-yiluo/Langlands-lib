import Langlands.AlgebraicGeometry.FiberwiseFlatness
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.SchemeEtaleLocus
import Langlands.CommutativeAlgebra.EtaleFlatLocalDescentProof
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.RelativeIdentityComponent.OpenGeometry
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Isomorphisms near a fibre for smooth group monomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry

/-- The fibrewise flatness criterion at one specified source point. -/
theorem flat_stalkMap_of_flat_residueFiber
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [LocallyOfFinitePresentation Y.hom] (x : X.left)
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

namespace Langlands.GroupScheme.SmoothMonoLocalIso

/-- The given homomorphism is an isomorphism after restriction to some open
neighbourhood of the specified base point. -/
def IsIsoNear {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K) (s : S) : Prop :=
  ∃ V : S.Opens, s ∈ V ∧ IsIso (((baseChange V.ι).map f).hom.hom.left)

/-- Local finite presentation of a group homomorphism follows from that of its
source over the base and local finite type of its target over the base. -/
theorem locallyOfFinitePresentation_hom
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [LocallyOfFinitePresentation H.X.hom] [LocallyOfFiniteType K.X.hom] :
    LocallyOfFinitePresentation f.hom.hom.left :=
  have : LocallyOfFinitePresentation (f.hom.hom.left ≫ K.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp f.hom.hom.left K.X.hom

/-- The open subset of the base where the homomorphism is etale at the unit
section of the source. -/
def unitEtaleOpen {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [LocallyOfFinitePresentation H.X.hom] [LocallyOfFiniteType K.X.hom] : S.Opens :=
  letI := locallyOfFinitePresentation_hom f
  η[H.X].left ⁻¹ᵁ Langlands.AlgebraicGeometry.schemeEtaleLocus f.hom.hom.left

/-- Flatness of a homomorphism propagates from any flat family whose base map is
surjective, by translating that family through the source group. -/
theorem flat_of_flat_family {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat H.X.hom] {W : Over S} (a : W ⟶ H.X) [Flat W.hom] [Surjective W.hom]
    [Flat (a ≫ f.hom.hom).left] : Flat f.hom.hom.left := by
  let φ := f.hom.hom
  let g' : W ⊗ H.X ⟶ H.X := (fst W H.X ≫ a) * snd W H.X
  let f' : W ⊗ H.X ⟶ K.X ⊗ H.X := (a ≫ φ) ▷ H.X
  let g : K.X ⊗ H.X ⟶ K.X := fst K.X H.X * (snd K.X H.X ≫ φ)
  have hsq : f' ≫ g = g' ≫ φ := by
    simp only [f', g, g', MonObj.comp_mul, MonObj.mul_comp, whiskerRight_fst,
      whiskerRight_snd_assoc, Category.assoc]
  have hsq' : f'.left ≫ g.left = g'.left ≫ φ.left := by
    rw [← Over.comp_left, hsq, Over.comp_left]
  have : Flat g.left := DominantHomFlat.flat_mul_right _
  have : Flat g'.left := DominantHomFlat.flat_mul_left _
  have : Flat f'.left :=
    MorphismProperty.pullbackMap (P := @Flat) inferInstance
      (by change Flat (𝟙 H.X.left); infer_instance) (Over.w (a ≫ φ)).symm (by simp)
  have : Surjective g'.left := DominantHomFlat.surjective_mul_left _
  apply Flat.of_stalkMap
  intro x
  obtain ⟨z, hz⟩ := g'.left.surjective x
  rw [← hz]
  exact DominantHomFlat.flat_stalkMap_of_comm φ.left f'.left g.left g'.left hsq'
    z (Flat.stalkMap _ z)

/-- A flat monomorphism of locally finite presentation onto a smooth group with
geometrically connected fibres is an isomorphism. -/
theorem isIso_of_flat {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]
    [Mono f.hom.hom.left] [Smooth K.X.hom] [GeometricallyConnected K.X.hom] :
    IsIso f.hom.hom.left := by
  have hopen : IsOpenImmersion f.hom.hom.left :=
    IsOpenImmersion.of_flat_of_mono _
  have hfiber (s : S) :
      Surjective (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) := by
    let b := S.fromSpecResidueField s
    let fs := (baseChange b).map f
    have : Flat fs.hom.hom.left :=
      MorphismProperty.of_isPullback (P := @Flat)
        (RelativeIdentityComponent.overPullback_isPullback b f.hom.hom).flip inferInstance
    have : Smooth ((baseChange b).obj K).X.hom :=
      inferInstanceAs (Smooth (pullback.snd K.X.hom b))
    have : ConnectedSpace ((baseChange b).obj K).X.left :=
      inferInstanceAs (ConnectedSpace (K.X.hom.fiber s))
    have : IrreducibleSpace ((baseChange b).obj K).X.left :=
      Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected
        ((baseChange b).obj K).X.hom
    exact DominantHomFlat.surjective_of_flat fs
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
          pullback.fst K.X.hom (S.fromSpecResidueField s) := by
      exact (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst H.X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    exact congrArg (fun z => z x') key
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩

/-- An isomorphic residue fibre puts the corresponding unit in the etale locus. -/
theorem mem_unitEtaleOpen_of_residueFiber
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Smooth H.X.hom] [Smooth K.X.hom] [Mono f.hom.hom.left]
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
    Langlands.AlgebraicGeometry.flat_stalkMap_of_flat_residueFiber φ x (by
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

/-- On the unit-etale open, a smooth group monomorphism with geometrically
connected target fibres is an isomorphism. -/
theorem isIso_unitEtaleOpen
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Smooth H.X.hom] [Smooth K.X.hom] [Mono f.hom.hom.left]
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
  have : Smooth KV.X.hom := inferInstanceAs (Smooth (pullback.snd K.X.hom V.ι))
  have : GeometricallyConnected KV.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd K.X.hom V.ι))
  have : Mono fV.hom.hom.left :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms Scheme)
      (RelativeIdentityComponent.overPullback_isPullback V.ι φ).flip inferInstance
  have : LocallyOfFinitePresentation fV.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (RelativeIdentityComponent.overPullback_isPullback V.ι φ).flip inferInstance
  exact isIso_of_flat fV

/-- An isomorphism on one residue fibre spreads to an open neighbourhood for
a monomorphism between smooth groups with geometrically connected target
fibres. No quasi-compactness or affine hypothesis is required. -/
theorem isIsoNear_of_residueFiber
    {S : Scheme.{u}} {H K : GroupScheme S} (f : H ⟶ K)
    [Smooth H.X.hom] [Smooth K.X.hom] [Mono f.hom.hom.left]
    [GeometricallyConnected K.X.hom] (s : S)
    (hs : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left)) :
    IsIsoNear f s :=
  ⟨unitEtaleOpen f, mem_unitEtaleOpen_of_residueFiber f s hs, isIso_unitEtaleOpen f⟩

end Langlands.GroupScheme.SmoothMonoLocalIso
