import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.RealApproximationOpen
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Real approximation on the identity component of a unirational group -/

noncomputable section

open CategoryTheory Topology
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A smooth morphism of affine rational schemes is open on real points. -/
theorem isOpenMap_affineSmoothRealPointMap
    {X Y : Over (Spec (CommRingCat.of ℚ))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left] :
    IsOpenMap (X := RingPoint ℚ X ℝ) (Y := RingPoint ℚ Y ℝ) (fun p => p ≫ f) := by
  let fR := (Over.pullback (Spec.algebraMap ℚ ℝ)).map f
  let : IsAffine ((Over.pullback (Spec.algebraMap ℚ ℝ)).obj X).left :=
    ringBaseChange_isAffine ℚ ℝ X
  let : IsAffine ((Over.pullback (Spec.algebraMap ℚ ℝ)).obj Y).left :=
    ringBaseChange_isAffine ℚ ℝ Y
  let : Smooth fR.left := MorphismProperty.of_isPullback (P := @Smooth)
    (Langlands.GroupScheme.RelativeIdentityComponent.overPullback_isPullback
      (Spec.algebraMap ℚ ℝ) f).flip inferInstance
  let eX := (ringPointBaseChangeEquiv ℚ ℝ ℝ X).toHomeomorphOfIsInducing
    (isHomeomorph_ringPointBaseChangeEquiv ℚ ℝ ℝ X).isInducing
  let eY := (ringPointBaseChangeEquiv ℚ ℝ ℝ Y).toHomeomorphOfIsInducing
    (isHomeomorph_ringPointBaseChangeEquiv ℚ ℝ ℝ Y).isInducing
  let F : RingPoint ℝ (ringBaseChange ℚ ℝ X) ℝ → RingPoint ℝ (ringBaseChange ℚ ℝ Y) ℝ :=
    fun p => p ≫ fR
  have hF : IsOpenMap F := isOpenMap_affineSmoothPointMap ℝ fR
  have h : (fun p : RingPoint ℚ X ℝ => (p ≫ f : RingPoint ℚ Y ℝ)) = eY.symm ∘ F ∘ eX := by
    funext p
    apply (ringPointBaseChangeEquiv ℚ ℝ ℝ Y).injective
    change ringPointBaseChangeEquiv ℚ ℝ ℝ Y (p ≫ f) =
      ringPointBaseChangeEquiv ℚ ℝ ℝ Y ((ringPointBaseChangeEquiv ℚ ℝ ℝ Y).symm (F (eX p)))
    rw [Equiv.apply_symm_apply]
    exact ringPointBaseChangeEquiv_natural ℚ ℝ ℝ f p
  rw [h]
  exact eY.symm.isOpenMap.comp (hF.comp eX.isOpenMap)

set_option backward.isDefEq.respectTransparency false in
private theorem genericPoint_mem_smoothLocus_rat
    {X Y : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left] (hf : DenseRange f.left) :
    genericPoint X.left ∈ f.left.smoothLocus := by
  let x := genericPoint X.left
  let y := f.left x
  have hy : y = genericPoint Y.left := by
    have h := (genericPoint_spec X.left).image f.left.continuous
    have hd : Dense (Set.range (fun z : X.left => f.left z)) := hf
    rw [Set.image_univ, hd.closure_eq] at h
    exact h.eq (genericPoint_spec Y.left)
  let Yy := Y.left.presheaf.stalk y
  let Xx := X.left.functionField
  have hYfield : IsField (Y.left.presheaf.stalk y) := by
    rw [hy]
    exact Field.toIsField Y.left.functionField
  let : Field Yy := hYfield.toField
  let : Field Xx := inferInstanceAs (Field X.left.functionField)
  let a : ℚ →+* Yy := ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ Y.hom.appTop ≫
    Y.left.presheaf.germ ⊤ y (by trivial)).hom
  let : CharZero Yy := charZero_of_injective_ringHom a.injective
  have := LocallyOfFiniteType.stalkMap f.left x
  rw [Scheme.Hom.mem_smoothLocus]
  change (f.left.stalkMap x).hom.FormallySmooth
  algebraize [(f.left.stalkMap x).hom]
  exact Algebra.FormallySmooth.of_perfectField

set_option backward.isDefEq.respectTransparency false in
/-- The rational-point closure of an integral unirational affine rational scheme
contains a nonempty open set of real points. -/
theorem IsUnirational.exists_realOpen_subset_closure
    {X : Over (Spec (CommRingCat.of ℚ))} [IsAffine X.left] [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (hX : IsUnirational ℚ X) :
    ∃ W : Set (RingPoint ℚ X ℝ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ closure (Set.range fun p : RingPoint ℚ X ℚ => p.changeRing (Algebra.ofId ℚ ℝ)) := by
  obtain ⟨I, hI, U, hU, f, hf⟩ := hX
  let := hI
  let A : Over (Spec (CommRingCat.of ℚ)) :=
    Over.mk (𝔸(I; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))
  let P := openOver ℚ A U
  let : Nonempty U := hU.to_subtype
  let : IsIntegral P.left := inferInstanceAs (IsIntegral U)
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : LocallyOfFiniteType P.hom := inferInstanceAs (LocallyOfFiniteType
    (U.ι ≫ (𝔸(I; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))))
  let : LocallyOfFiniteType (f.left ≫ X.hom) := by
    rw [Over.w f]
    exact inferInstanceAs (LocallyOfFiniteType P.hom)
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  have hη := genericPoint_mem_smoothLocus_rat (X := P) f hf
  obtain ⟨V, hV, hηV, hVs⟩ := exists_isAffineOpen_mem_and_subset hη
  let : IsAffine V := hV
  let : Nonempty V := ⟨⟨genericPoint P.left, hηV⟩⟩
  let Q := openOver ℚ P V
  let : Nonempty Q.left := inferInstanceAs (Nonempty V)
  let g : Q ⟶ X := openOverι ℚ P V ≫ f
  let : Smooth g.left := by
    change Smooth (V.ι ≫ f.left)
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_unique (fun z _ => hVs z.property)
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of ℚ))))
  let j : Q ⟶ A := openOverι ℚ P V ≫ openOverι ℚ A U
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι))
  have hQ : HasRealApproximation Q := (hasRealApproximation_affineSpace I).of_isOpenImmersion j
  have hd : HasDenseRationalPoints ℚ Q := hasDenseRationalPoints_open P V
    (hasDenseRationalPoints_open A U (hasDenseRationalPoints_affineSpace ℚ I))
  obtain ⟨q₀, _⟩ := Set.nonempty_iUnion.mp hd.nonempty
  let q := rationalPointEquiv ℚ Q q₀
  let F : RingPoint ℚ Q ℝ → RingPoint ℚ X ℝ := fun p => p ≫ g
  refine ⟨Set.range F, (isOpenMap_affineSmoothRealPointMap g).isOpen_range,
    ⟨_, q.changeRing (Algebra.ofId ℚ ℝ), rfl⟩, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hc : Continuous F := continuous_affineSchemePointMap ℚ ℝ g
  have he : F '' Set.range (fun r : RingPoint ℚ Q ℚ => r.changeRing (Algebra.ofId ℚ ℝ)) ⊆
      Set.range (fun r : RingPoint ℚ X ℚ => r.changeRing (Algebra.ofId ℚ ℝ)) := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r ≫ g, (Category.assoc _ _ _).symm⟩
  exact closure_mono he (image_closure_subset_closure_image hc ⟨p, hQ p, rfl⟩)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Rational points of a smooth connected unirational affine rational group
approximate every point of its real identity component. -/
def UnirationalRealApproximationIdentityComponentStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left]
    [Smooth G.X.hom] [ConnectedSpace G.X.left], IsUnirational ℚ G.X →
    letI : Group (RingPoint ℚ G.X ℝ) := inferInstanceAs (Group (ringTest ℚ ℝ ⟶ G.X))
    connectedComponent (1 : RingPoint ℚ G.X ℝ) ⊆
      closure (Set.range fun p : RingPoint ℚ G.X ℚ => p.changeRing (Algebra.ofId ℚ ℝ))

theorem unirationalRealApproximationIdentityComponent :
    UnirationalRealApproximationIdentityComponentStatement := by
  intro G _ _ _ hG
  let : Group (RingPoint ℚ G.X ℝ) := inferInstanceAs (Group (ringTest ℚ ℝ ⟶ G.X))
  let : Group (RingPoint ℚ G.X ℚ) := inferInstanceAs (Group (ringTest ℚ ℚ ⟶ G.X))
  let : IsTopologicalGroup (RingPoint ℚ G.X ℝ) := affineGroupTopological_proof ℚ ℝ G
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth ℚ G.X.hom
  let c : RingPoint ℚ G.X ℚ →* RingPoint ℚ G.X ℝ :=
    { toFun := fun p => p.changeRing (Algebra.ofId ℚ ℝ)
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  let H := c.range.topologicalClosure
  have hH : (H : Set (RingPoint ℚ G.X ℝ)) =
      closure (Set.range fun p : RingPoint ℚ G.X ℚ => p.changeRing (Algebra.ofId ℚ ℝ)) :=
    Subgroup.topologicalClosure_coe
  obtain ⟨W, hW, ⟨x, hx⟩, hWH⟩ := hG.exists_realOpen_subset_closure
  have hOpen : IsOpen (H : Set (RingPoint ℚ G.X ℝ)) := by
    apply H.isOpen_of_mem_nhds (g := x)
    rw [hH]
    exact Filter.mem_of_superset (hW.mem_nhds hx) hWH
  change connectedComponent (1 : RingPoint ℚ G.X ℝ) ⊆ _
  rw [← hH]
  have hClopen : IsClopen (H : Set (RingPoint ℚ G.X ℝ)) :=
    ⟨c.range.isClosed_topologicalClosure, hOpen⟩
  exact hClopen.connectedComponent_subset H.one_mem

end Langlands.GroupScheme
