import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.Unipotent.TorusStableSubgroupConnectedStatement
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedReduction
import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.SplitUnipotentSolvable
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Rational.SemigroupBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.RepresentedAction
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Torus-stable subgroups of connected unipotent groups are connected (Milne 16.25) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusStableUnipotentConnected

/-- The same factorization for morphisms of schemes over a base. -/
theorem exists_overLift_of_range_subset {B : Scheme.{u}} {X Y Z : Over B} [IsReduced X.left]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsClosedImmersion g.left]
    (h : Set.range f.left ⊆ Set.range g.left) : ∃ l : X ⟶ Z, l ≫ g = f := by
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset g.left f.left h
  refine ⟨Over.homMk l (by rw [← Over.w g, ← Category.assoc, hl, Over.w f]), ?_⟩
  apply Over.OverMorphism.ext
  exact hl

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, a morphism from a reduced scheme locally of finite type
factors through a closed immersion as soon as every rational point does. -/
theorem exists_lift_of_points {X Y Z : Over (Spec (CommRingCat.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (g : Z ⟶ Y) [IsClosedImmersion g.left]
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, ∃ z, z ≫ g = x ≫ f) :
    ∃ l : X ⟶ Z, l ≫ g = f := by
  apply exists_overLift_of_range_subset
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed : IsClosed (f.left ⁻¹' Set.range g.left) :=
    g.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have hpts : closedPoints X.left ⊆ f.left ⁻¹' Set.range g.left := by
    intro x hx
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    obtain ⟨z, hz⟩ := h a
    refine ⟨z.left (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg
      (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y =>
        q.left (IsLocalRing.closedPoint k)) hz
    change g.left (z.left (IsLocalRing.closedPoint k)) =
      f.left (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint k)) at he
    exact he.trans (congrArg f.left
      (pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint k)))
  have huniv : f.left ⁻¹' Set.range g.left = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← closure_closedPoints (X := X.left)]
    exact closure_minimal hpts hclosed
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ f.left ⁻¹' Set.range g.left := by
    rw [huniv]
    trivial
  exact hx

omit [IsAlgClosed k] in
/-- The location of a rational point lies in the closure of rational points, so a rational point
of a closed set of rational points factors through the represented closure. -/
theorem exists_point_lift_of_mem_closure {U Z : GroupScheme (Spec (CommRingCat.of k))}
    (ψ : Z ⟶ U) [IsClosedImmersion ψ.hom.hom.left] {Γ : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)}
    (hψ : Set.range ψ.hom.hom.left = closure (rationalPointImage U Γ))
    (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) (hw : w ∈ Γ) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X, z ≫ ψ.hom.hom = w := by
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  apply exists_overLift_of_range_subset
  rintro _ ⟨p, rfl⟩
  have hp : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hp
  rw [hψ]
  exact subset_closure ⟨w, hw, rfl⟩

/-- **Core case.** Over an algebraically closed field, with a split acting torus given as a
commutative group scheme, a stable closed subgroup of a connected unipotent affine group
containing the fixed subgroup is connected. -/
theorem connectedSpace_of_isAlgClosed (U : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom] (hUc : ConnectedSpace U.X.left)
    (hUu : IsUnipotent U) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (c : AutomorphicAction S.toGrp U)
    (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ U) (hh : IsClosedSubgroup h)
    (hstab : c.IsStable (SubgroupFunctor.range h))
    (hfix : c.fixedSubgroup ≤ SubgroupFunctor.range h) : ConnectedSpace H.X.left := by
  classical
  have : JacobsonSpace U.X.left := LocallyOfFiniteType.jacobsonSpace U.X.hom
  have : IsClosedImmersion h.hom.hom.left := hh
  have hSs : Smooth S.toGrp.X.hom := hS.smooth
  -- Step 1: the reduced subgroup `U'` of `U`, the closure of all rational points.
  obtain ⟨U', ζ, hζc, hU's, hζr⟩ := rationalPointClosureSubgroup k U ⊤
  have : IsClosedImmersion ζ.hom.hom.left := hζc
  have : Smooth U'.X.hom := hU's
  have hU'a : IsAffineHom U'.X.hom := by
    rw [← Over.w ζ.hom.hom]
    infer_instance
  have : IsAffineHom U'.X.hom := hU'a
  have : LocallyOfFiniteType U'.X.hom := by
    rw [← Over.w ζ.hom.hom]
    infer_instance
  have hζuniv : Set.range ζ.hom.hom.left = Set.univ := by
    rw [hζr]
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := U.X.left)]
    apply closure_mono
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint U.X.hom x hx) (pointOfClosedPoint_comp U.X.hom x hx),
      trivial, ?_⟩
    exact pointOfClosedPoint_apply U.X.hom x hx (IsLocalRing.closedPoint k)
  have hU'c : ConnectedSpace U'.X.left := by
    let e := ζ.hom.hom.left.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
      (Set.range_eq_univ.mp hζuniv)
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have hU'u : IsUnipotent U' := unipotentClosedSubgroup k U U' ζ hζc hUu
  have hU'sol : RelativeRoot.IsSolvableScheme U' :=
    (perfectFieldUnipotentSplit k U' hU'c hU'u).isSolvableScheme
  have hrepζ : (SubgroupFunctor.range ζ).IsRepresentedBy ζ := ⟨Over.mono_of_mono_left _, rfl⟩
  have : Mono ζ.hom.hom := hrepζ.1
  -- Step 2: `U'` is stable, so the action restricts to it.
  have hstabζ : c.IsStable (SubgroupFunctor.range ζ) := by
    have : Smooth (S.toGrp.X ⊗ U'.X).hom := smooth_tensor _ _ hSs hU's
    have : IsReduced (S.toGrp.X ⊗ U'.X).left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
        (S.toGrp.X ⊗ U'.X).hom
    obtain ⟨L, hL⟩ := exists_overLift_of_range_subset
      (c.act (fst S.toGrp.X U'.X) (snd S.toGrp.X U'.X ≫ ζ.hom.hom)) ζ.hom.hom
      (by rw [hζuniv]; exact Set.subset_univ _)
    rintro T s _ ⟨y, rfl⟩
    change T ⟶ U'.X at y
    refine ⟨lift s y ≫ L, ?_⟩
    change (lift s y ≫ L) ≫ ζ.hom.hom = c.act s (y ≫ ζ.hom.hom)
    rw [Category.assoc, hL, c.naturality, lift_fst, lift_snd_assoc]
  let c' := c.onRepresentedSubgroup ζ hrepζ hstabζ
  have hc' : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.toGrp.X) (x : T ⟶ U'.X),
      c'.act s x ≫ ζ.hom.hom = c.act s (x ≫ ζ.hom.hom) :=
    fun s x => AutomorphicAction.onRepresentedSubgroup_act_comp c ζ hrepζ hstabζ s x
  -- Step 3: the reduced subgroup `H''` of `H`, the closure of the rational points of `H`.
  let Γ := (SubgroupFunctor.range h).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  obtain ⟨H'', ψ, hψc, hH''s, hψr⟩ := rationalPointClosureSubgroup k U Γ
  have : IsClosedImmersion ψ.hom.hom.left := hψc
  have : Smooth H''.X.hom := hH''s
  have : IsReduced H''.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ H''.X.hom
  have : LocallyOfFiniteType H''.X.hom := by
    rw [← Over.w ψ.hom.hom]
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w h.hom.hom]
    infer_instance
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hψh : Set.range ψ.hom.hom.left = Set.range h.hom.hom.left := by
    apply Set.Subset.antisymm
    · rw [hψr]
      apply closure_minimal _ h.hom.hom.left.isClosedEmbedding.isClosed_range
      rintro _ ⟨w, ⟨y, hy⟩, rfl⟩
      change Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X at y
      change y ≫ h.hom.hom = w at hy
      subst hy
      exact ⟨y.left (IsLocalRing.closedPoint k), rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ closure (closedPoints H.X.left) := by
        rw [closure_closedPoints]
        trivial
      have hx' := image_closure_subset_closure_image h.hom.hom.left.continuous ⟨x, hx, rfl⟩
      rw [hψr]
      refine closure_mono ?_ hx'
      rintro _ ⟨x, hx, rfl⟩
      let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
        Over.homMk (pointOfClosedPoint H.X.hom x hx) (pointOfClosedPoint_comp H.X.hom x hx)
      refine ⟨a ≫ h.hom.hom, ⟨a, rfl⟩, ?_⟩
      change h.hom.hom.left (pointOfClosedPoint H.X.hom x hx (IsLocalRing.closedPoint k)) = _
      exact congrArg h.hom.hom.left
        (pointOfClosedPoint_apply H.X.hom x hx (IsLocalRing.closedPoint k))
  obtain ⟨θ, hθ⟩ := exists_overLift_of_range_subset ψ.hom.hom h.hom.hom hψh.subset
  have hθsurj : Function.Surjective θ.left := by
    intro x
    obtain ⟨z, hz⟩ : h.hom.hom.left x ∈ Set.range ψ.hom.hom.left := by
      rw [hψh]
      exact ⟨x, rfl⟩
    refine ⟨z, h.hom.hom.left.isClosedEmbedding.injective ?_⟩
    change (θ ≫ h.hom.hom).left z = h.hom.hom.left x
    rw [hθ]
    exact hz
  obtain ⟨l, hl⟩ := exists_overLift_of_range_subset ψ.hom.hom ζ.hom.hom
    (by rw [hζuniv]; exact Set.subset_univ _)
  have hψζ : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range ζ := by
    rintro T _ ⟨y, rfl⟩
    change T ⟶ H''.X at y
    refine ⟨y ≫ l, ?_⟩
    change (y ≫ l) ≫ ζ.hom.hom = y ≫ ψ.hom.hom
    rw [Category.assoc, hl]
  let j := hrepζ.factorHom ψ hψζ
  have hjζ : j.hom.hom ≫ ζ.hom.hom = ψ.hom.hom := by
    rw [← Grp.comp_hom_hom, hrepζ.factorHom_comp ψ hψζ]
  have hjc : IsClosedSubgroup j := by
    have : IsClosedImmersion (j.hom.hom.left ≫ ζ.hom.hom.left) := by
      rw [← Over.comp_left, hjζ]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left ζ.hom.hom.left
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hF1 : ∀ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X, w ∈ Γ →
      ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H''.X, z ≫ ψ.hom.hom = w :=
    fun w hw => exists_point_lift_of_mem_closure ψ hψr w hw
  -- Step 4: `H''` is stable under the restricted action.
  have hstabj : c'.IsStable (SubgroupFunctor.range j) := by
    have : Smooth (S.toGrp.X ⊗ H''.X).hom := smooth_tensor _ _ hSs hH''s
    have : IsReduced (S.toGrp.X ⊗ H''.X).left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
        (S.toGrp.X ⊗ H''.X).hom
    obtain ⟨L, hL⟩ := exists_lift_of_points
      (c'.act (fst S.toGrp.X H''.X) (snd S.toGrp.X H''.X ≫ j.hom.hom)) j.hom.hom (by
        intro x
        rw [c'.naturality]
        obtain ⟨z, hz⟩ := hF1 (c.act (x ≫ fst _ _) (x ≫ snd _ _ ≫ ψ.hom.hom)) (by
          apply hstab
          refine ⟨(x ≫ snd _ _) ≫ θ, ?_⟩
          change ((x ≫ snd _ _) ≫ θ) ≫ h.hom.hom = _
          simp only [Category.assoc, hθ])
        refine ⟨z, ?_⟩
        apply (cancel_mono ζ.hom.hom).1
        simp only [Category.assoc, hjζ, hc']
        exact hz)
    rintro T s _ ⟨y, rfl⟩
    change T ⟶ H''.X at y
    refine ⟨lift s y ≫ L, ?_⟩
    change (lift s y ≫ L) ≫ j.hom.hom = c'.act s (y ≫ j.hom.hom)
    rw [Category.assoc, hL, c'.naturality, lift_fst, lift_snd_assoc]
  -- Step 5: the fixed subgroup of the restricted action lies in `H''`.
  have hfixj : c'.fixedSubgroup ≤ SubgroupFunctor.range j := by
    obtain ⟨Φ, φ, hφrep, hφc⟩ :=
      fieldFixedSubgroupRepresentability k S.toGrp U' hS.isAffineHom c'
    have : IsClosedImmersion φ.hom.hom.left := hφc
    obtain ⟨I, hI, ⟨f⟩⟩ := id hS
    let : Fintype I := Fintype.ofFinite I
    let e := f ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
    have hΦs : Smooth Φ.X.hom := Diagonalizable.fixedSubgroup_smooth_of_actingIso
      Diagonalizable.FixedSmooth.fixedSubgroupSmooth c' e hU's hU'a φ hφrep hφc
    have : Smooth Φ.X.hom := hΦs
    have : IsReduced Φ.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ Φ.X.hom
    have : LocallyOfFiniteType Φ.X.hom := inferInstance
    rw [← hφrep.2]
    apply SubgroupFunctor.range_le_of_algClosed_points hjc
    rw [hφrep.2]
    intro x hx
    have hx' : c'.IsFixed x := hx
    have hxζ : c.IsFixed (x ≫ ζ.hom.hom) := by
      intro T' b s
      rw [← Category.assoc, ← hc', hx' T' b s]
    obtain ⟨z, hz⟩ := hF1 _ (hfix _ hxζ)
    refine ⟨z, ?_⟩
    apply (cancel_mono ζ.hom.hom).1
    change (z ≫ j.hom.hom) ≫ ζ.hom.hom = x ≫ ζ.hom.hom
    rw [Category.assoc, hjζ, hz]
  -- Step 6: the solvable case (CGP 2.1.12) gives connectedness of `H''`, hence of `H`.
  have hH''c : ConnectedSpace H''.X.left :=
    Torus.solvableFixedContainmentConnected k U' hU's hU'a hU'c hU'sol S hS c'
      (SubgroupFunctor.range j) hstabj hfixj H'' j ⟨Over.mono_of_mono_left _, rfl⟩ hjc hH''s
  exact hθsurj.connectedSpace θ.left.continuous

end TorusStableUnipotentConnected

open TorusStableUnipotentConnected in
/-- The first assertion of Milne 2017, Corollary 16.25, for an arbitrary field and torus:
base change to an algebraic closure of a splitting field of `T` and apply the core case. -/
theorem TorusStableUnipotentConnected.connectedSpace {k : Type u} [Field k]
    (U T : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom] (hUc : ConnectedSpace U.X.left)
    (hUu : IsUnipotent U) (hT : IsTorus T) (a : AutomorphicAction T U)
    (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ U) (hh : IsClosedSubgroup h)
    (hstab : a.IsStable (SubgroupFunctor.range h))
    (hfix : a.fixedSubgroup ≤ SubgroupFunctor.range h) : ConnectedSpace H.X.left := by
  obtain ⟨K, _, _, hK⟩ := hT
  let E := AlgebraicClosure K
  let b : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k E))
  have hTE : IsSplitTorus ((GroupScheme.baseChange b).obj T) :=
    hK.baseChange_fieldTower k K E T
  let S : CommGroupScheme (Spec (CommRingCat.of E)) :=
    { (GroupScheme.baseChange b).obj T with comm := hTE.isCommMonObj }
  let UE := (GroupScheme.baseChange b).obj U
  let HE := (GroupScheme.baseChange b).obj H
  have : LocallyOfFiniteType UE.X.hom := by
    change LocallyOfFiniteType (pullback.snd U.X.hom b)
    infer_instance
  have : IsAffineHom UE.X.hom := by
    change IsAffineHom (pullback.snd U.X.hom b)
    infer_instance
  have : ConnectedSpace U.X.left := hUc
  have hUEc : ConnectedSpace UE.X.left := U.connectedSpace_baseChange_of_connected b
  have hUEu : IsUnipotent UE :=
    unipotentFieldExtensionStatement k E U inferInstance inferInstance hUu
  let cE : AutomorphicAction S.toGrp UE := a.baseChange b
  have hstabE : cE.IsStable (SubgroupFunctor.range ((GroupScheme.baseChange b).map h)) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hstab.baseChange b
  have hfixE : cE.fixedSubgroup ≤ SubgroupFunctor.range ((GroupScheme.baseChange b).map h) := by
    change (a.baseChange b).fixedSubgroup ≤ _
    rw [SubgroupFunctor.range_baseChangeHom, AutomorphicAction.fixedSubgroup_baseChange]
    intro T x hx
    exact hfix _ hx
  have hHEc : ConnectedSpace HE.X.left :=
    connectedSpace_of_isAlgClosed UE hUEc hUEu S hTE cE HE ((GroupScheme.baseChange b).map h)
      (hh.baseChange b) hstabE hfixE
  let : Surjective b := (fieldExtension_fpqc k E).1
  let : ConnectedSpace (pullback H.X.hom b : Scheme.{u}) := hHEc
  exact (inferInstance : Surjective (pullback.fst H.X.hom b)).surj.connectedSpace
    (pullback.fst H.X.hom b).continuous

/-- **Milne 2017, Corollary 16.25.** For a torus acting on a connected unipotent affine group
over a field, every stable closed subgroup containing the fixed subgroup is connected; in
particular every closed subgroup representing the fixed subgroup is connected. -/
theorem torusStableUnipotentSubgroupConnected :
    TorusStableUnipotentSubgroupConnectedStatement.{u} := by
  intro k _ U T _ _ hUc hUu hT a
  refine ⟨fun H h hh hstab hfix =>
    TorusStableUnipotentConnected.connectedSpace U T hUc hUu hT a H h hh hstab hfix, ?_⟩
  intro F j hj hrange
  refine TorusStableUnipotentConnected.connectedSpace U T hUc hUu hT a F j hj ?_ hrange.ge
  rw [hrange]
  intro T' t g hg
  have hg' : a.IsFixed g := hg
  have ht : a.act t g = g := by
    simpa only [Category.id_comp] using hg' T' (𝟙 _) t
  rw [ht]
  exact hg

end Langlands.GroupScheme
