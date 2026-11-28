import Langlands.AlgebraicGeometry.PointTopology.NormedOpenZariskiDensity
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.UnirationalBaseChange
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Torus.TorusUnirationalityProof
import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-! # Simultaneous approximation at the complex places of a number field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Topology TopologicalSpace
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false

variable (L : Type u) [Field L] [NumberField L]

abbrev ComplexPlace := {v : InfinitePlace L // v.IsComplex}

private abbrev affineSpace (I : Type u) :=
  Over.mk (𝔸(I; Spec (CommRingCat.of L)) ↘ Spec (CommRingCat.of L))

private local instance affineSpace_isAffine (I : Type u) : IsAffine (affineSpace L I).left :=
  inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of L))))

private theorem exists_affinePoint_in_complexOpens (I : Type u)
    (V : ∀ v : ComplexPlace L, Set (RingPoint L (affineSpace L I) v.1.Completion))
    (hV : ∀ v, IsOpen (V v)) (hVne : ∀ v, (V v).Nonempty) :
    ∃ p : RingPoint L (affineSpace L I) L,
      ∀ v, p.changeRing (Algebra.ofId L v.1.Completion) ∈ V v := by
  classical
  let A := MvPolynomial I L
  let i : ringTest L A ≅ affineSpace L I := Over.isoMk
    (AffineSpace.SpecIso I (CommRingCat.of L)).symm (AffineSpace.SpecIso_inv_over _)
  let e (v : ComplexPlace L) : RingPoint L (affineSpace L I) v.1.Completion ≃ₜ
      (I → v.1.Completion) :=
    (affineSchemePointIsoHomeomorph L v.1.Completion i.symm).trans
      ((spectrumAlgebraPointHomeomorph L v.1.Completion A).trans
        (AlgPoint.polynomialPointHomeomorph (R := L) (S := v.1.Completion) I))
  have hd : DenseRange (fun a : L => fun v : ComplexPlace L => algebraMap L v.1.Completion a) := by
    let r : InfiniteAdeleRing L → (∀ v : ComplexPlace L, v.1.Completion) := fun a v => a v.1
    have hr : Function.Surjective r := by
      intro a
      refine ⟨fun v => if h : v.IsComplex then a ⟨v, h⟩ else 0, ?_⟩
      funext v
      exact dite_eq_left v.2
    exact hr.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap L)
      (continuous_pi fun v => continuous_apply v.1)
  let tr (p : I → ∀ v : ComplexPlace L, v.1.Completion) (v : ComplexPlace L) (a : I) := p a v
  have htr : Function.Surjective tr := fun p => ⟨fun a v => p v a, rfl⟩
  have htrc : Continuous tr := continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)
  have happ := htr.denseRange.comp (DenseRange.piMap fun _ : I => hd) htrc
  obtain ⟨a, ha⟩ := happ.exists_mem_open
    (isOpen_set_pi Set.finite_univ fun v _ => (e v).isOpenMap _ (hV v))
    (Set.univ_pi_nonempty_iff.mpr fun v => (hVne v).image (e v))
  let p : RingPoint L (ringTest L A) L := ringTestMap L (MvPolynomial.aeval a)
  let p₀ : RingPoint L (affineSpace L I) L := p ≫ i.hom
  refine ⟨p₀, fun v => ?_⟩
  have hcoeff : e v (p₀.changeRing (Algebra.ofId L v.1.Completion)) = fun j => algebraMap L v.1.Completion (a j) := by
    funext j
    have hq : ((p₀.changeRing (Algebra.ofId L v.1.Completion)) ≫ i.inv :
        RingPoint L (ringTest L A) v.1.Completion) =
        ringTestMap L ((Algebra.ofId L v.1.Completion).comp (MvPolynomial.aeval a)) := by
      change (ringTestMap L (Algebra.ofId L v.1.Completion) ≫ (p ≫ i.hom)) ≫ i.inv = _
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact (ringTestMap_comp L (MvPolynomial.aeval a) (Algebra.ofId L v.1.Completion)).symm
    change spectrumAlgebraPointHomeomorph L v.1.Completion A
      (affineSchemePointIsoHomeomorph L v.1.Completion i.symm _) (MvPolynomial.X j) = _
    rw [affineSchemePointIsoHomeomorph_apply]
    change spectrumAlgebraPointHomeomorph L v.1.Completion A
      (p₀.changeRing (Algebra.ofId L v.1.Completion) ≫ i.inv) (MvPolynomial.X j) = _
    erw [hq, spectrumAlgebraPointHomeomorph_apply]
    change (Spec.preimage (Spec.map (CommRingCat.ofHom
      ((Algebra.ofId L v.1.Completion).comp (MvPolynomial.aeval a)).toRingHom))).hom
        (MvPolynomial.X j) = _
    rw [Spec.preimage_map]
    exact congrArg (algebraMap L v.1.Completion) (MvPolynomial.aeval_X a j)
  obtain ⟨q, hq, heq⟩ := ha v (Set.mem_univ v)
  exact ((e v).injective (hcoeff.trans heq.symm)).symm ▸ hq

private theorem exists_local_parameter
    {k K : Type u} [Field k] [NontriviallyNormedField K] [IsAlgClosed K] [Algebra k K]
    {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (f : X ⟶ G.X) (hf : DenseRange f.left)
    (hG : IsUnirational k G.X) (V : Set (RingPoint k G.X K))
    (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ p : RingPoint k X K, (p ≫ f : RingPoint k G.X K) ∈ V := by
  let b := Spec.algebraMap k K
  let X' := ringBaseChange k K X
  let G' := (GroupScheme.baseChange b).obj G
  let f' : X' ⟶ G'.X := (Over.pullback b).map f
  let : IsAffine X'.left := ringBaseChange_isAffine k K X
  let : IsAffine G'.X.left := ringBaseChange_isAffine k K G.X
  have hd : DenseRange f'.left := denseRange_of_isPullback_of_isOpenMap
    (RelativeIdentityComponent.overPullback_isPullback b f).flip hf
    (pullback.fst G.X.hom b).isOpenMap
  have : LocallyOfFiniteType X'.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X.hom b))
  have : LocallyOfFiniteType G'.X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : LocallyOfFiniteType (f'.left ≫ G'.X.hom) := (Over.w f').symm ▸ inferInstance
  have : LocallyOfFiniteType f'.left := locallyOfFiniteType_of_comp f'.left G'.X.hom
  have : LocallyOfFinitePresentation f'.left :=
    Langlands.AlgebraicGeometry.TangentSmoothness.locallyOfFinitePresentation_of_comp_eq
      f'.left (Over.w f')
  let : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  let : IsNoetherian X'.left := AlgebraicGeometry.IsNoetherian.mk
  let : IsLocallyNoetherian G'.X.left := LocallyOfFiniteType.isLocallyNoetherian G'.X.hom
  let : IsNoetherian G'.X.left := AlgebraicGeometry.IsNoetherian.mk
  have hcr : IsConstructible (Set.range f'.left) := by
    rw [← Set.image_univ]
    exact f'.left.isConstructible_image ((NoetherianSpace.isCompact _).isConstructible isOpen_univ)
  have : Nonempty G'.X.left := ⟨(1 : rationalPoints G').left (IsLocalRing.closedPoint K)⟩
  obtain ⟨U, hU, hUne, hUr⟩ := ClosedOrbit.exists_isOpen_subset_of_dense hcr hd
  let e := ringPointBaseChangeEquiv k K K G.X
  have he := isHomeomorph_ringPointBaseChangeEquiv k K K G.X
  have d := dense_underlyingNormedPoint_of_unirational G' (hG.baseChange (K := K))
    (e '' V) (he.isOpenMap V hV) (hVne.image e)
  obtain ⟨_, hx, p, hp, rfl⟩ := d.inter_open_nonempty U hU hUne
  obtain ⟨q, hq⟩ := exists_rationalPoint_lift_of_mem_range f'.left p.left (hUr hx)
  let q' : RingPoint K X' K := Over.homMk q (by
    rw [← Over.w f', ← Category.assoc, hq]
    exact Over.w p)
  let r := (ringPointBaseChangeEquiv k K K X).symm q'
  refine ⟨r, ?_⟩
  have hr : e (r ≫ f) = p := by
    change ringPointBaseChangeEquiv k K K G.X (r ≫ f) = p
    rw [ringPointBaseChangeEquiv_natural]
    change ringPointBaseChangeEquiv k K K X ((ringPointBaseChangeEquiv k K K X).symm q') ≫ f' = p
    rw [Equiv.apply_symm_apply]
    exact Over.OverMorphism.ext hq
  obtain ⟨s, hs, heq⟩ := hp
  exact (e.injective (hr.trans heq.symm)).symm ▸ hs

/-- Rational points of a connected reductive group approximate a prescribed
family at all complex places of the ground number field. -/
theorem exists_approximate_complexPoints
    (G : GroupScheme (Spec (CommRingCat.of L))) [IsAffine G.X.left]
    (hG : IsConnectedReductive G)
    (V : ∀ v : ComplexPlace L, Set (RingPoint L G.X v.1.Completion))
    (hV : ∀ v, IsOpen (V v)) (hVne : ∀ v, (V v).Nonempty) :
    ∃ p : RingPoint L G.X L, ∀ v, p.changeRing (Algebra.ofId L v.1.Completion) ∈ V v := by
  classical
  let : Smooth G.X.hom := hG.smooth
  by_cases hplaces : Nonempty (ComplexPlace L)
  swap
  · exact ⟨(1 : ringTest L L ⟶ G.X), fun v => (hplaces ⟨v⟩).elim⟩
  let v₀ := Classical.choice hplaces
  have huni := ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality G hG
  obtain ⟨I, hI, U, ⟨x, hx⟩, f, hf⟩ := huni
  let := hI
  let A := affineSpace L I
  let P := openOver L A U
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : IrreducibleSpace P.left := inferInstanceAs (IrreducibleSpace U)
  obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := P.left) (x := (⟨x, hx⟩ : U)) (U := ⊤) (by trivial)
  let : IsAffine W := hW
  let : Nonempty W := ⟨⟨⟨x, hx⟩, hxW⟩⟩
  let Q := openOver L P W
  let j : Q ⟶ A := openOverι L P W ≫ openOverι L A U
  let g : Q ⟶ G.X := openOverι L P W ≫ f
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (W.ι ≫ U.ι))
  let : LocallyOfFiniteType Q.hom := by
    have : LocallyOfFiniteType A.hom := inferInstanceAs
      (LocallyOfFiniteType (𝔸(I; Spec (CommRingCat.of L)) ↘ Spec (CommRingCat.of L)))
    rw [← Over.w j]
    infer_instance
  have hg : DenseRange g.left := hf.comp W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
    f.left.continuous
  let C (v : ComplexPlace L) := v.1.Completion
  let (v : ComplexPlace L) : NontriviallyNormedField (C v) :=
    infiniteCompletionNontriviallyNormedField v.1
  let (v : ComplexPlace L) : IsAlgClosed (C v) := Langlands.Analytic.isAlgClosed_of_ringEquiv _
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.2).symm
  let F (v : ComplexPlace L) (p : RingPoint L Q (C v)) : RingPoint L A (C v) := p ≫ j
  let V' (v : ComplexPlace L) := {p : RingPoint L Q (C v) | (p ≫ g : RingPoint L G.X (C v)) ∈ V v}
  have hVo (v : ComplexPlace L) : IsOpen (V' v) :=
    (hV v).preimage (continuous_affineSchemePointMap L (C v) g)
  have hVn (v : ComplexPlace L) : (V' v).Nonempty :=
    exists_local_parameter g hg ⟨I, hI, U, ⟨x, hx⟩, f, hf⟩ (V v) (hV v) (hVne v)
  have hF (v : ComplexPlace L) : IsOpenMap (F v) := by
    have h := isOpenEmbedding_schemePointMap L (C v) j
    change @IsOpenEmbedding _ _ (schemePointTopology L Q (C v))
      (schemePointTopology L A (C v)) (F v) at h
    rw [schemePointTopology_eq_affine L Q (C v), schemePointTopology_eq_affine L A (C v)] at h
    exact h.isOpenMap
  obtain ⟨p, hp⟩ := exists_affinePoint_in_complexOpens L I (fun v => F v '' V' v)
    (fun v => hF v _ (hVo v)) (fun v => (hVn v).image (F v))
  obtain ⟨q₀, -, hq₀⟩ := hp v₀
  have hrange : Set.range p.left ⊆ Set.range j.left := by
    rintro _ ⟨a, rfl⟩
    have ha : (ringTestMap L (Algebra.ofId L (C v₀))).left (IsLocalRing.closedPoint (C v₀)) = a :=
      @Subsingleton.elim (PrimeSpectrum L) inferInstance _ _
    have hleft := congrArg (fun r : RingPoint L A (C v₀) => r.left) hq₀
    have hx := congrArg (fun r : Spec (CommRingCat.of (C v₀)) ⟶ A.left =>
      r (IsLocalRing.closedPoint (C v₀))) hleft
    change j.left (q₀.left _) =
      p.left ((ringTestMap L (Algebra.ofId L (C v₀))).left _) at hx
    rw [ha] at hx
    exact ⟨_, hx⟩
  let r : RingPoint L Q L := Over.homMk (IsOpenImmersion.lift j.left p.left hrange) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w p)
  have hr : r ≫ j = p := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨r ≫ g, fun v => ?_⟩
  obtain ⟨q, hq, heq⟩ := hp v
  have hq' : q = r.changeRing (Algebra.ofId L (C v)) := by
    have : Mono j := Over.mono_of_mono_left _
    apply (cancel_mono j).mp
    change F v q = (ringTestMap L (Algebra.ofId L (C v)) ≫ r) ≫ j
    rw [heq, Category.assoc, hr]
    rfl
  change (q ≫ g : RingPoint L G.X (C v)) ∈ V v at hq
  rw [hq', RingPoint.changeRing, Category.assoc] at hq
  exact hq

end Langlands.GroupScheme.QuadraticToralReduction
