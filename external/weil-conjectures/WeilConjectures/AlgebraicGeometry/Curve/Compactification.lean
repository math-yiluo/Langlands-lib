/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Curve.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Smooth proper completion of a smooth curve over a finite field

A smooth geometrically connected curve `U₀` over a finite field `K = 𝔽_q` embeds as a dense
open subscheme of a curve `C₀` which is *proper* over `K` and still smooth and geometrically
connected, the boundary `C₀ \ U₀` being a finite set of closed points.

Separatedness of `U₀` over `K` is part of `AlgebraicGeometry.IsCurve` and is necessary: a
compactification of `p` forces `p` to be separated
(`AlgebraicGeometry.Compactification.isSeparated`), so the affine line with doubled origin has
none.

The proof works over any perfect field `K`. Nagata's compactification theorem embeds `U₀` as an
open subscheme of a scheme `Z` proper over `K`. Let `C₀` be the relative normalization of `Z` in
`U₀`, i.e. the normalization of `Z` in the function field of `U₀` restricted to `U₀`. Since
normalization commutes with the smooth base change `U₀ ⟶ Z`, the curve `U₀` is a dense open
subscheme of `C₀`; the morphism `C₀ ⟶ Z` is finite, so `C₀` is proper over `K`; it is integral of
dimension `dim U₀ = 1` and has integrally closed local rings because `U₀` has. Being normal of
dimension one, `C₀` is regular, hence smooth over the perfect field `K`. The boundary is the
complement of a nonempty open subset of an irreducible noetherian space of dimension one, hence
a finite set of closed points, and `C₀` is geometrically connected since it contains the
geometrically connected `U₀` as a dense open subscheme.

## Main statements

- `AlgebraicGeometry.exists_smooth_properCompactification`: the smooth proper completion of a
  smooth geometrically connected curve over a finite field.
- `AlgebraicGeometry.exists_smooth_properCompactification_of_perfectField`: the same over a
  perfect field, recording also that the completion is integral and `U₀` dense in it.
- `AlgebraicGeometry.IsCurve.exists_projectiveClosure`: an integral curve over a field is a dense
  open subscheme of an integral closed subscheme of projective space.
- `AlgebraicGeometry.exists_smooth_projectiveCompactification`: a normal geometrically connected
  curve of pure dimension one over a perfect field is smooth and has a smooth projective
  geometrically connected completion with finite boundary.
- `AlgebraicGeometry.IsCurve.isQuasiProjective`: a smooth curve over a field is
  quasi-projective.
- `AlgebraicGeometry.IsConnectedCurve.exists_smooth_properCompactification`: a smooth connected
  curve over an algebraically closed field is a dense open subscheme of a smooth proper
  connected curve, with finite boundary.
- `AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top`: a proper open subscheme of a smooth
  proper connected curve over an algebraically closed field is affine.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {U : Scheme.{u}}

/-- Blueprint `lemma-proper-smooth-model--1`: Finite-field curves admit a
projective closure.

An integral curve `U` over a field `K` (separated, of finite type, of dimension at most one)
admits a locally closed immersion `j ≫ ι` into a projective space `ℙ(n; Spec K)` over `K`, where
`ι : X ⟶ ℙ(n; Spec K)` is a closed immersion of an integral scheme `X` and `j : U ⟶ X` is an open
immersion with dense image; thus `X` is the scheme-theoretic closure of `U` in `ℙ(n; Spec K)`.
The input is that `U` has an ample invertible sheaf (Stacks `0A25`). -/
theorem IsCurve.exists_projectiveClosure (p : U ⟶ Spec (.of K)) [IsCurve p] [IsIntegral U] :
    ∃ (n : Type u) (_ : Finite n) (X : Scheme.{u}) (ι : X ⟶ ℙ(n; Spec (.of K))) (j : U ⟶ X),
      IsClosedImmersion ι ∧ IsOpenImmersion j ∧ IsIntegral X ∧ DenseRange j.base ∧
      j ≫ ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)) = p := by
  -- an ample coordinate cover of `U` gives an immersion `f : U ⟶ ℙ(n; Spec K)`
  obtain ⟨β, hβ, 𝒟, h𝒟⟩ := IsCurve.exists_coordinateCover p
  obtain ⟨n, hn, f, hf, hfp⟩ := 𝒟.exists_isImmersion p h𝒟
  -- `f` is quasi-compact, so it factors through its scheme-theoretic image as an open immersion
  have : IsLocallyNoetherian ℙ(n; Spec (.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of K)) ↘ Spec (.of K))
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace U := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : QuasiCompact f := by
    rw [← f.liftCoborder_ι]
    infer_instance
  have : IsOpenImmersion f.toImage := inferInstance
  -- the scheme-theoretic image is integral
  have : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ U).image f.toImage.base
      f.toImage.base.hom.continuous.continuousOn
    rw [Set.image_univ] at h
    simpa [f.toImage.denseRange.closure_range] using h.closure
  have : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨n, hn, f.image, f.imageι, f.toImage, inferInstance, inferInstance, inferInstance,
    f.toImage.denseRange, by rw [f.toImage_imageι_assoc, hfp]⟩

/-- The smooth proper completion of a smooth geometrically connected curve `U` over a perfect
field `K`: there is a compactification `c` of `p : U ⟶ Spec K` whose ambient scheme `c.Z` is an
integral smooth geometrically connected curve over `K` containing `U` as a dense open subscheme
with complement a finite set of closed points.

`c.Z` is the relative normalization of a Nagata compactification of `U` in `U`. -/
theorem exists_smooth_properCompactification_of_perfectField [PerfectField K]
    (p : U ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ c : Compactification p, IsIntegral c.Z ∧ IsCurve c.g ∧ SmoothOfRelativeDimension 1 c.g ∧
      GeometricallyConnected c.g ∧ DenseRange c.i.base ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  -- `U` is integral of dimension one, with integrally closed local rings.
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_smooth p
  obtain ⟨x, -⟩ := p.surjective (Classical.arbitrary _)
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace U := IsRegular.irreducibleSpace U
  have : IsReduced U := isReduced_of_isReduced_stalk U
  have : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced U
  have hdimU : topologicalKrullDim U = 1 :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mp inferInstance
  have hnormU := isIntegrallyClosed_stalk_of_isRegular (X := U) hdimU.le
  -- Nagata's compactification `U ⟶ Z ⟶ Spec K`, and the normalization of `Z` in `U`.
  obtain ⟨c₀, -⟩ := exists_isDense_compactification p
  have := c₀.isProper
  have := c₀.isOpenImmersion
  have : QuasiCompact c₀.i := by
    have : QuasiCompact (c₀.i ≫ c₀.g) := c₀.comm ▸ inferInstance
    exact .of_comp c₀.i c₀.g
  have : IsFinite c₀.i.fromNormalization := c₀.i.isFinite_fromNormalization c₀.g
  let c : Compactification p :=
    { Z := c₀.i.normalization
      g := c₀.i.fromNormalization ≫ c₀.g
      i := c₀.i.toNormalization
      comm := by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, ← c₀.comm]
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have : IsIntegral c.Z := inferInstanceAs (IsIntegral c₀.i.normalization)
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsProper c.g := c.isProper
  -- `c.Z` has dimension one.
  have : Nonempty c.i.opensRange := ⟨⟨c.i.base x, x, rfl⟩⟩
  have hdim : topologicalKrullDim c.Z = 1 := by
    rw [← topologicalKrullDim_opens_eq c.g c.i.opensRange, ← hdimU]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso c.i.isoOpensRange).isHomeomorph).symm
  have hcurve : IsCurve c.g := { krullDim_le_one := hdim.le }
  -- `c.Z` is normal of dimension one, hence regular, hence smooth.
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_isIntegrallyClosed_stalk
    (fun z ↦ ⟨inferInstance, c₀.i.isIntegrallyClosed_stalk_normalization hnormU z⟩) hdim.le
  have : Smooth c.g := smooth_of_isRegular c.g
  have hsmooth : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr hdim
  -- `c.Z` is geometrically connected.
  have : Nonempty U := ⟨x⟩
  have : GeometricallyConnected (c.i ≫ c.g) := c.comm ▸ inferInstance
  have hconn := GeometricallyConnected.of_isOpenImmersion c.i c.g
  -- The boundary is a finite set of closed points.
  have hopen : IsOpen (Set.range c.i.base) := c.i.isOpenEmbedding.isOpen_range
  have hne : (Set.range c.i.base).Nonempty := ⟨_, x, rfl⟩
  have : CompactSpace c.Z := (quasiCompact_iff_compactSpace c.g).mp inferInstance
  have : IsNoetherian c.Z := ⟨⟩
  exact ⟨c, inferInstance, hcurve, hsmooth, hconn, hopen.dense hne,
    hopen.finite_compl_of_topologicalKrullDim_le_one hdim.le hne,
    fun z hz ↦ hopen.isClosed_singleton_of_mem_compl hdim.le hne hz⟩

/-- Blueprint `lemma-proper-smooth-model--1`: Smooth proper completion.

Every smooth geometrically connected curve `U₀` over a finite field `K` admits a smooth proper
completion: a compactification `c : Compactification p` of the structure morphism
`p : U₀ ⟶ Spec K` whose ambient scheme `c.Z = C₀` is again a smooth geometrically connected
curve over `K`, and whose boundary `C₀ \ U₀` is a finite set of closed points of `C₀`.

The open immersion `U₀ ⟶ C₀` and the properness of `C₀ ⟶ Spec K` are part of the data of a
`Compactification`, so they do not appear among the conclusions. -/
theorem exists_smooth_properCompactification
    {K : Type u} [Field K] [Finite K] {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] :
    ∃ c : Compactification p, IsCurve c.g ∧ SmoothOfRelativeDimension 1 c.g ∧
      GeometricallyConnected c.g ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  obtain ⟨c, -, h₁, h₂, h₃, -, h₄, h₅⟩ := exists_smooth_properCompactification_of_perfectField p
  exact ⟨c, h₁, h₂, h₃, h₄, h₅⟩

/-- Blueprint `lemma-proper-smooth-model--1`: Smooth proper compactification of a
normal finite-field curve.

Let `U` be a normal geometrically connected curve of pure dimension one over a perfect field `K`
(for instance a finite field): its local rings are integrally closed domains and
`dim U = 1`. Then `U` is smooth over `K`, and there is a compactification `c` of `U` whose
ambient scheme `c.Z` is a smooth geometrically connected curve over `K` which is *projective*,
i.e. admits a closed immersion into a projective space over `K`, in which `U` is a dense open
subscheme with finite complement. -/
theorem exists_smooth_projectiveCompactification [PerfectField K] (p : U ⟶ Spec (.of K))
    [IsCurve p] [GeometricallyConnected p]
    (hU : ∀ x : U, IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x))
    (hdim : topologicalKrullDim U = 1) :
    SmoothOfRelativeDimension 1 p ∧ ∃ c : Compactification p, IsCurve c.g ∧
      SmoothOfRelativeDimension 1 c.g ∧ GeometricallyConnected c.g ∧
      (∃ (n : Type u) (_ : Finite n) (ι : c.Z ⟶ ℙ(n; Spec (.of K))), IsClosedImmersion ι ∧
        ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)) = c.g) ∧
      DenseRange c.i.base ∧ (Set.range c.i.base)ᶜ.Finite := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_isIntegrallyClosed_stalk hU hdim.le
  have : Smooth p := smooth_of_isRegular p
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace U := irreducibleSpace_of_isDomain_stalk U fun x ↦ (hU x).1
  have hsmooth : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mpr hdim
  refine ⟨hsmooth, ?_⟩
  obtain ⟨c, hint, hcurve, hsm, hconn, hdense, hfin, -⟩ :=
    exists_smooth_properCompactification_of_perfectField p
  -- The projective closure `X` of `c.Z` is `c.Z` itself, since `c.Z` is proper.
  obtain ⟨n, hn, X, ι, j, hι, hj, -, hjd, hcomm⟩ := IsCurve.exists_projectiveClosure c.g
  have := c.isProper
  have : IsProper (j ≫ ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K))) := hcomm ▸ inferInstance
  have : IsProper j := .of_comp j (ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)))
  have : Surjective j := by
    refine ⟨fun y ↦ ?_⟩
    have : Set.range j.base = Set.univ := by
      rw [← (j.isClosedMap.isClosed_range).closure_eq, hjd.closure_range]
    exact Set.range_eq_univ.mp this y
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hj, ‹_›⟩
  exact ⟨c, hcurve, hsm, hconn, ⟨n, hn, j ≫ ι, inferInstance, by simpa using hcomm⟩, hdense,
    hfin⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Smooth curves are quasi-projective.** A smooth curve `U` over a field `K` (separated, of
finite type, of dimension at most one) admits an immersion into a projective space over `K`.

Each of the finitely many connected components of `U` is an integral curve, hence a dense open
subscheme of a closed subscheme of a projective space
(`AlgebraicGeometry.IsCurve.exists_projectiveClosure`), so it has a coordinate cover by affine
charts (`AlgebraicGeometry.exists_isAffineOpen_preimage_of_isImmersion`). These glue to a
coordinate cover of `U` by affine charts (`AlgebraicGeometry.Scheme.CoordinateCover.sigma`), which
gives an immersion into projective space
(`AlgebraicGeometry.Scheme.CoordinateCover.exists_isImmersion`). The blueprint instead glues
embeddings of the members of an affine cover one at a time (Stacks `0A25`).
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem IsCurve.isQuasiProjective (p : U ⟶ Spec (.of K)) [IsCurve p] [Smooth p] :
    IsQuasiProjective p := by
  classical
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace U := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian U := ⟨⟩
  have : IsRegular U := IsRegular.of_smooth p
  -- the connected components `V c` of `U`
  choose x hx using ConnectedComponents.surjective_coe (α := U)
  let V (c : ConnectedComponents U) : U.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hVx (y : U) : y ∈ V y := by
    change y ∈ connectedComponent (x y)
    rw [ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  have hV : Pairwise (Function.onFun Disjoint V) := by
    intro c d hcd
    have h : Disjoint (V c : Set U) (V d : Set U) := by
      refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
        (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
      rw [← hx c, ← hx d, ConnectedComponents.coe_eq_coe,
        connectedComponent_eq hyc, connectedComponent_eq hyd]
    exact disjoint_iff.mpr (SetLike.coe_injective
      (by simpa using Set.disjoint_iff_inter_eq_empty.mp h))
  have hcov : ⨆ c, V c = ⊤ :=
    eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hVx y⟩
  -- each component has a coordinate cover by affine charts
  have key (c : ConnectedComponents U) : ∃ (β : Type u) (_ : Finite β)
      (𝒟 : (V c).toScheme.CoordinateCover β), ∀ b, IsAffineOpen (𝒟.U b) := by
    have : ConnectedSpace (V c) :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    have : IsCurve ((V c).ι ≫ p) :=
      { krullDim_le_one :=
          (topologicalKrullDim_subspace_le U (V c)).trans (IsCurve.krullDim_le_one p) }
    have : IsRegular (V c) := IsRegular.of_smooth ((V c).ι ≫ p)
    have : IrreducibleSpace (V c) := IsRegular.irreducibleSpace _
    have : IsReduced (V c) := isReduced_of_isReduced_stalk _
    have : IsIntegral (V c) := isIntegral_of_irreducibleSpace_of_isReduced _
    have : CompactSpace (V c) :=
      isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := x c)).isCompact
    obtain ⟨n, _, X, ι, j, hι, hj, -, -, hcomm⟩ := IsCurve.exists_projectiveClosure ((V c).ι ≫ p)
    have : IsImmersion (j ≫ ι) := inferInstance
    have : IsLocallyNoetherian ℙ(n; Spec (.of K)) :=
      LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of K)) ↘ Spec (.of K))
    have : QuasiCompact (j ≫ ι) := quasiCompact_of_compactSpace _
    obtain ⟨β, hβ, ψ, -, hψ⟩ := exists_isAffineOpen_preimage_of_isImmersion (j ≫ ι)
    let ρ := ψ ≫ ProjectiveSpace.toProjInt β (Spec (.of K))
    have hX (b : β) : MvPolynomial.X b ∈
        MvPolynomial.homogeneousSubmodule β (ULift.{u} ℤ) 1 :=
      MvPolynomial.X_mem_homogeneousSubmodule_one _ b
    have hpre (b : β) : ρ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule β (ULift.{u} ℤ))
        (MvPolynomial.X b) = ψ ⁻¹ᵁ ProjectiveSpace.standardOpen β (Spec (.of K)) b := rfl
    have hcovψ : ⨆ b, ρ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule β (ULift.{u} ℤ))
        (MvPolynomial.X b) = ⊤ := by
      simp only [hpre]
      rw [← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen, Scheme.Hom.preimage_top]
    exact ⟨β, hβ, Scheme.CoordinateCover.ofProj _ ρ one_pos _ hX hcovψ, fun b ↦ hψ b⟩
  choose β hβ 𝒟 h𝒟 using key
  let 𝒟' := Scheme.CoordinateCover.sigma V 𝒟 hV hcov
  exact 𝒟'.exists_isImmersion p fun a ↦ (h𝒟 a.1 a.2).image_of_isOpenImmersion (V a.1).ι

/-- **Compactification of a smooth curve.** A smooth connected curve `U` over an algebraically
closed field `K` admits a compactification `c` whose ambient scheme `c.Z` is a smooth proper
connected curve over `K`, in which `U` is open with complement a finite set of closed points.

The compactification is the normalization of a Nagata compactification of `U` in `U`, as in
`AlgebraicGeometry.exists_smooth_properCompactification_of_perfectField`; the blueprint uses the
normalization of the closure of `U` in a projective space instead.
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem IsConnectedCurve.exists_smooth_properCompactification [IsAlgClosed K]
    (p : U ⟶ Spec (.of K)) [IsConnectedCurve p] [Smooth p] :
    ∃ c : Compactification p, IsConnectedCurve c.g ∧ Smooth c.g ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  have := IsConnectedCurve.connectedSpace (f := p)
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_smooth p
  have : IrreducibleSpace U := IsRegular.irreducibleSpace U
  have : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := p))
  let : U.Over (Spec (.of K)) := ⟨p⟩
  have : GeometricallyConnected p := GeometricallyConnected.of_isSepClosed (k := K) U
  obtain ⟨c, hint, hcurve, hsm, -, -, hfin, hclosed⟩ :=
    exists_smooth_properCompactification_of_perfectField p
  have : Smooth c.g := SmoothOfRelativeDimension.smooth 1 c.g
  have hconn : IsConnectedCurve c.g :=
    { toIsCurve := hcurve
      connectedSpace := inferInstance
      krullDim_eq_one := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mp hsm }
  exact ⟨c, hconn, inferInstance, hfin, hclosed⟩

/-- A smooth connected curve is smooth of relative dimension one. -/
lemma IsConnectedCurve.smoothOfRelativeDimension_one {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    [IsConnectedCurve f] [Smooth f] : SmoothOfRelativeDimension 1 f := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
    (IsConnectedCurve.krullDim_eq_one (f := f))

/-- **Open subschemes of a proper curve are affine.** Let `C` be a smooth proper connected curve
over an algebraically closed field `K`. Every open subscheme `V ≠ C` is affine: its complement
`S` is a finite nonempty set of closed points, the effective divisor `D = ∑_{P ∈ S} [P]` has
positive degree, so `𝒪(D)` is ample, and `V = C ∖ D` is affine.
(blueprint: `proposition-p-torsion-smooth-proper-curve--3`) -/
theorem IsConnectedCurve.isAffine_of_ne_top [IsAlgClosed K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [IsConnectedCurve p] [Smooth p] [IsProper p] (V : C.Opens)
    (hV : V ≠ ⊤) : IsAffine V := by
  classical
  have := IsConnectedCurve.connectedSpace (f := p)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular C := IsRegular.of_smooth p
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have hdim : topologicalKrullDim C = 1 := IsConnectedCurve.krullDim_eq_one (f := p)
  have : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mpr hdim
  rcases (V : Set C).eq_empty_or_nonempty with hVe | hne
  · have : IsEmpty V := ⟨fun x ↦ by
      have h : V.ι x ∈ Set.range V.ι := ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι, hVe] at h
      exact h⟩
    infer_instance
  have : CompactSpace C := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  -- the complement `S` of `V` is a finite set of closed points
  have hfin := V.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim.le hne
  have hcl (x : C) (hx : x ∈ (V : Set C)ᶜ) : IsClosed ({x} : Set C) :=
    V.isOpen.isClosed_singleton_of_mem_compl hdim.le hne hx
  -- the effective Cartier divisor `D = ∑_{P ∈ S} [P]`
  have key (S : Finset C) (hS : ∀ x ∈ S, IsClosed ({x} : Set C)) :
      ∃ J : C.IdealSheafData, J.IsInvertible ∧ (J.support : Set C) = S := by
    induction S using Finset.induction_on with
    | empty => exact ⟨⊤, Scheme.IdealSheafData.isInvertible_top, by simp⟩
    | insert Q S hQ ih =>
      obtain ⟨J, hJ, hJS⟩ := ih fun x hx ↦ hS x (Finset.mem_insert_of_mem hx)
      have hQc := hS Q (Finset.mem_insert_self Q S)
      refine ⟨J * Scheme.IdealSheafData.vanishingIdeal ⟨{Q}, hQc⟩,
        hJ.mul (isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one p hQc), ?_⟩
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, hJS]
      ext x
      simp
  obtain ⟨J, hJ, hJS⟩ := key hfin.toFinset fun x hx ↦ hcl x (hfin.mem_toFinset.1 hx)
  rw [Set.Finite.coe_toFinset] at hJS
  let : C.Over (Spec (.of K)) := ⟨p⟩
  have hf : C ↘ Spec (.of K) = p := rfl
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := by rw [hf]; infer_instance
  have : IsProper (C ↘ Spec (.of K)) := by rw [hf]; infer_instance
  have : IsReduced C := isReduced_of_smooth p
  have : Scheme.GlobalSectionsBijective K C := Scheme.GlobalSectionsBijective.of_isAlgClosed
  -- `D` is finite and nonempty over `K`, so it has positive degree
  have : Finite (Set.range J.subschemeι.base) := by
    rw [J.range_subschemeι, hJS]
    exact hfin.to_subtype
  have : Finite J.subscheme :=
    Finite.of_injective (Set.rangeFactorization J.subschemeι.base)
      (Set.rangeFactorization_injective.mpr J.subschemeι.isEmbedding.injective)
  have hne' : Nonempty J.subscheme := by
    obtain ⟨Q, hQ⟩ : ((V : Set C)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h ↦ hV (SetLike.coe_injective h)
    have : Q ∈ Set.range J.subschemeι.base := by rw [J.range_subschemeι, hJS]; exact hQ
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  have : LocallyQuasiFinite (J.subschemeι ≫ p) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  have : IsFinite (J.subschemeι ≫ p) := .of_isProper_of_locallyQuasiFinite _
  have hpos : 0 < (J.subschemeι ≫ p).finrankΓ := by
    have hfin := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)
      (f := J.subschemeι ≫ p)).mp inferInstance
    let := (J.subschemeι ≫ p).ΓAlgebra
    have : Module.Finite K Γ(J.subscheme, ⊤) := by
      have h2 : RingHom.Finite ((Scheme.ΓSpecIso (.of K)).inv ≫
          (J.subschemeι ≫ p).appTop).hom := by
        rw [CommRingCat.hom_comp]
        exact hfin.2.comp (RingHom.Finite.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
      exact h2
    have : Nonempty (⊤ : J.subscheme.Opens) := ⟨⟨hne'.some, trivial⟩⟩
    exact Module.finrank_pos
  have hdeg : 0 < J.toModulesᵛ.degree K := by
    rw [hJ.degree_dual_toModules]
    exact_mod_cast hpos
  have := hJ.isInvertible_dual_toModules
  have hample := Scheme.isAmple_of_degree_pos_of_isAlgClosed (k := K) J.toModulesᵛ hdeg
  exact Scheme.isAffine_compl_of_isAmple hJ hample V.ι (by simp [hJS])

end AlgebraicGeometry
