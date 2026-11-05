import Langlands.AlgebraicGeometry.PointTopology.UnirationalBaseChange
import Langlands.AlgebraicGeometry.PointTopology.UnirationalSpreading
import Langlands.AlgebraicGeometry.PointTopology.IteratedAffineSpace
import Mathlib.AlgebraicGeometry.Fiber

/-! # Unirationality from a unirational base and a unirational generic fiber -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A morphism from the spectrum of a field factors through the residue field
of the image of its unique point. -/
theorem exists_factor_fromSpecResidueField {K : Type u} [Field K] {X : Scheme.{u}}
    (g : Spec (CommRingCat.of K) ⟶ X) (a : Spec (CommRingCat.of K)) (x : X)
    (hx : g a = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K,
      Spec.map ψ ≫ X.fromSpecResidueField x = g := by
  have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst hx ha
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X g⟩

/-- Iterated finite-dimensional affine space over a field is unirational. -/
theorem isUnirational_iteratedAffineSpace {k : Type u} [Field k]
    (ι' ι : Type u) [Finite ι'] [Finite ι] :
    IsUnirational k (Over.mk
      (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))) ↘ 𝔸(ι; Spec (CommRingCat.of k)) ≫
        𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) := by
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨x, -⟩ :=
    (𝔸(ι ⊕ ι'; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).surjective s
  refine ⟨ι ⊕ ι', inferInstance, ⊤, ⟨x, trivial⟩,
    Over.homMk ((⊤ : (𝔸(ι ⊕ ι'; Spec (CommRingCat.of k))).Opens).ι ≫
      (affineSpaceSumIso ι ι' _).hom) ?_, ?_⟩
  · change ((⊤ : (𝔸(ι ⊕ ι'; Spec (CommRingCat.of k))).Opens).ι ≫
        (affineSpaceSumIso ι ι' _).hom) ≫
        (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))) ↘ 𝔸(ι; Spec (CommRingCat.of k)) ≫
          𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      (⊤ : (𝔸(ι ⊕ ι'; Spec (CommRingCat.of k))).Opens).ι ≫
        𝔸(ι ⊕ ι'; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)
    rw [Category.assoc, affineSpaceSumIso_hom_over]
  · refine Function.Surjective.denseRange fun y => ?_
    refine ⟨⟨(affineSpaceSumIso ι ι' _).inv y, trivial⟩, ?_⟩
    change ((affineSpaceSumIso ι ι' _).inv ≫ (affineSpaceSumIso ι ι' _).hom) y = y
    rw [Iso.inv_hom_id]
    rfl

/-- The fiber hypothesis of the generic-fiber criterion: the scheme-theoretic fiber of
`f : X ⟶ Y` over the point `η` is unirational over the residue field `κ(η)`, and the canonical
map from that fiber to `X` has dense image. -/
def HasUnirationalDenseFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y) : Prop :=
  IsUnirational (Y.residueField η) (Over.mk (f.fiberToSpecResidueField η)) ∧
    DenseRange (f.fiberι η)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Generic-fiber criterion.** Let `f : X → Y` be a morphism over a field
`k`, with `X` locally of finite type over `k`. If `Y` is unirational, `η` is a
generic point of `Y`, the scheme-theoretic fiber of `f` over `η` is unirational
over the residue field `κ(η)`, and that fiber has dense image in `X`, then `X`
is unirational over `k`. -/
theorem IsUnirational.of_genericFiber
    {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom)
    (hY : IsUnirational k Y) (η : Y.left) (hη : IsGenericPoint η Set.univ)
    (hfib : IsUnirational (Y.left.residueField η)
      (Over.mk (f.fiberToSpecResidueField η)))
    (hdense : DenseRange (f.fiberι η)) :
    IsUnirational k X := by
  obtain ⟨ι, hι, U, hU, p, hp⟩ := hY
  -- The generic point `u` of the parametrizing affine space lies in `U`.
  let u : 𝔸(ι; Spec (CommRingCat.of k)) := genericPoint _
  have hu : IsGenericPoint u Set.univ := genericPoint_spec _
  have huU : u ∈ U := (hu.mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  -- Its residue field maps to `Y` through `U`, hitting the generic point `η`.
  let t : Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι ((𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u)
      (by
        rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
        simpa using huU)
  have ht : t ≫ U.ι = (𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨a₀⟩ : Nonempty (Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) :=
    inferInstance
  have hpt : (t ≫ p.left) a₀ = η := by
    have h1 : IsGenericPoint (t a₀) Set.univ := by
      refine SchemeFiberGeometry.isGenericPoint_of_isInducing U.ι.isOpenEmbedding.isInducing ?_
      rw [← Scheme.Hom.comp_apply, ht, Scheme.fromSpecResidueField_apply]
      exact hu
    rw [Scheme.Hom.comp_apply]
    exact (isGenericPoint_univ_of_denseRange p.left.continuous hp h1).eq hη
  obtain ⟨φ₁, hφ₁⟩ := exists_factor_fromSpecResidueField
    (K := (𝔸(ι; Spec (CommRingCat.of k))).residueField u) (t ≫ p.left) a₀ η hpt
  let : Algebra (Y.left.residueField η)
      ((𝔸(ι; Spec (CommRingCat.of k))).residueField u) := φ₁.hom.toAlgebra
  have hφ₁' : Spec.algebraMap (Y.left.residueField η)
      ((𝔸(ι; Spec (CommRingCat.of k))).residueField u) = Spec.map φ₁ := rfl
  -- Extend the generic-fiber parametrization to the function field.
  obtain ⟨ι', hι', V, hV, g, hg⟩ :=
    hfib.baseChange (K := (𝔸(ι; Spec (CommRingCat.of k))).residueField u)
  -- The iterated affine space and its generic point.
  let gen : 𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))) := genericPoint _
  have hgen : IsGenericPoint gen Set.univ := genericPoint_spec _
  have hgenu : (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))) ↘
      𝔸(ι; Spec (CommRingCat.of k))) gen = u :=
    (isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _)
      (Scheme.Hom.surjective _).denseRange hgen).eq hu
  obtain ⟨b₀⟩ : Nonempty (Spec (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).functionField) :=
    inferInstance
  have hb₀ : (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).fromSpecStalk gen b₀ = gen := by
    convert Scheme.fromSpecStalk_closedPoint (X := 𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))))
      (x := gen) using 2
    exact Subsingleton.elim (α := PrimeSpectrum _) _ _
  obtain ⟨ψ₀, hψ₀⟩ := exists_factor_fromSpecResidueField
    (K := (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).functionField)
    ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).fromSpecStalk gen ≫
      (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k))) ↘ 𝔸(ι; Spec (CommRingCat.of k)))) b₀ u
    (by rw [Scheme.Hom.comp_apply, hb₀, hgenu])
  -- The generic point of affine space over the function field.
  let s : Spec (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).functionField ⟶
      𝔸(ι'; Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) :=
    AffineSpace.homOfVector (Spec.map ψ₀)
      (fun i => ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).fromSpecStalk gen).appTop
        (AffineSpace.coord _ i))
  have hs : s ≫ AffineSpace.map ι'
      ((𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u) =
      (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).fromSpecStalk gen := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.map_over, s,
        AffineSpace.homOfVector_over_assoc]
      exact hψ₀
    · intro i
      simp [s]
  have hm : IsPreimmersion (AffineSpace.map ι'
      ((𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion)
      (AffineSpace.isPullback_map (n := ι')
        ((𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u)).flip inferInstance
  have hz : IsGenericPoint (s b₀) Set.univ := by
    refine SchemeFiberGeometry.isGenericPoint_of_isInducing
      (Scheme.Hom.isEmbedding (AffineSpace.map ι'
        ((𝔸(ι; Spec (CommRingCat.of k))).fromSpecResidueField u))).isInducing ?_
    rw [← Scheme.Hom.comp_apply, hs, hb₀]
    exact hgen
  have hzV : s b₀ ∈ V :=
    (hz.mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  let s' := IsOpenImmersion.lift V.ι s (by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum _) w b₀, Scheme.Opens.range_ι]
    exact hzV)
  have hs' : s' ≫ V.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hw : IsGenericPoint (s' b₀) Set.univ := by
    refine SchemeFiberGeometry.isGenericPoint_of_isInducing V.ι.isOpenEmbedding.isInducing ?_
    rw [← Scheme.Hom.comp_apply, hs']
    exact hz
  have hsurj : Surjective (Spec.algebraMap (Y.left.residueField η)
      ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) :=
    ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hfst : Surjective (pullback.fst (Over.mk (f.fiberToSpecResidueField η)).hom
      (Spec.algebraMap (Y.left.residueField η)
        ((𝔸(ι; Spec (CommRingCat.of k))).residueField u))) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback _ _).flip hsurj
  let φ := s' ≫ g.left ≫ pullback.fst (Over.mk (f.fiberToSpecResidueField η)).hom
      (Spec.algebraMap (Y.left.residueField η)
        ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) ≫ f.fiberι η
  have hφ : φ ≫ X.hom =
      (𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).fromSpecStalk gen ≫
        ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))) ↘ 𝔸(ι; Spec (CommRingCat.of k)) ≫
          𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) := by
    have hg' : g.left ≫ pullback.snd (Over.mk (f.fiberToSpecResidueField η)).hom
        (Spec.algebraMap (Y.left.residueField η)
          ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) =
        V.ι ≫ (𝔸(ι'; Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) ↘
            Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) :=
      Over.w g
    have hp' : p.left ≫ Y.hom = U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)) := Over.w p
    have hcond : pullback.fst (Over.mk (f.fiberToSpecResidueField η)).hom
        (Spec.algebraMap (Y.left.residueField η)
          ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) ≫
          f.fiberToSpecResidueField η =
        pullback.snd (Over.mk (f.fiberToSpecResidueField η)).hom
          (Spec.algebraMap (Y.left.residueField η)
            ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) ≫
          Spec.algebraMap (Y.left.residueField η)
            ((𝔸(ι; Spec (CommRingCat.of k))).residueField u) :=
      pullback.condition
    have hsover : s ≫ 𝔸(ι'; Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u)) ↘
        Spec ((𝔸(ι; Spec (CommRingCat.of k))).residueField u) = Spec.map ψ₀ :=
      AffineSpace.homOfVector_over _ _
    simp only [φ, Category.assoc]
    rw [← hf, Scheme.Hom.fiber_fac_assoc, reassoc_of% hcond, reassoc_of% hg',
      reassoc_of% hs', reassoc_of% hsover, hφ₁', reassoc_of% hφ₁, hp', reassoc_of% ht,
      reassoc_of% hψ₀]
  have hdenseφ : DenseRange φ := by
    refine denseRange_of_isGenericPoint (a := b₀) ?_
    simp only [φ, Scheme.Hom.comp_apply]
    exact isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _) hdense
      (isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _)
        hfst.surj.denseRange
        (isGenericPoint_univ_of_denseRange (Scheme.Hom.continuous _) hg hw))
  have : (Over.mk ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))) ↘
      𝔸(ι; Spec (CommRingCat.of k)) ≫
        𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))).left.IsGermInjectiveAt
          gen :=
    inferInstanceAs ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))).IsGermInjectiveAt gen)
  exact (isUnirational_iteratedAffineSpace (k := k) ι' ι).of_stalk
    (Y := Over.mk ((𝔸(ι'; 𝔸(ι; Spec (CommRingCat.of k)))) ↘
      𝔸(ι; Spec (CommRingCat.of k)) ≫
        𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) gen φ hφ hdenseφ

/-- The generic-fiber criterion, with the fiber hypothesis packaged as
`HasUnirationalDenseFiber`. -/
theorem IsUnirational.of_hasUnirationalDenseFiber
    {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom)
    (hY : IsUnirational k Y) (η : Y.left) (hη : IsGenericPoint η Set.univ)
    (hfib : HasUnirationalDenseFiber f η) :
    IsUnirational k X :=
  IsUnirational.of_genericFiber f hf hY η hη hfib.1 hfib.2

end Langlands.AlgebraicGeometry.PointTopology
