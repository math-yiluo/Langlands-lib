import Langlands.AlgebraicGeometry.SchemeGeometricComponentCountBaseChange
import Langlands.AlgebraicGeometry.GeometricallyConnectedConstructibilityFromGeneric
import Langlands.AlgebraicGeometry.FiniteEtaleGenericComponentSplittingProof
import Langlands.AlgebraicGeometry.GeometricIrreducibilityProof

/-! # Constructibility of every geometric connected-component count for schemes -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open GenericImagePattern

/-- The geometric component count of actual fibres equals its value at the given
point throughout an open neighbourhood of that point. -/
def GeometricFiberComponentCountConstancyAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : Y) : Prop :=
  ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
    geometricFiberComponentCount f y = geometricFiberComponentCount f η

variable {X Y : Scheme.{u}}

/-- When all generic-fibre components are geometrically irreducible, the geometric
component count is constant near the generic point of a Noetherian base. -/
theorem geometricFiberComponentCountConstancyAt_of_split_components
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (hgeom : FiberComponentsGeometricallyIrreducible f η) :
    GeometricFiberComponentCountConstancyAt f η := by
  obtain ⟨U, hU, hηU, hpattern⟩ :=
    exists_open_genericComponentClosures_geometricallyIrreducible_and_incidence
      finiteTypeGeometricallyIrreducibleGenericSpreading f hη hgeom
  let : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField η))
    infer_instance
  let : IsNoetherian (f.fiber η) :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
      toCompactSpace := inferInstance }
  let := (NoetherianSpace.finite_irreducibleComponents (α := f.fiber η)).to_subtype
  have hcount (y : Y) (hy : y ∈ U) :
      geometricFiberComponentCount f y =
        ENat.card (Quot (fun C D : irreducibleComponents (f.fiber η) =>
          (C.val ∩ D.val).Nonempty)) := by
    have hpieces (C : irreducibleComponents (f.fiber η)) : GeometricallyConnected
        (pullback.snd (fiberComponentClosureι f η C) (f.fiberι y) ≫
          f.fiberToSpecResidueField y) :=
      let := (hpattern y hy).2.1 C
      geometricallyConnected_of_geometricallyIrreducible _
    exact (geometricFiberComponentCount_eq_incidence f (fiberComponentClosureι f η) y
      (hpattern y hy).1 hpieces).trans
        (ENat.card_congr (Quot.congr (Equiv.refl _) (hpattern y hy).2.2))
  exact ⟨U, hU, hηU, fun y hy => (hcount y hy).trans (hcount η hηU).symm⟩

section OpenDescent

variable {P X' Y' : Scheme.{u}} {a : P ⟶ X'} {b : P ⟶ Y'} {f : X' ⟶ Y} {g : Y' ⟶ Y}

/-- Constancy near any point upstairs gives constancy near the generic point
downstairs when the cartesian base-change map is open. -/
theorem geometricFiberComponentCountConstancyAt_of_open_baseChange
    (h : IsPullback a b f g) [LocallyOfFiniteType f] [QuasiCompact f] (hg : IsOpenMap g)
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) {η' : Y'}
    (hc : GeometricFiberComponentCountConstancyAt b η') :
    GeometricFiberComponentCountConstancyAt f η := by
  obtain ⟨W, hW, hη'W, hconst⟩ := hc
  have hopen : IsOpen (g '' W) := hg W hW
  have hηW : η ∈ g '' W :=
    (hη.mem_open_set_iff hopen).mpr ⟨g η', Set.mem_univ _, ⟨η', hη'W, rfl⟩⟩
  obtain ⟨ζ, hζ, hζη⟩ := hηW
  refine ⟨g '' W, hopen, ⟨ζ, hζ, hζη⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [← hζη, ← geometricFiberComponentCount_baseChange h,
    ← geometricFiberComponentCount_baseChange h]
  exact (hconst y hy).trans (hconst ζ hζ).symm

end OpenDescent

/-- The geometric component count is constant near a whole-space generic point of
every Noetherian finite-type family. -/
theorem geometricFiberComponentCountConstancyAt_of_isGenericPoint
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    GeometricFiberComponentCountConstancyAt f η := by
  let : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr hη.isIrreducible
  obtain ⟨V, _, Y', g, _, hirr, hsurj, hfinite, hetale, _, _, _, η', hη', hgeom⟩ :=
    finiteTypeFiniteEtaleGenericComponentSplitting f
  let := hirr
  let := hsurj
  let := hfinite
  let := hetale
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (NoetherianSpace.isCompact (V : Set Y)) }
  let : IsNoetherian Y' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  have hc := geometricFiberComponentCountConstancyAt_of_split_components
    (pullback.snd (f ∣_ V) g) hη' hgeom
  exact geometricFiberComponentCountConstancyAt_of_open_baseChange
    ((IsPullback.of_hasPullback (f ∣_ V) g).paste_horiz
      (isPullback_morphismRestrict f V).flip)
    (V.ι.isOpenEmbedding.isOpenMap.comp g.isOpenMap) hη hc

/-- On every irreducible closed subset of a Noetherian base, each level set of the
geometric component count either contains or misses a nonempty relatively open part. -/
theorem exists_open_irreducibleClosed_geometricFiberComponentCount
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ∞)
    (Z : Set Y) (hZ : IsClosed Z) (hirr : IsIrreducible Z) :
    ∃ V : Set Y, IsOpen V ∧ (Z ∩ V).Nonempty ∧
      (Z ∩ V ⊆ {y | geometricFiberComponentCount f y = n} ∨
        Disjoint (Z ∩ V) {y | geometricFiberComponentCount f y = n}) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z, hZ⟩ : TopologicalSpace.Closeds Y)
  let g := I.subschemeι
  have hrange : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  let : IsNoetherian I.subscheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace Z
    exact isIrreducible_iff_irreducibleSpace.mp hirr
  let η := genericPoint I.subscheme
  obtain ⟨W, hW, hηW, hconst⟩ := geometricFiberComponentCountConstancyAt_of_isGenericPoint
    (pullback.snd f g) (genericPoint_spec I.subscheme)
  obtain ⟨V, hV, himage⟩ := g.isEmbedding.isInducing.image_eq_isOpen_inter_range hW
  have himage' : g '' W = Z ∩ V := by
    simpa only [hrange, Set.inter_comm] using himage
  have hηV : g η ∈ Z ∩ V := himage' ▸ Set.mem_image_of_mem g hηW
  have hconst' : ∀ y ∈ Z ∩ V,
      geometricFiberComponentCount f y = geometricFiberComponentCount f (g η) := by
    rw [← himage']
    rintro _ ⟨y, hy, rfl⟩
    rw [← geometricFiberComponentCount_baseChange (IsPullback.of_hasPullback f g),
      ← geometricFiberComponentCount_baseChange (IsPullback.of_hasPullback f g)]
    exact hconst y hy
  refine ⟨V, hV, ⟨g η, hηV⟩, ?_⟩
  by_cases hc : geometricFiberComponentCount f (g η) = n
  · exact Or.inl (fun y hy => (hconst' y hy).trans hc)
  · exact Or.inr (Set.disjoint_left.mpr fun y hy hyc => hc ((hconst' y hy).symm.trans hyc))

/-- Over a Noetherian base, every level set of the geometric component count of a
finite-type quasi-compact morphism is constructible. -/
theorem isConstructible_geometricFiberComponentCount_of_isNoetherian
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ∞) :
    IsConstructible {y | geometricFiberComponentCount f y = n} :=
  isConstructible_of_irreducibleClosed_genericConstancy _
    (exists_open_irreducibleClosed_geometricFiberComponentCount f n)

/-- Conrad's Lemma 5.1 for schemes over an arbitrary affine base: every geometric
connected-component count of a finite-presentation family is a constructible condition. -/
theorem schemeGeometricComponentCountConstructible :
    SchemeGeometricComponentCountConstructibleStatement.{u} := by
  intro B _ X f _ _ _ n
  let : Algebra (ULift.{u} ℤ) B := ULift.algebra' ℤ B
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, _, X₀, f₀, π, hfp, hqc, hqs, hs⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent (A₀ := ULift.{u} ℤ) f ∅
  let : Algebra.FiniteType (ULift.{u} ℤ) T := T.fg_iff_finiteType.mp hT
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) T
  let := hfp
  let := hqc
  have hset : {p | geometricFiberComponentCount f p = n} =
      (Spec.map (CommRingCat.ofHom (algebraMap T B))) ⁻¹'
        {p | geometricFiberComponentCount f₀ p = n} := by
    ext p
    exact Iff.of_eq (congrArg (· = (n : ℕ∞)) (geometricFiberComponentCount_baseChange hs p))
  rw [hset]
  exact (Spec.map (CommRingCat.ofHom (algebraMap T B))).isConstructible_preimage
    (isConstructible_geometricFiberComponentCount_of_isNoetherian f₀ n)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
