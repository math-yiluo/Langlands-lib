import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTower

/-! # Conjugation of the original finite-index rational towers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual open subgroup conjugation preserves inclusions. -/
theorem conjugateOpenSubgroup_mono {V W : OpenSubgroup G} (h : V ≤ W) (g : G) :
    conjugateOpenSubgroup V g ≤ conjugateOpenSubgroup W g :=
  fun _ hk => h hk

/-- Inverse conjugation also reflects inclusions. -/
theorem conjugateOpenSubgroup_le_iff (V W : OpenSubgroup G) (g : G) :
    conjugateOpenSubgroup V g ≤ conjugateOpenSubgroup W g ↔ V ≤ W := by
  constructor
  · intro h
    simpa only [conjugateOpenSubgroup_inv] using conjugateOpenSubgroup_mono h g⁻¹
  · exact fun h => conjugateOpenSubgroup_mono h g

/-- The actual relative index is unchanged by simultaneous conjugation. -/
theorem relIndex_conjugateOpenSubgroup (V W : OpenSubgroup G) (g : G) :
    (conjugateOpenSubgroup V g).toSubgroup.relIndex
        (conjugateOpenSubgroup W g).toSubgroup =
      V.toSubgroup.relIndex W.toSubgroup := by
  change (V.toSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom).relIndex
    (W.toSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom) = _
  rw [Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g⁻¹).surjective]

/-- Conjugation retains the original subgroup intersection. -/
theorem conjugateOpenSubgroup_inf (V W : OpenSubgroup G) (g : G) :
    conjugateOpenSubgroup (V ⊓ W) g =
      conjugateOpenSubgroup V g ⊓ conjugateOpenSubgroup W g := by
  ext k
  rfl

namespace OpenSubgroupTransport.FiniteIndexLevel

variable {U : OpenSubgroup G}

/-- All original finite-index levels correspond by actual subgroup conjugation. -/
def conjugationOrderIso (U : OpenSubgroup G) (g : G) :
    FiniteIndexLevel U ≃o FiniteIndexLevel (conjugateOpenSubgroup U g) where
  toFun V := ⟨conjugateOpenSubgroup V.val g,
    conjugateOpenSubgroup_mono V.property.1 g, by
      rw [relIndex_conjugateOpenSubgroup]
      exact V.property.2⟩
  invFun W := ⟨conjugateOpenSubgroup W.val g⁻¹, by
    simpa only [conjugateOpenSubgroup_inv] using
      conjugateOpenSubgroup_mono W.property.1 g⁻¹, by
    have h := relIndex_conjugateOpenSubgroup W.val (conjugateOpenSubgroup U g) g⁻¹
    rw [conjugateOpenSubgroup_inv] at h
    rw [h]
    exact W.property.2⟩
  left_inv V := Subtype.ext (conjugateOpenSubgroup_inv V.val g)
  right_inv W := Subtype.ext (by
    simpa only [inv_inv] using conjugateOpenSubgroup_inv W.val g⁻¹)
  map_rel_iff' := fun {V W} => conjugateOpenSubgroup_le_iff V.val W.val g

/-- Conjugation is an equivalence of the actual thin level categories. -/
def conjugationEquivalence (U : OpenSubgroup G) (g : G) :
    FiniteIndexLevel U ≌ FiniteIndexLevel (conjugateOpenSubgroup U g) :=
  (conjugationOrderIso U g).equivalence

@[simp]
theorem conjugationEquivalence_obj_val (g : G) (V : FiniteIndexLevel U) :
    ((conjugationEquivalence U g).functor.obj V).val = conjugateOpenSubgroup V.val g :=
  rfl

/-- The largest original level goes to the largest conjugate level. -/
@[simp]
theorem conjugationOrderIso_base (g : G) :
    conjugationOrderIso U g (base U) = base (conjugateOpenSubgroup U g) :=
  Subtype.ext rfl

/-- Canonical common refinements are transported by the same actual intersection. -/
@[simp]
theorem conjugationOrderIso_commonRefinement (g : G) (V W : FiniteIndexLevel U) :
    conjugationOrderIso U g (commonRefinement V W) =
      commonRefinement (conjugationOrderIso U g V) (conjugationOrderIso U g W) :=
  Subtype.ext (conjugateOpenSubgroup_inf V.val W.val g)

/-- Every original tower degree is preserved, including between incomparable levels. -/
@[simp]
theorem conjugationOrderIso_relIndex (g : G) (V W : FiniteIndexLevel U) :
    (conjugationOrderIso U g V).val.toSubgroup.relIndex
        (conjugationOrderIso U g W).val.toSubgroup =
      V.val.toSubgroup.relIndex W.val.toSubgroup :=
  relIndex_conjugateOpenSubgroup V.val W.val g

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K} {ρ : RationalSpectralAction G P}
  (d : ρ.InvariantRationalDomain U) (g : G)

/-- At every original level, use the actual label-g rational translation. -/
def rationalConjugationIso (V : FiniteIndexLevel U) :
    rationalObject d V ≅
      rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V) :=
  translationIso V.val g ((ρ.invariantRestrictionFunctor V.property.1).obj d)

@[simp]
theorem rationalConjugationIso_hom_label (V : FiniteIndexLevel U) :
    (rationalConjugationIso d g V).hom.label = g := rfl

@[simp]
theorem rationalConjugationIso_inv_label (V : FiniteIndexLevel U) :
    (rationalConjugationIso d g V).inv.label = g⁻¹ := rfl

/-- Original subgroup arrows commute with the actual rational translations. -/
@[reassoc]
theorem rationalConjugationIso_naturality {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    rationalArrow d f ≫ (rationalConjugationIso d g W).hom =
      (rationalConjugationIso d g V).hom ≫
        rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
          ((conjugationEquivalence U g).functor.map f) := by
  apply Hom.ext
  simp

/-- A natural isomorphism of the original rational transport towers. -/
def rationalTowerConjugationIso :
    rationalTower d ≅ (conjugationEquivalence U g).functor ⋙
      rationalTower ((ρ.invariantConjugationEquivalence U g).functor.obj d) :=
  NatIso.ofComponents (rationalConjugationIso d g)
    (fun f => rationalConjugationIso_naturality d g f)

/-- The same original tower isomorphism on full-group continuous induced spectra. -/
def inducedSpectrumTowerConjugationIso :
    rationalTower d ⋙ inducedSpectrumFunctor ≅
      ((conjugationEquivalence U g).functor ⋙
        rationalTower ((ρ.invariantConjugationEquivalence U g).functor.obj d)) ⋙
          inducedSpectrumFunctor :=
  Functor.isoWhiskerRight (rationalTowerConjugationIso d g) inducedSpectrumFunctor

/-- Forgetting actions retains a natural isomorphism of the actual quotient spaces. -/
def inducedSpaceTowerConjugationIso :
    rationalTower d ⋙ inducedTopologicalSpaceFunctor ≅
      ((conjugationEquivalence U g).functor ⋙
        rationalTower ((ρ.invariantConjugationEquivalence U g).functor.obj d)) ⋙
          inducedTopologicalSpaceFunctor :=
  Functor.isoWhiskerRight (rationalTowerConjugationIso d g) inducedTopologicalSpaceFunctor

/-- At each level the original balanced quotients are actually homeomorphic. -/
def inducedConjugationHomeomorph (V : FiniteIndexLevel U) :
    (rationalObject d V).InducedSpectrum ≃ₜ
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)).InducedSpectrum :=
  TopCat.homeoOfIso (inducedTopologicalSpaceFunctor.mapIso (rationalConjugationIso d g V))

@[simp]
theorem inducedConjugationHomeomorph_apply (V : FiniteIndexLevel U)
    (z : (rationalObject d V).InducedSpectrum) :
    inducedConjugationHomeomorph d g V z =
      (rationalConjugationIso d g V).hom.inducedMap z := rfl

@[simp]
theorem inducedConjugationHomeomorph_symm_apply (V : FiniteIndexLevel U)
    (z : (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.obj V)).InducedSpectrum) :
    (inducedConjugationHomeomorph d g V).symm z =
      (rationalConjugationIso d g V).inv.inducedMap z := rfl

/-- The full original group action is preserved by each quotient homeomorphism. -/
@[simp]
theorem inducedConjugationHomeomorph_smul (V : FiniteIndexLevel U) (a : G)
    (z : (rationalObject d V).InducedSpectrum) :
    inducedConjugationHomeomorph d g V (a • z) =
      a • inducedConjugationHomeomorph d g V z :=
  Hom.inducedMap_smul (rationalConjugationIso d g V).hom a z

/-- The original inverse-label correction is visible on every quotient representative. -/
@[simp]
theorem inducedConjugationHomeomorph_mk (V : FiniteIndexLevel U) (a : G)
    (x : (rationalObject d V).LocalSpectrum) :
    inducedConjugationHomeomorph d g V ((rationalObject d V).inducedMk a x) =
      (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.obj V)).inducedMk
          (a * g⁻¹) ((rationalConjugationIso d g V).hom.localSpectrumMap x) :=
  Hom.inducedMap_mk (rationalConjugationIso d g V).hom a x

/-- The actual homeomorphism lies over the identity of the ambient spectrum. -/
@[simp]
theorem ambientMap_inducedConjugationHomeomorph (V : FiniteIndexLevel U)
    (z : (rationalObject d V).InducedSpectrum) :
    (rationalObject ((ρ.invariantConjugationEquivalence U g).functor.obj d)
      ((conjugationEquivalence U g).functor.obj V)).ambientMap
        (inducedConjugationHomeomorph d g V z) =
      (rationalObject d V).ambientMap z :=
  Hom.ambientMap_inducedMap (rationalConjugationIso d g V).hom z

/-- The square uses the original subgroup quotient maps on both sides. -/
theorem inducedConjugationHomeomorph_naturality {V W : FiniteIndexLevel U}
    (f : V ⟶ W) (z : (rationalObject d V).InducedSpectrum) :
    inducedConjugationHomeomorph d g W ((rationalArrow d f).inducedMap z) =
      (rationalArrow ((ρ.invariantConjugationEquivalence U g).functor.obj d)
        ((conjugationEquivalence U g).functor.map f)).inducedMap
          (inducedConjugationHomeomorph d g V z) := by
  have h := congrArg (fun a => a.inducedMap z) (rationalConjugationIso_naturality d g f)
  simpa only [Hom.inducedMap_comp, inducedConjugationHomeomorph_apply] using h

/-- Properness is derived from the actual homeomorphism, without local stability. -/
theorem isProperMap_rationalConjugationIso_hom (V : FiniteIndexLevel U) :
    IsProperMap (rationalConjugationIso d g V).hom.inducedMap :=
  (inducedConjugationHomeomorph d g V).isProperMap

theorem isProperMap_rationalConjugationIso_inv (V : FiniteIndexLevel U) :
    IsProperMap (rationalConjugationIso d g V).inv.inducedMap :=
  (inducedConjugationHomeomorph d g V).symm.isProperMap

end OpenSubgroupTransport.FiniteIndexLevel

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
