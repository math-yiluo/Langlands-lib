/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.ReducedFlatAffinePreparation
import WeilConjectures.AlgebraicGeometry.RadicialReducedFlatGenericFibre
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Affine radicial preparation with a universal homeomorphism onto the original
base-changed family, before the final generic-flat shrinking.

Source: Stacks Project, Tag 0559, second proof, through its finite purely inseparable
extension construction; Tags 051T and 052A for the first generic-flat shrinking.
Proof: the geometrically irreducible generic fibre is nonempty, so its image puts
η in V. Factor f through V and reduce both affine schemes. A map from a reduced
scheme factors through the reduction of its target. The reduced base is integral
because η is generic. Both reduction maps are surjective closed immersions and
hence universal homeomorphisms. The reduced family is locally of finite type and
quasi-compact, since its source and target are affine. Apply generic flat finite
presentation and choose a principal open containing the generic point inside the
resulting open. This principal open can be lifted to a principal open U of V:
its defining element lifts from the reduced coordinate ring. Its inverse image
in the affine source is affine. Write the resulting base ring as A, its fraction
field as K, and the reduced flat source ring as B. Flatness makes B inject into
B tensor_A K. That generic ring is a domain, since it is reduced and irreducible.
Let L be its fraction field. The field argument in Tag 0559 gives a finite purely
inseparable K'/K for which the reduction of L tensor_K K' is a separably generated
field. In characteristic zero take K'=K. Choose field generators b_i of K'/K with
b_i^q_i=a_i/d_i in K, and replace them by d_i*b_i. Their q_i-th powers now lie in
A. The A-subalgebra A' they generate inside K' is a finite integral domain with
fraction field K', and Spec A' to Spec A is a universal homeomorphism: the integral
extension is surjective on spectra and purely inseparable on all residue fields.
Set S=Spec A' and compose this map with the base reduction map to obtain q to U.
Set Y to the reduction of X tensor_T S, and let h be its canonical reduction map.
Then h is a universal homeomorphism and g=h followed by the pullback projection.
Affineness, reducedness, and local finite type follow from this construction.
At the generic point of S, the coordinate ring of Y is the reduction of the
original generic ring tensored with K'. Reduction and localization commute.
This ring embeds in the reduction of L tensor_K K': before reduction the tensor
map is injective, and an element of a subring is nilpotent exactly when its image
is nilpotent. The latter reduced tensor ring is a separably generated field,
hence geometrically reduced. Tensoring this injection with any extension of K'
remains injective, proving geometric reducedness of the generic fibre of Y.
The homeomorphism q uniquely lifts η to the generic point of S. No second flat
shrinking is made. Empty special fibres cause no problem. Every scheme here has
an explicit spectrum, pullback, or reduction construction; no definition chooses
an arbitrary object from this unproved existence theorem.

(blueprint: lem-sbc-radicial-preparation-construction) -/
theorem exists_radicial_preparation_construction
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ LocallyOfFiniteType g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∃ h : Y ⟶ pullback f (q ≫ U.ι),
            IsUniversalHomeomorphism h ∧ h ≫ pullback.snd f (q ≫ U.ι) = g := by
  let : GeometricallyIrreducible (f.fiberToSpecResidueField η) := hgeom
  have hηV : η ∈ V := by
    let : Surjective (f.fiberToSpecResidueField η) := inferInstance
    have hn : Nonempty (f.fiber η) := by
      obtain ⟨x, _⟩ :=
        (f.fiberToSpecResidueField η).surjective (Classical.choice inferInstance)
      exact ⟨x⟩
    obtain ⟨x⟩ := hn
    have hx : f (f.fiberι η x) = η := by
      have hx := (f.range_fiberι η).le ⟨x, rfl⟩
      exact hx
    exact hx ▸ himage ⟨f.fiberι η x, rfl⟩
  obtain ⟨U, hηU, hU, S₀, Z, q₀, h₀, hS₀, hiS₀, hZ, hrZ, hq₀, hh₀,
    hflat, hfp, η₀, hη₀, heη₀⟩ :=
    exists_reduced_flat_affine_preparation f V hV himage η hη hηV
  have : IsAffine S₀ := hS₀
  have : IsIntegral S₀ := hiS₀
  have : IsAffine Z := hZ
  have : IsReduced Z := hrZ
  have : IsUniversalHomeomorphism q₀ := hq₀
  have : IsUniversalHomeomorphism h₀ := hh₀
  let r₀ := q₀ ≫ U.ι
  let g₀ := h₀ ≫ pullback.snd f r₀
  have : Flat g₀ := hflat
  have : LocallyOfFinitePresentation g₀ := hfp
  have hgeom₀ : GeometricallyIrreducible (g₀.fiberToSpecResidueField η₀) := by
    apply (exists_radicial_preparation_fibre_comparison f r₀ h₀ η₀).mpr
    rw [heη₀]
    exact hgeom
  obtain ⟨S, q₁, hS, hiS, hq₁, η', hη', heη', hred⟩ :=
    exists_radicial_reduced_flat_generic_fibre g₀ η₀ hη₀ hgeom₀
  have : IsAffine S := hS
  have : IsIntegral S := hiS
  have : IsUniversalHomeomorphism q₁ := hq₁
  let P := pullback g₀ q₁
  let Y := P.nilradical.subscheme
  let a : Y ⟶ P := P.nilradical.subschemeι
  have : IsReduced Y :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P).1
  have : Surjective a :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P).2.2.1
  have : IsUniversalHomeomorphism a := inferInstance
  have : IsAffine P := inferInstance
  have : IsAffine Y := isAffine_of_isAffineHom a
  let g := a ≫ pullback.snd g₀ q₁
  let q := q₁ ≫ q₀
  refine ⟨U, hηU, hU, S, Y, q, g, hS, hiS, inferInstance, inferInstance,
    inferInstance, inferInstance, η', hη', ?_, hred, ?_⟩
  · change U.ι (q₀ (q₁ η')) = η
    rw [heη']
    exact heη₀
  · let e₁ := pullbackRightPullbackFstIso (pullback.snd f r₀) q₁ h₀
    let e₂ := pullbackLeftPullbackSndIso f r₀ q₁
    let k := e₁.inv ≫ pullback.snd h₀ (pullback.fst (pullback.snd f r₀) q₁) ≫ e₂.hom
    have hk : IsUniversalHomeomorphism k := inferInstance
    have hk_snd : k ≫ pullback.snd f (q₁ ≫ r₀) = pullback.snd g₀ q₁ := by
      simp [k, e₁, e₂, g₀]
    have hh : ∃ h : Y ⟶ pullback f (q₁ ≫ r₀),
        IsUniversalHomeomorphism h ∧ h ≫ pullback.snd f (q₁ ≫ r₀) = g := by
      refine ⟨a ≫ k, inferInstance, ?_⟩
      rw [Category.assoc, hk_snd]
    refine ⟨hh.choose, hh.choose_spec.1, ?_⟩
    change hh.choose ≫ pullback.snd f (q₁ ≫ q₀ ≫ U.ι) = g
    simpa [r₀, Category.assoc] using hh.choose_spec.2

end AlgebraicGeometry
