/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.AlgebraicGeometry.Regular.RegularClosedImmersionCodimension
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionAffineCoordinates
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.RegularIdealConormalCoordinates
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover

/-!
# Centred affine coordinates for a smooth section

Source: blueprint main-20261015, lemma-section-normal-bundle, Local construction; Stacks Tags 054L,
024T, 067U, 00LN and 0633 (blueprint: lem-trf-smooth-section-centred-coordinates).

The chart witness packages the affine neighbourhoods, the actual etale map and its
coordinate functions. Its conormal frame and monomial formulas use the published
conormal algebra and symmetric comparison, including their restriction maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SmoothSectionCentredCoordinates

/-- One centred affine chart, with the algebra and monomial conclusions, for the section.
Here `T` and `U` are affine opens of the original schemes. The containment `mapsInto`
identifies `U` with an open in the base change to `T`, and `sectionPreimage` says that
its intersection with the section is exactly `T`. The Cartesian zero square specifies
the scheme-theoretic zero fibre. The coordinate ring map is polynomial evaluation in
the actual pullbacks of the standard affine-space coordinates.

The conormal basis lives on `s ⁻¹ᵁ U`, which is the very same open as `T`. Products of its
images under the symmetric-algebra inclusion are sent by the canonical comparison to
the classes of the coordinate monomials. Those classes are sections of the fixed
degree pieces, so the formulas commute with restrictions, including on overlaps.
Source: lemma-section-normal-bundle, Local construction; Stacks Tags 054L, 024T, 00LN, 0631--0633
(blueprint: lem-trf-smooth-section-centred-coordinates). -/
structure Chart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] where
  T : S.affineOpens
  U : V.affineOpens
  mapsInto : U.1 ≤ g ⁻¹ᵁ T.1
  openInBaseChange : IsOpenImmersion
    (pullback.lift U.1.ι (g.resLE T.1 U.1 mapsInto) (g.resLE_comp_ι mapsInto).symm)
  sectionInto : T.1 ≤ s ⁻¹ᵁ U.1
  sectionPreimage : s ⁻¹ᵁ U.1 = T.1
  e : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) T.1.toScheme
  over : e ≫ (AffineSpace (ULift.{u} (Fin d)) T.1.toScheme ↘ T.1.toScheme) =
    g.resLE T.1 U.1 mapsInto
  etale : Etale e
  separated : IsSeparated e
  zeroFiber : IsPullback (s.resLE U.1 T.1 sectionInto) (𝟙 T.1.toScheme) e
    (AffineSpace.homOfVector (𝟙 T.1.toScheme) (fun _ ↦ 0))
  x : Fin d → Γ(V, U.1)
  coordinates : ∀ j : Fin d,
    x j = U.1.topIso.hom (e.appTop (AffineSpace.coord T.1.toScheme (ULift.up j)))
  algebraEtale : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Etale
  algebraFlat : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Flat
  sectionIdeal : Ideal.map (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x)
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) Γ(S, T.1)))) =
      s.ker.ideal U
  quotient : Γ(V, U.1) ⧸ s.ker.ideal U ≃+* Γ(S, T.1)
  augmentation : ∀ b : Γ(V, U.1),
    quotient (Ideal.Quotient.mk (s.ker.ideal U) b) = s.appLE U.1 T.1 sectionInto b
  regular : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x)
  coordinateLift : Fin d → (ConormalGradedAlgebra.power s 1).val.obj (op U.1)
  coordinateLift_value : ∀ j : Fin d,
    (ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) (coordinateLift j) = x j
  conormalBasis : Module.Basis (Fin d) Γ(S, s ⁻¹ᵁ U.1)
    ((ConormalGradedAlgebra.piece s 1).val.obj (op (s ⁻¹ᵁ U.1)))
  conormalBasis_value : ∀ j : Fin d,
    conormalBasis j = ConormalGradedAlgebra.representative s 1 U.1 (coordinateLift j)
  monomials : ∀ α : Fin d →₀ ℕ,
    ∃ a : (ConormalGradedAlgebra.power s α.degree).val.obj (op U.1),
      (ConormalGradedAlgebra.powerInclusion s α.degree).val.app (op U.1) a =
          α.prod (fun j k ↦ x j ^ k) ∧
      (ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op (s ⁻¹ᵁ U.1))
          (α.prod (fun j k ↦
            (@id ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece s 1)).right.obj.obj
              (op (s ⁻¹ᵁ U.1)))
              ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece s 1)).val.app
                (op (s ⁻¹ᵁ U.1)) (conormalBasis j))) ^ k)) =
        ConormalGradedAlgebra.homogeneousClass s
          (ConormalGradedAlgebra.presentation s).algebra
          (ConormalGradedAlgebra.presentation s).inclusion α.degree U.1 a

set_option backward.isDefEq.respectTransparency false in
private def comparisonModuleMap {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (f : A ⟶ B) : A.toModule ⟶ B.toModule where
  val :=
    { app U := ModuleCat.ofHom (X := A.toModule.val.obj U)
        (Y := B.toModule.val.obj U)
        { toFun := f.right.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change A.right.obj.obj U at x
            change f.right.hom.app U (A.hom.hom.app U r * x) =
              B.hom.hom.app U r * f.right.hom.app U x
            rw [map_mul]
            congr 1
            exact congrArg (fun k ↦ k.hom.app U r) f.w }
      naturality {U V} k := by
        ext x
        exact congrArg (fun q ↦ q x) (f.right.hom.naturality k) }

set_option backward.isDefEq.respectTransparency false in
private theorem algebra_isIso_of_module {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (f : A ⟶ B) [IsIso (comparisonModuleMap f)] : IsIso f := by
  have : IsIso (comparisonModuleMap f).val := by
    change IsIso ((SheafOfModules.forget S.ringCatSheaf).map (comparisonModuleMap f))
    infer_instance
  have (U : S.Opensᵒᵖ) : IsIso (f.right.hom.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have : IsIso ((comparisonModuleMap f).val.app U) := by
      change IsIso ((PresheafOfModules.evaluation _ U).map (comparisonModuleMap f).val)
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ((comparisonModuleMap f).val.app U)
  have : IsIso f.right.hom := NatIso.isIso_of_isIso_app _
  have : IsIso f.right := by
    refine ⟨⟨ObjectProperty.homMk (inv f.right.hom), ?_, ?_⟩⟩
    · apply Sheaf.hom_ext
      exact IsIso.hom_inv_id f.right.hom
    · apply Sheaf.hom_ext
      exact IsIso.inv_hom_id f.right.hom
  have : IsIso ((Under.forget _).map f) := ‹IsIso f.right›
  exact isIso_of_reflects_iso f (Under.forget _)

set_option backward.isDefEq.respectTransparency false in
/-- A smooth separated finite-type map with a closed section has a Zariski affine cover
with centred separated etale coordinates, regular coordinate sequence and the specified
conormal monomial description. The section is regular of codimension `d`, its conormal
module is locally free of rank `d`, and its canonical symmetric comparison is invertible.
Source: lemma-section-normal-bundle, Local construction; Stacks Tags 054L, 024T, 067U, 00LN and 0633
(blueprint: lem-trf-smooth-section-centred-coordinates).

Proof: Choose a centred affine chart at every base point by
`exists_affineChart`. Apply `regular_ideal_conormal_coordinates` to its regular
coordinate ideal to obtain the actual conormal basis, monomial representatives,
a free frame and bijectivity of the canonical symmetric comparison on that
affine inverse image. Assemble these into `Chart`. The base-point indexing gives
the cover, and the same local equations give the regular immersion. The free
frames show finite local freeness of rank d. Both algebra sheaves are
quasi-coherent; the affine-cover criterion makes the comparison an isomorphism
of modules. A morphism of algebra sheaves whose underlying module morphism is
invertible is itself invertible. All formulas concern the single canonical
comparison, so compatibility with restriction is automatic. The point indexing
is empty when the base is empty, and the arguments also include d = 0. -/
theorem exists_centred_coordinates {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    (∃ (A : Type u) (c : A → Chart d g s), ⨆ a, (c a).T.1 = ⊤) ∧
      IsRegularClosedImmersionWithCodimension s (fun _ ↦ d) ∧
      (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison s) := by
  classical
  choose c hc using fun t : S ↦ exists_affineChart d g s hs t
  have hI (t : S) : Ideal.span (Set.range (c t).x) = s.ker.ideal (c t).U := by
    have h := (c t).sectionIdeal
    rw [Ideal.map_span, ← Set.range_comp] at h
    simpa only [Function.comp_def, MvPolynomial.eval₂Hom_X'] using h
  choose l b hl hb hm hf hbij using fun t : S ↦
    ConormalGradedAlgebra.regular_ideal_conormal_coordinates s (c t).U d (c t).x
      (hI t) (c t).regular
  let charts (t : S) : Chart d g s :=
    { T := (c t).T
      U := (c t).U
      mapsInto := (c t).mapsInto
      openInBaseChange := (c t).openInBaseChange
      sectionInto := (c t).sectionInto
      sectionPreimage := (c t).sectionPreimage
      e := (c t).e
      over := (c t).over
      etale := (c t).etale
      separated := (c t).separated
      zeroFiber := (c t).zeroFiber
      x := (c t).x
      coordinates := (c t).coordinates
      algebraEtale := (c t).algebraEtale
      algebraFlat := (c t).algebraFlat
      sectionIdeal := (c t).sectionIdeal
      quotient := (c t).quotient
      augmentation := (c t).augmentation
      regular := (c t).regular
      coordinateLift := l t
      coordinateLift_value := hl t
      conormalBasis := b t
      conormalBasis_value := hb t
      monomials := hm t }
  have hcover : ⨆ t : S, (c t).T.1 = ⊤ := by
    apply eq_top_iff.mpr
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hc t⟩
  have hprecover : ⨆ t : S, s ⁻¹ᵁ (c t).U.1 = ⊤ := by
    simpa only [(c _).sectionPreimage] using hcover
  have hregular : IsRegularClosedImmersionWithCodimension s (fun _ ↦ d) := by
    refine ⟨inferInstance, fun t ↦ ⟨(c t).U, ?_, List.ofFn (c t).x, ?_,
      (c t).regular, ?_⟩⟩
    · exact (c t).sectionInto (hc t)
    · exact List.length_ofFn
    · have hset : {r | r ∈ List.ofFn (c t).x} = Set.range (c t).x := by
        ext r
        simp
      simpa only [Ideal.ofList, hset, Scheme.Hom.ker_apply] using hI t
  have hfree : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d := by
    apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free _
      (fun t : S ↦ (s ⁻¹ᵁ (c t).U.1).ι)
    · simpa only [Scheme.Opens.opensRange_ι] using hprecover
    · intro t
      exact ⟨Scheme.Modules.overIsoFreeEquiv _ _ _ (hf t).some⟩
  have hqc : (ConormalGradedAlgebra.piece s 1).IsQuasicoherent :=
    (ConormalGradedAlgebra.presentation s).pieceQuasicoherent 1
  have hsrc := (quasiCoherentSymmetricAlgebra_affine_comparison S
    (ConormalGradedAlgebra.piece s 1)).1
  have hdst := (ConormalGradedAlgebra.presentation s).quasicoherent
  have hiso : IsIso (comparisonModuleMap (ConormalGradedAlgebra.symmetricComparison s)) := by
    apply Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover _
      (fun t : S ↦ s ⁻¹ᵁ (c t).U.1) hprecover
      (fun t ↦ (c t).U.2.preimage s)
    intro t
    exact hbij t
  exact ⟨⟨S, charts, hcover⟩, hregular, hfree,
    algebra_isIso_of_module (ConormalGradedAlgebra.symmetricComparison s)⟩

end AlgebraicGeometry.SmoothSectionCentredCoordinates
