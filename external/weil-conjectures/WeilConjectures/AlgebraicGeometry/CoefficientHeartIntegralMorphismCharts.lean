/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteHomLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Basic

/-! # Integral charts for the coefficient-heart argument -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- An integral lattice of a pullback of a continuous `E`-module pulls back to an integral
lattice of the further pullback along any morphism of schemes.
(auxiliary; not a blueprint node) -/
theorem exists_integral_lattice_upperStar_comp {X U W : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X) (r : W ⟶ U)
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hP : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) P)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj P ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj M) :
    ∃ P' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) W),
      IsLocallyFree (condensedRingObj (integralCoeff ℓ E) W) P' ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) W)).obj P' ≅
        (upperStar (Profinite.continuousMapRingObj E) (r ≫ p)).obj M) :=
  ⟨(upperStar (integralCoeff ℓ E) r).obj P, IsLocallyFree.upperStar _ r hP,
    ⟨(pullIso (integralScalarMap ℓ E) r).app P ≪≫
      (upperStar (Profinite.continuousMapRingObj E) r).mapIso e ≪≫
      ((upperStarComp (Profinite.continuousMapRingObj E) r p).app M).symm⟩⟩

/-- Two locally free continuous `E`-modules on a locally Noetherian scheme admit integral
lattices on a common connected affine etale neighbourhood of any given point.
(auxiliary; not a blueprint node)

Proof in words. Take an affine etale neighbourhood carrying a lattice of `M`, and over it an
affine etale neighbourhood of a point above `x` carrying a lattice of the pullback of `N`.
This scheme is affine and etale over a locally Noetherian scheme, hence Noetherian, so the
connected component of a point above `x` is open; it is also closed, so it is affine. Pull
back both lattices to this component. -/
theorem exists_connected_affine_etale_lattices [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    [IsLocallyNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) M)
    (hN : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) N) (x : X) :
    ∃ (V : Scheme.{u}) (q : V ⟶ X), Etale q ∧ x ∈ Set.range q ∧ IsAffine V ∧
      IsLocallyNoetherian V ∧ ConnectedSpace V ∧
      ∃ P Q : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) V),
        IsLocallyFree (condensedRingObj (integralCoeff ℓ E) V) P ∧
        IsLocallyFree (condensedRingObj (integralCoeff ℓ E) V) Q ∧
        Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj P ≅
          (upperStar (Profinite.continuousMapRingObj E) q).obj M) ∧
        Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj Q ≅
          (upperStar (Profinite.continuousMapRingObj E) q).obj N) := by
  obtain ⟨U₁, p₁, hU₁, hp₁, ⟨y₁, hy₁⟩, P₁, hP₁, ⟨e₁⟩⟩ :=
    continuousLisse_affine_etale_lattice ℓ E X M hM x
  obtain ⟨U₂, p₂, hU₂, hp₂, ⟨y₂, hy₂⟩, Q₂, hQ₂, ⟨e₂⟩⟩ :=
    continuousLisse_affine_etale_lattice ℓ E U₁
      ((upperStar (Profinite.continuousMapRingObj E) p₁).obj N)
      (IsLocallyFree.upperStar _ p₁ hN) y₁
  have : IsLocallyNoetherian U₁ := LocallyOfFiniteType.isLocallyNoetherian p₁
  have : IsLocallyNoetherian U₂ := LocallyOfFiniteType.isLocallyNoetherian p₂
  have : IsNoetherian U₂ := ⟨⟩
  let C : U₂.Opens :=
    ⟨connectedComponent y₂, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent y₂⟩
  have : IsAffineHom C.ι := isAffineHom_of_isInducing _ C.ι.isOpenEmbedding.isInducing
    (by simpa [C] using isClosed_connectedComponent)
  have hP := exists_integral_lattice_upperStar_comp ℓ E M p₁ (C.ι ≫ p₂) P₁ hP₁ e₁
  have hQ := exists_integral_lattice_upperStar_comp ℓ E N (p₂ ≫ p₁) C.ι Q₂ hQ₂
    (e₂ ≪≫ ((upperStarComp (Profinite.continuousMapRingObj E) p₂ p₁).app N).symm)
  rw [Category.assoc] at hP
  obtain ⟨P, hP, eP⟩ := hP
  obtain ⟨Q, hQ, eQ⟩ := hQ
  refine ⟨C, C.ι ≫ p₂ ≫ p₁, inferInstance, ⟨⟨y₂, mem_connectedComponent⟩, ?_⟩,
    isAffine_of_isAffineHom C.ι, inferInstance,
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent, P, Q, hP, hQ, eP, eQ⟩
  exact (congrArg p₁ hy₂).trans hy₁

/-- On a quasi-compact quasi-separated scheme, every morphism between the rationalizations of
two integral modules, the source being locally free, becomes the rationalization of an
integral morphism after multiplication by a power of `ℓ`.
(auxiliary; not a blueprint node)

Proof in words. The restricted scalar extension of the target is the colimit of its
multiplication-by-`ℓ` telescope, whose `k`-th leg is the extension unit followed by `ℓ⁻ᵏ`.
Transpose the morphism by the extension-restriction adjunction and factor it through a finite
stage of the telescope. Transposing back gives an integral morphism whose rationalization is
the given morphism followed by `ℓ⁻ᵏ`. -/
theorem exists_extendScalars_map_eq_pow_nsmul {V : Scheme.{u}} [CompactSpace V]
    [QuasiSeparatedSpace V]
    (P Q : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) V))
    (hP : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) V) P)
    (ψ : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj P ⟶
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj Q) :
    ∃ (k : ℕ) (g : P ⟶ Q),
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).map g = ℓ ^ k • ψ := by
  let φ := coefficientMap (integralScalarMap ℓ E) V
  let adj := Mod.extendRestrictAdjunction φ
  have := module_nsmul_isIso ℓ E V ((Mod.extendScalars φ).obj Q)
  let e := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence
  have : IsFiltered (ULift.{u + 1} ℕ) := IsFiltered.of_equivalence e.symm
  obtain ⟨hc⟩ := integralModuleLocalization_isColimit ℓ E V Q
  obtain ⟨⟨k⟩, b, hb⟩ :=
    hP.exists_comp_eq_of_isColimit _ (hc.whiskerEquivalence e) (adj.homEquiv _ _ ψ)
  refine ⟨k, b, ?_⟩
  let t : End ((Mod.extendScalars φ).obj Q) := .of (inv (ℓ • 𝟙 ((Mod.extendScalars φ).obj Q)))
  have h : (Mod.extendScalars φ).map b ≫ (t ^ k).asHom = ψ := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, ← hb, adj.homEquiv_unit]
    rfl
  rw [← h, ← Preadditive.comp_nsmul]
  exact Preadditive.eq_pow_nsmul_comp_pow ℓ t (IsIso.hom_inv_id _) k _

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- Absorb a cleared common denominator into the source rationalization
isomorphism. The integral map then represents the original rational map exactly. -/
private theorem heartAbsorbDenominator
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    (T : C ⥤ D) {P Q : C} {M N : D} (g : P ⟶ Q) (f : M ⟶ N)
    (eP : T.obj P ≅ M) (eQ : T.obj Q ≅ N) (n : ℕ) [IsIso (n • 𝟙 M)]
    (hs : T.map g ≫ eQ.hom = n • (eP.hom ≫ f)) :
    ∃ eP' : T.obj P ≅ M, T.map g ≫ eQ.hom = eP'.hom ≫ f := by
  refine ⟨eP ≪≫ asIso (n • 𝟙 M), ?_⟩
  simpa only [Iso.trans_hom, asIso_hom, Category.assoc, Preadditive.nsmul_comp,
    Category.id_comp, Preadditive.comp_nsmul] using hs

/-- On an affine scheme carrying integral lattices of two continuous `E`-modules, every
morphism between them is the rationalization of an integral morphism, after rescaling the
source rationalization isomorphism.
(auxiliary; not a blueprint node) -/
theorem CondensedRing.exists_integral_hom_of_lattices (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] {X V : Scheme.{u}} [IsAffine V]
    (q : V ⟶ X) {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)} (f : M ⟶ N)
    {P Q : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) V)}
    (hP : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) V) P)
    (eP : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj P ≅
      (upperStar (Profinite.continuousMapRingObj E) q).obj M)
    (eQ : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj Q ≅
      (upperStar (Profinite.continuousMapRingObj E) q).obj N) :
    ∃ (g : P ⟶ Q)
      (eP' : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).obj P ≅
        (upperStar (Profinite.continuousMapRingObj E) q).obj M),
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)).map g ≫ eQ.hom =
        eP'.hom ≫ (upperStar (Profinite.continuousMapRingObj E) q).map f := by
  obtain ⟨k, g, hg⟩ := CondensedRing.exists_extendScalars_map_eq_pow_nsmul ℓ E P Q hP
    (eP.hom ≫ (upperStar (Profinite.continuousMapRingObj E) q).map f ≫ eQ.inv)
  have := CondensedRing.module_nsmul_isIso ℓ E V
    ((upperStar (Profinite.continuousMapRingObj E) q).obj M)
  have := Preadditive.isIso_pow_nsmul_id ℓ
    (Y := (upperStar (Profinite.continuousMapRingObj E) q).obj M) k
  obtain ⟨eP', h⟩ := heartAbsorbDenominator _ g _ eP eQ (ℓ ^ k)
    (by rw [hg, Preadditive.nsmul_comp, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id])
  exact ⟨g, eP', h⟩

/-- A property of etale neighbourhoods which holds for some neighbourhood of every point
holds for all members of some pro-etale cover.
(auxiliary; not a blueprint node) -/
theorem _root_.AlgebraicGeometry.Scheme.exists_proetale_cover_of_forall_etale
    {X : Scheme.{u}}
    (p : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop)
    (h : ∀ x : X, ∃ (Z : Scheme.{u}) (g : Z ⟶ X), Etale g ∧ x ∈ Set.range g ∧ p Z g) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀, p (C.X i) (C.f i) := by
  choose Z g hg hx hp using h
  exact ⟨(Scheme.Cover.mkOfCovers X Z g (fun x ↦ ⟨x, hx x⟩) hg).weaken
    Scheme.etalePrecoverage_le_proetalePrecoverage, hp⟩

/-- The normed `ℚ_ℓ`-algebra structure of a finite subextension `E ⊆ ℚ̄_ℓ`, for the norm
`PadicAlgCl.normedFieldOfAlgebra` restricted from `ℚ̄_ℓ`. -/
abbrev normedAlgebraOfFiniteIntermediateField (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    NormedAlgebra ℚ_[ℓ] E.1 :=
  NormedAlgebra.induced ℚ_[ℓ] E.1 (PadicAlgCl ℓ) (IsScalarTower.toAlgHom ℚ_[ℓ] E.1 (PadicAlgCl ℓ))

/-- Integral charts of a morphism of lisse continuous `E`-modules on a locally Noetherian
scheme: a pro-etale cover by connected affine Noetherian schemes, on each of which the
pullback of the morphism is the rationalization of a morphism of lisse integral modules.
The pullback functors are passed as a family `U` equal to `upperStar`, so that the statement
can be specialized along definitionally equal coefficient rings without unfolding them.
(auxiliary; not a blueprint node)

Proof in words: at each point take a connected affine etale neighbourhood carrying lattices
of both modules (`CondensedRing.exists_connected_affine_etale_lattices`); these form a
pro-etale cover. On each such qcqs neighbourhood, the pullback of `f` becomes integral after
multiplication by a power `ℓᵏ` (`CondensedRing.exists_extendScalars_map_eq_pow_nsmul`), and
`ℓᵏ` is invertible on `E`-modules, so it is absorbed into the source isomorphism. -/
theorem CondensedRing.exists_lisse_integral_morphism_charts (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) (f : M ⟶ N)
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) N)
    (U : ∀ {V : Scheme.{u}}, (V ⟶ X) →
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) V))
    (hU : ∀ {V : Scheme.{u}} (q : V ⟶ X),
      U q = upperStar (Profinite.continuousMapRingObj E) q) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      IsAffine (C.X i) ∧ IsLocallyNoetherian (C.X i) ∧ ConnectedSpace (C.X i) ∧
      ∃ (P Q : Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) (C.X i))) (g : P ⟶ Q),
        IsLisseCoefficientModule (integralCoeff ℓ E) P ∧
        IsLisseCoefficientModule (integralCoeff ℓ E) Q ∧
        let T := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (C.X i))
        ∃ (eP : T.obj P ≅ (U (C.f i)).obj M) (eQ : T.obj Q ≅ (U (C.f i)).obj N),
          T.map g ≫ eQ.hom = eP.hom ≫ (U (C.f i)).map f := by
  refine Scheme.exists_proetale_cover_of_forall_etale (fun V q ↦
    IsAffine V ∧ IsLocallyNoetherian V ∧ ConnectedSpace V ∧
      ∃ (P Q : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) V)) (g : P ⟶ Q),
        IsLisseCoefficientModule (integralCoeff ℓ E) P ∧
        IsLisseCoefficientModule (integralCoeff ℓ E) Q ∧
        let T := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) V)
        ∃ (eP : T.obj P ≅ (U q).obj M) (eQ : T.obj Q ≅ (U q).obj N),
          T.map g ≫ eQ.hom = eP.hom ≫ (U q).map f)
    fun x ↦ ?_
  obtain ⟨V, q, hq, hx, hV, hVn, hVc, P, Q, hP, hQ, ⟨eP⟩, ⟨eQ⟩⟩ :=
    CondensedRing.exists_connected_affine_etale_lattices ℓ E X M N
      ((isLocallyFree_iff M).2 hM) ((isLocallyFree_iff N).2 hN) x
  obtain ⟨g, eP', h⟩ := CondensedRing.exists_integral_hom_of_lattices ℓ E q f hP eP eQ
  refine ⟨V, q, hq, hx, ?_⟩
  rw [hU]
  exact ⟨hV, hVn, hVc, P, Q, g, (isLocallyFree_iff _).1 hP, (isLocallyFree_iff _).1 hQ, eP',
    eQ, h⟩

/-- A rational lisse morphism has compatible integral models on connected affine
etale neighbourhoods. The source lattice may be rescaled to absorb its denominator.

Source: latest blueprint,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`, proof (1),
"First let Lambda = E", through the construction of h = pi^m f.
This is a step of the proof of `lemma-constructible-sheaves`
(auxiliary; not a blueprint node).

Proof in words: at each point of `X`, take a connected affine etale neighbourhood, which is
Noetherian, carrying integral lattices of both `M` and `N`
(`CondensedRing.exists_connected_affine_etale_lattices`); these neighbourhoods form a
pro-etale cover. The integral coefficients with the norm restricted from `ℚ̄_ℓ` are the
condensed integers of `E`. The rational target is the colimit of the multiplication-by-`ℓ`
telescope of its lattice, so on the qcqs neighbourhood the pullback of `f` becomes integral
after multiplication by a power `ℓᵏ` (`CondensedRing.exists_extendScalars_map_eq_pow_nsmul`).
Since `ℓ` is invertible on `E`-modules, rescaling the source rationalization isomorphism by
`ℓᵏ` gives the stated commuting square. Rank zero and the empty scheme are allowed. -/
theorem coefficientHeart_integralMorphismCharts (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) (f : M ⟶ N)
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) N) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      IsAffine (C.X i) ∧ IsLocallyNoetherian (C.X i) ∧ ConnectedSpace (C.X i) ∧
      ∃ (P Q : Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (C.X i))) (g : P ⟶ Q),
        IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) P ∧
        IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) Q ∧
        let T := Mod.extendScalars
          (padicIntegersToPadicSubfield (C.X i) ℓ E)
        ∃ (eP : T.obj P ≅ (CondensedRing.upperStar
            (Profinite.continuousMapRingObj E.1) (C.f i)).obj M)
          (eQ : T.obj Q ≅ (CondensedRing.upperStar
            (Profinite.continuousMapRingObj E.1) (C.f i)).obj N),
          T.map g ≫ eQ.hom = eP.hom ≫
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) (C.f i)).map f :=
  @CondensedRing.exists_lisse_integral_morphism_charts ℓ _ E.1
    (PadicAlgCl.normedFieldOfAlgebra ℓ E.1) (normedAlgebraOfFiniteIntermediateField ℓ E) E.2
    X _ M N f hM hN (fun q ↦ CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) q)
    fun _ ↦ rfl

end AlgebraicGeometry.ProEtale
