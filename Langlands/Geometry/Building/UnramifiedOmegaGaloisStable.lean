import Langlands.Geometry.Building.IntegerOmegaGaloisStability
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Galois stability of centralizer-compatible apartment classes over an extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.IntegerValuation

section Comparison

variable {k : Type u} [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- Two representatives of the same actual torus centralizer give the same
integer-valued translation vector. -/
theorem centralizerTranslation_comparison (C E : CentralizerDatum i)
    (z : rationalPoints C.Z) :
    (centralizerTranslation v C.s C.bijective z).toAdd =
      (centralizerTranslation v E.s E.bijective
        (rationalPoints.map
          (C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy).hom z)).toAdd := by
  set e := C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy with he_def
  have he : e.hom ≫ E.j = C.j :=
    C.isRepresentedBy.isoOfIsRepresentedBy_hom_comp E.isRepresentedBy
  have hs : C.s ≫ e.hom = E.s := by
    apply E.isRepresentedBy.hom_ext
    rw [Category.assoc, he, C.comp_eq, E.comp_eq]
  apply E.bijective.injective
  apply AddMonoidHom.ext
  intro χ
  change eval S (Cartan.characterRestriction E.s χ)
      (centralizerTranslation v C.s C.bijective z).toAdd =
    eval S (Cartan.characterRestriction E.s χ)
      (centralizerTranslation v E.s E.bijective (rationalPoints.map e.hom z)).toAdd
  have hχ :
      Cartan.characterRestriction C.s (characterRestrict e.hom χ) =
        Cartan.characterRestriction E.s χ := by
    apply congrArg (rationalCharacters.equivCharacterLattice S)
    change Additive.ofMul (C.s ≫ (e.hom ≫ χ.toMul)) = Additive.ofMul (E.s ≫ χ.toMul)
    rw [← Category.assoc, hs]
  calc
    _ = eval S (Cartan.characterRestriction C.s (characterRestrict e.hom χ))
        (centralizerTranslation v C.s C.bijective z).toAdd := by rw [hχ]
    _ = -order v (rationalCharacterEval (characterRestrict e.hom χ) z) :=
      eval_centralizerTranslation v C.s C.bijective z _
    _ = -order v (rationalCharacterEval χ (rationalPoints.map e.hom z)) := by
      rw [rationalCharacterEval_characterRestrict]
    _ = _ := (eval_centralizerTranslation v E.s E.bijective _ χ).symm

variable [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Full integer-valued V6 is independent of the representative of the actual
centralizer. -/
theorem IsOmegaCompatible.of_centralizerDatum {D : KPApartmentData i (order v)}
    {C : CentralizerDatum i} (E : CentralizerDatum i) (hD : IsOmegaCompatible v D C) :
    IsOmegaCompatible v D E := by
  intro φ hφ a ha z u hu
  set e := C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy with he_def
  have hsurj : Function.Surjective (rationalPoints.map e.hom) := by
    intro z
    obtain ⟨w, hw⟩ := (isoPointsEquiv e (Over.mk (𝟙 _))).surjective z
    exact ⟨w, by simpa only [rationalPoints.map_apply, isoPointsEquiv_apply] using hw⟩
  obtain ⟨z, rfl⟩ := hsurj z
  have hmap : rationalPoints.map E.j (rationalPoints.map e.hom z) =
      rationalPoints.map C.j z := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : C.Z ⟶ G => z ≫ f.hom.hom)
        (C.isRepresentedBy.isoOfIsRepresentedBy_hom_comp E.isRepresentedBy)
  rw [hmap, ← centralizerTranslation_comparison v C E]
  exact hD φ hφ a ha z u hu

theorem isOmegaCompatible_iff_centralizerDatum {D : KPApartmentData i (order v)}
    (C E : CentralizerDatum i) :
    IsOmegaCompatible v D C ↔ IsOmegaCompatible v D E :=
  ⟨fun h => h.of_centralizerDatum v E, fun h => h.of_centralizerDatum v C⟩

end Comparison

section BaseChange

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (w : Valuation K (WithZero (Multiplicative ℤ)))

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance unramifiedOmegaExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

/-- **Galois stability from V6 for any centralizer datum.** Let `i : T → G` be a
homomorphism from an affine commutative `k`-group whose scalar extension to `K` is a maximal
`K`-split torus of the connected reductive group `G_K`, and let `w` be an integer-valued
valuation of `K` invariant under `Aut(K/k)`. Every class of valuations of the root datum of
`(G_K, T_K)` satisfying V6 for some centralizer datum of `T_K` is stable under the actual
coefficient action of `Aut(K/k)`. -/
theorem IsOmegaCompatible.galoisStable_of_centralizerDatum
    (hw : ∀ (σ : K ≃ₐ[k] K) (t : Kˣ), order w (Units.map σ.toMonoidHom t) = order w t)
    [IsAffineHom T.X.hom] (hG : IsConnectedReductive G_K)
    (hi : IsMaximalSplitTorus (T := T_K) i_K)
    (D : KPApartmentData (S := T_K) i_K (order w)) (C : CentralizerDatum (S := T_K) i_K)
    (hD : IsOmegaCompatible w D C) :
    KPApartmentData.GaloisStable k K i D := by
  obtain ⟨Z, j, hj, hjc⟩ := fieldCentralizerRepresentability k T G inferInstance i
  have hs : torusCentralizerFactor i hj ≫ j = i := torusCentralizerFactor_comp i hj
  have hcl : IsClosedSubgroup ((GroupScheme.baseChange b).map j) :=
    IsClosedSubgroup.baseChange b hjc
  have hrep : (torusCentralizer (T := T_K) i_K).IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact hj.baseChange b
  have hcomp : (GroupScheme.baseChange b).map (torusCentralizerFactor i hj) ≫
      (GroupScheme.baseChange b).map j = i_K := by
    rw [← Functor.map_comp, hs]
  have hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K)
      ((GroupScheme.baseChange b).map (torusCentralizerFactor i hj))) :=
    Cartan.restrictionEvaluation_bijective_of_torusCentralizer hG hi hcl hrep hcomp
  have hpair : RelativeRoot.HasOppositeFactorPairs (T := T_K) i_K := by
    have hsm : Smooth (G_K).X.hom := hG.smooth
    have hTs : IsSplitTorus (T_K).toGrp := hi.isSplitSubtorus.1
    have hr : RelativeRoot.HasRankOneFactorization (T := T_K) i_K :=
      rootRankOneFactorization K G_K hG T_K i_K hi
    exact (@RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs K _ T_K G_K
      inferInstance i_K inferInstance hsm hTs).mp hr
  let E : CentralizerDatum (S := T_K) i_K :=
    { Z := (GroupScheme.baseChange b).obj Z
      j := (GroupScheme.baseChange b).map j
      s := (GroupScheme.baseChange b).map (torusCentralizerFactor i hj)
      isClosedSubgroup := hcl
      isRepresentedBy := hrep
      comp_eq := hcomp
      bijective := hK }
  have hE : IsOmegaCompatible w D E := hD.of_centralizerDatum w E
  have h := IsOmegaCompatible.galoisStable k K i j (torusCentralizerFactor i hj) w hw D hcl
    hrep hcomp hK
  exact h hE hG hi hpair

end BaseChange

end Langlands.Geometry.Building.IntegerValuation

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

/-- The spectral valuation of the maximal unramified extension is invariant under
every `F`-automorphism. -/
theorem fixedFieldValuation_galois (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : inertiaFixedField F) :
    fixedFieldValuation F (σ x) = fixedFieldValuation F x := by
  rw [fixedFieldValuation_eq_spectralValuation]
  apply NNReal.eq
  change spectralNorm F (inertiaFixedField F) (σ x) = spectralNorm F (inertiaFixedField F) x
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- The normalized integer valuation of the maximal unramified extension is invariant
under every `F`-automorphism. -/
theorem valuation_galois (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : inertiaFixedField F) : valuation F (σ x) = valuation F x :=
  le_antisymm (((valuation_isEquiv F) (σ x) x).2 (fixedFieldValuation_galois F σ x).le)
    (((valuation_isEquiv F) x (σ x)).2 (fixedFieldValuation_galois F σ x).ge)

/-- The real order of the normalized integer valuation is invariant under every
`F`-automorphism. -/
theorem order_galois (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (t : (inertiaFixedField F)ˣ) :
    IntegerValuation.order (valuation F) (Units.map σ.toMonoidHom t) =
      IntegerValuation.order (valuation F) t := by
  unfold IntegerValuation.order
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd, Units.coe_map]
  exact congrArg (fun z => ((-WithZero.log z : ℤ) : ℝ)) (valuation_galois F σ t)

end Langlands.Geometry.Building.MaximalUnramified

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)

private instance unramifiedOmegaAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]

/-- **Galois stability of V6 classes over the maximal unramified extension.** Let `K` be
the maximal unramified extension of a nonarchimedean local field `F`, with its normalized
integer valuation, and let `iT : T → G` be a closed `F`-subgroup whose scalar extension
`T_K` is a maximal `K`-split torus of the connected reductive group `G_K`. Every class of
valuations of the root datum of `(G_K, T_K)` satisfying V6 for some centralizer datum of
`T_K` is stable under the coefficient action of `Aut(K/F)`. -/
theorem galoisStable_of_isOmegaCompatible (hiTc : IsClosedSubgroup iT)
    (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (valuation F)))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hD : IntegerValuation.IsOmegaCompatible (valuation F) D C) :
    KPApartmentData.GaloisStable F (inertiaFixedField F) iT D :=
  have : IsAffineHom T.X.hom := hiTc.isAffineHom
  IntegerValuation.IsOmegaCompatible.galoisStable_of_centralizerDatum F (inertiaFixedField F)
    iT (valuation F) (order_galois F) hGK hiT D C hD

end Langlands.Geometry.Building.MaximalUnramified
