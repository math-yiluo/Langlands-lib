import Langlands.Representation.Geometric.RepresentedGeometricLemmaRadicalLift
import Langlands.Representation.Geometric.RepresentedGeometricLemmaSourceJacquet
import Langlands.Representation.Plancherel.UnramifiedJacquetScalarExtension

/-! Native coefficient quotients of the actual normalized orbit stabilizer. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u uR uV uW

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance coefficientStabilizerPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {n : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hn : LeviSubgroup.IsGeometricUnipotentRadical n}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l n)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {z : rationalPoints G}
  {B : Type uR} [CommRing B] [Algebra ℂ B]
  {V : Type uV} [AddCommGroup V] [Module B V]
  {W : Type uW} [AddCommGroup W] [Module B W]

/-- Constant extension of the original actual Levi inducing half-character. -/
def coefficientLeviInducingHalfCharacter :
    letI := leviPointTopology l hl
    rationalPoints M →* Bˣ := by
  letI := leviPointTopology l hl
  exact (Units.map (algebraMap ℂ B).toMonoidHom).comp
    (leviInducingHalfCharacter p l n hp hn hl).toMonoidHom

/-- Native full-parabolic induction covariance, with the original positive
half-modulus extended as constants to the coefficient algebra. -/
def coefficientInducingRepresentation (σ : Representation B (rationalPoints M) V) :
    Representation B (pointImage p) V := by
  let := leviPointTopology l hl
  let d := isSemidirectDecomposition_pointImage p l n hp.isClosedSubgroup hn hmul
  let hc := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  exact Langlands.twist
    ((Units.map (algebraMap ℂ B).toMonoidHom).comp
      (HaarModulus.closedHalfCharacter (pointImage (n ≫ p)) hc
        (pointImage p) d.le_normalizer))
    (σ.comp (parabolicToLeviPoints p l n hp hn hl hmul))

/-- The native coefficient on the literal full orbit stabilizer, expressed
through the original source Levi projection and its original half-character. -/
def coefficientStabilizerRepresentation
    (σ : Representation B (rationalPoints M) V) :
    Representation B
      (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹) V := by
  letI := leviPointTopology l hl
  exact (Langlands.twist
    (coefficientLeviInducingHalfCharacter (B := B) (p := p) (l := l) (n := n)
      (hp := hp) (hn := hn) (hl := hl)) σ).comp
    (stabilizerToLeviPoints p l n hp hn hl hmul q z)

/-- This coefficient is the restriction of the original full positively
normalized parabolic covariance, rather than an independently chosen twist. -/
theorem coefficientInducingRepresentation_comp_stabilizer
    (σ : Representation B (rationalPoints M) V) :
    (coefficientInducingRepresentation (p := p) (l := l) (n := n)
      (hp := hp) (hn := hn) (hl := hl) (hmul := hmul) σ).comp
        (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹) =
      coefficientStabilizerRepresentation (p := p) (l := l) (n := n)
        (hp := hp) (hn := hn) (hl := hl) (hmul := hmul) (q := q) (z := z) σ := by
  let := leviPointTopology l hl
  let d := isSemidirectDecomposition_pointImage p l n hp.isClosedSubgroup hn hmul
  let hc := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hδ := isUnimodularModulus_pointImage_radical p n hp.isClosedSubgroup hn.1
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  let y := Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹ x
  change
    ((Units.map (algebraMap ℂ B).toMonoidHom)
      (HaarModulus.closedHalfCharacter (pointImage (n ≫ p)) hc
        (pointImage p) d.le_normalizer y) : B) •
      σ ((leviPointsEquiv p l hp hl).symm (d.projection y)) v =
    ((Units.map (algebraMap ℂ B).toMonoidHom)
      (HaarModulus.closedHalfCharacter (pointImage (n ≫ p)) hc
        (pointImage (l ≫ p)) d.levi_le_normalizer
          ((leviPointsEquiv p l hp hl)
            ((leviPointsEquiv p l hp hl).symm (d.projection y)))) : B) •
      σ ((leviPointsEquiv p l hp hl).symm (d.projection y)) v
  rw [closedHalfCharacter_eq_comp_projection d hc hδ,
    MonoidHom.comp_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The stabilizer coefficient preserves the original coefficient map. -/
def coefficientStabilizerMap
    {σ : Representation B (rationalPoints M) V}
    {σ' : Representation B (rationalPoints M) W} (T : σ.IntertwiningMap σ') :
    (coefficientStabilizerRepresentation
      (p := p) (l := l) (n := n) (hp := hp) (hn := hn) (hl := hl)
      (hmul := hmul) (q := q) (z := z) σ).IntertwiningMap
      (coefficientStabilizerRepresentation
        (p := p) (l := l) (n := n) (hp := hp) (hn := hn) (hl := hl)
        (hmul := hmul) (q := q) (z := z) σ') := by
  letI := leviPointTopology l hl
  exact {
    toLinearMap := T.toLinearMap
    isIntertwining' x :=
      (Langlands.twistIntertwining
        (coefficientLeviInducingHalfCharacter (B := B) (p := p) (l := l)
          (n := n) (hp := hp) (hn := hn) (hl := hl)) T).isIntertwining'
        (stabilizerToLeviPoints p l n hp hn hl hmul q z x) }

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l n hp hn hl hmul
  q lQ nQ hq hnQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))
local notation "Rₛ" => pointImage (D.r' ≫ D.p')
local notation "τ" => coefficientStabilizerRepresentation
  (p := p) (l := l) (n := n) (hp := hp) (hn := hn) (hl := hl)
  (hmul := hmul) (q := q) (z := z)

/-- The native source-radical quotient surjects onto the actual stabilizer
kernel quotient by preserving every original vector class. -/
def sourceRadicalQuotientToCoefficientStabilizer
    (σ : Representation B (rationalPoints M) V) :
    Jacquet.Localization.Coinvariants σ Rₛ 1 →ₗ[B]
      Jacquet.Coinvariants (τ σ) NQH := by
  letI := leviPointTopology l hl
  refine Jacquet.Localization.lift σ Rₛ 1 (Jacquet.mk (τ σ) NQH) ?_
  intro m v
  have hχ : (leviInducingHalfCharacter p l n hp hn hl).toMonoidHom
      (m : rationalPoints M) = 1 :=
    D.sourceRadical_le_ker_inducingHalfCharacter m.property
  have haction : τ σ (D.sourceRadicalToStabilizer m) v =
      σ (m : rationalPoints M) v := by
    change
      ((Units.map (algebraMap ℂ B).toMonoidHom)
        ((leviInducingHalfCharacter p l n hp hn hl).toMonoidHom
          (stabilizerToLeviPoints p l n hp hn hl hmul q z
            (D.sourceRadicalToStabilizer m))) : B) •
        σ (stabilizerToLeviPoints p l n hp hn hl hmul q z
          (D.sourceRadicalToStabilizer m)) v = _
    rw [D.stabilizerToLeviPoints_sourceRadicalToStabilizer, hχ, map_one,
      Units.val_one, one_smul]
  have hrel := Jacquet.mk_apply_subgroup (τ σ) NQH
    ⟨D.sourceRadicalToStabilizer m, D.sourceRadicalToStabilizer_mem_kernel m⟩ v
  change Jacquet.mk (τ σ) NQH (τ σ (D.sourceRadicalToStabilizer m) v) =
    Jacquet.mk (τ σ) NQH v at hrel
  rw [haction] at hrel
  simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using hrel

@[simp]
theorem sourceRadicalQuotientToCoefficientStabilizer_mk
    (σ : Representation B (rationalPoints M) V) (v : V) :
    D.sourceRadicalQuotientToCoefficientStabilizer σ
        (Jacquet.Localization.mk σ Rₛ 1 v) = Jacquet.mk (τ σ) NQH v := rfl

theorem sourceRadicalQuotientToCoefficientStabilizer_surjective
    (σ : Representation B (rationalPoints M) V) :
    Function.Surjective (D.sourceRadicalQuotientToCoefficientStabilizer σ) := by
  intro x
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (τ σ) NQH x
  exact ⟨Jacquet.Localization.mk σ Rₛ 1 v, rfl⟩

/-- The quotient comparison commutes with every original coefficient-linear
intertwiner, on the same vector classes. -/
theorem sourceRadicalQuotientToCoefficientStabilizer_natural
    {σ : Representation B (rationalPoints M) V}
    {σ' : Representation B (rationalPoints M) W} (T : σ.IntertwiningMap σ')
    (x : Jacquet.Localization.Coinvariants σ Rₛ 1) :
    D.sourceRadicalQuotientToCoefficientStabilizer σ'
        (Jacquet.Localization.mapLinear Rₛ 1 T x) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap
          (coefficientStabilizerMap (p := p) (l := l) (n := n) (hp := hp)
            (hn := hn) (hl := hl) (hmul := hmul) (q := q) (z := z) T) NQH)
        (D.sourceRadicalQuotientToCoefficientStabilizer σ x) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective σ Rₛ 1 x
  rfl

/-- Source-radical vanishing already kills the full stabilizer's native
kernel quotient; no reverse image inclusion is required. -/
theorem coefficientStabilizerCoinvariants_subsingleton
    (σ : Representation B (rationalPoints M) V)
    [Subsingleton (Jacquet.Localization.Coinvariants σ Rₛ 1)] :
    Subsingleton (Jacquet.Coinvariants (τ σ) NQH) :=
  (D.sourceRadicalQuotientToCoefficientStabilizer_surjective σ).subsingleton

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Plancherel.RationalNormalized

open GroupScheme Aubert.General.RepresentedParabolic

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance universalStabilizerAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance universalStabilizerAmbientTopology : TopologicalSpace (rationalPoints G) :=
  AlgebraicGeometry.PointTopology.rationalPointTopology F G.X
local instance universalStabilizerFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : N ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication l n))
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance universalStabilizerTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

set_option maxHeartbeats 800000 in
/-- The coefficient covariance constructed through the Levi's own points is
the original actual universal full-parabolic inducing representation. -/
theorem universalInducingRepresentation_eq_coefficient
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    inducingRepresentation r h hU σ =
      coefficientInducingRepresentation (p := p) (l := l) (n := n)
        (hp := r.isCompatible.parabolic) (hn := hn) (hl := r.isCompatible.levi)
        (hmul := hmul) (B := RegularAlgebra r) (V := RegularAlgebra r ⊗[ℂ] E)
        ((universalRepresentation r σ).comp
          (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom) := by
  let := leviPointTopology l r.isCompatible.levi
  let e := leviPointsEquiv p l r.isCompatible.parabolic r.isCompatible.levi
  have he (m : rationalPoints M) :
      parabolicLeviPointHomeomorph r m = e m := by
    apply Subtype.ext
    rfl
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  change
    ((UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.le_normalizer).toMonoidHom x : RegularAlgebra r) •
        universalRepresentation r σ (h.projection x) v =
    ((UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.le_normalizer).toMonoidHom x : RegularAlgebra r) •
        universalRepresentation r σ
          (parabolicLeviPointHomeomorph r (e.symm (h.projection x))) v
  exact congrArg (fun m : parabolicLeviPointSubgroup p l =>
    ((UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.le_normalizer).toMonoidHom x : RegularAlgebra r) •
        universalRepresentation r σ m v)
    ((he (e.symm (h.projection x))).trans (e.apply_symm_apply (h.projection x))).symm

variable {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l n r.isCompatible.parabolic hn
    r.isCompatible.levi hmul q lQ nQ hq hnQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (Aubert.General.IsSemidirectDecomposition.projection dQ))

set_option maxHeartbeats 800000 in
/-- The actual universal orbit covariance is exactly the coefficient model
used in the native source-radical comparison. -/
theorem universalStabilizerRepresentation_eq_coefficient
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    (inducingRepresentation r h hU σ).comp
        (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹) =
      coefficientStabilizerRepresentation (p := p) (l := l) (n := n)
        (hp := r.isCompatible.parabolic) (hn := hn) (hl := r.isCompatible.levi)
        (hmul := hmul) (q := q) (z := z) (B := RegularAlgebra r)
        ((universalRepresentation r σ).comp
          (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom) :=
  (congrArg
    (fun ρ => ρ.comp (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹))
    (universalInducingRepresentation_eq_coefficient r hn hmul h hU σ)).trans
    (coefficientInducingRepresentation_comp_stabilizer _)

set_option maxHeartbeats 800000 in
/-- A proper source intersection kills the native kernel quotient of the
original full normalized universal stabilizer covariance. -/
theorem universalStabilizerCoinvariants_subsingleton
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsSupercuspidal r σ) (hproper : SubgroupFunctor.range D.p' ≠ ⊤) :
    Subsingleton (Jacquet.Coinvariants
      ((inducingRepresentation r h hU σ).comp
        (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹)) NQH) := by
  let : Subsingleton (Jacquet.Localization.Coinvariants
      ((universalRepresentation r σ).comp
        (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom)
      (pointImage (D.r' ≫ D.p')) 1) := by
    rw [pointImage_eq_range_carrier (D.r' ≫ D.p')]
    exact universalRepresentation_properJacquet_subsingleton r σ hσ D.hp' hproper D.hr'
  have hvanish := D.coefficientStabilizerCoinvariants_subsingleton
    ((universalRepresentation r σ).comp
      (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom)
  rw [universalStabilizerRepresentation_eq_coefficient r hn hmul h hU σ]
  exact hvanish

end Langlands.Plancherel.RationalNormalized
