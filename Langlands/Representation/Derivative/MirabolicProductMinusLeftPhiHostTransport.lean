import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Derivative.MirabolicProductRestrictionTransport

/-! Actual host rank transports for the left-Phi comparison. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction MixedProductTensor Geometric

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Equality transport agrees with actual pullback along the inverse matrix rank
cast, by the identity linear equivalence after equality elimination. -/
def mirabolicRankCastMixedOrbitIso {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ≅
      Mirabolic.continuousPullbackFunctor (rankCast (R := F.Carrier) h).symm.toMonoidHom
        (continuous_rankCast_symm h) := by
  letI := T.topology
  subst b
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso
    { toLinearEquiv := LinearEquiv.refl ℂ A
      isIntertwining' g := ?_ }) ?_
  · have hg : (rankCast (R := F.Carrier) (rfl : a = a)).symm g = g := by
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      rfl
    apply LinearMap.ext
    intro v
    change A.representation g v = A.representation ((rankCast rfl).symm g) v
    rw [hg]
  · intro A B f
    rfl

section HighRank

variable (k r : ℕ) (R : Type uF) [CommRing R] [TopologicalSpace R]

/-- The actual inverse rank cast from the ambient orbit group into the original
left mixed-product coordinates. -/
def leftPhiHighRankEquiv :
    mirabolic (k + r + 2) R ≃ₜ* mirabolic (k + 1 + (r + 1)) R where
  toMulEquiv := (rankCast (totalRank_eq k r)).symm
  continuous_toFun := continuous_rankCast_symm _
  continuous_invFun := continuous_rankCast _

theorem leftPhiHighRank_mem_iff (g : mirabolic (k + r + 2) R) :
    g ∈ leftInducing k r R ↔
      leftPhiHighRankEquiv k r R g ∈ leftSubgroup (k + 1) (r + 1) R :=
  Iff.rfl

end HighRank

variable (k r : ℕ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)

/-- The entire actual covariance-normalized higher inducing coefficient, in the
ambient coordinates of the mixed-orbit calculation. -/
def leftPhiHostInducingRepresentation :
    letI := T.topology
    Representation ℂ (leftInducing k r F.Carrier) (V ⊗[ℂ] W) :=
  letI := T.topology
  (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
    (leftInducingRepresentation ρ τ)).comp (leftInducingHom k r F.Carrier)

/-- Pullback and the open kernel of the actual covariance character preserve
smoothness of the full higher coefficient. -/
theorem leftPhiHostInducingRepresentation_smooth
    (hρ : letI := T.topology; IsSmooth ρ) (hτ : letI := T.topology; IsSmooth τ) :
    letI := T.topology
    IsSmooth (leftPhiHostInducingRepresentation T k r ρ τ) := by
  let := T.topology
  exact isSmooth_comp _ (continuous_leftInducingHom k r F.Carrier)
    ((isSmooth_twist_iff _ _ (T.leftCharacter (k + 1) (r + 1)).isOpen_ker).mpr
      (isSmooth_leftInducingRepresentation hρ hτ))

/-- Restriction of the actual inducing coefficient to either conjugated orbit
stabilizer is exactly the full published normalized stabilizer action. -/
theorem leftPhiHostInducingRepresentation_stabilizer (i : Fin 2) :
    letI := T.topology
    (leftPhiHostInducingRepresentation T k r ρ τ).comp
        (stabilizerToInducing (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier i)) =
      leftPhiNormalizedStabilizer T k r ρ τ i := rfl

/-- Transport of entire compactly induced function carriers to the ambient
mixed-orbit coordinates, retaining the complete covariance character. -/
def leftPhiHostCompactInducedEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
    Representation.Equiv
      ((compactInduced (leftSubgroup (k + 1) (r + 1) F.Carrier)
        (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
          (leftInducingRepresentation ρ τ))).comp
            (leftPhiHighRankEquiv k r F.Carrier).toMonoidHom)
      (compactInduced (leftInducing k r F.Carrier)
        (leftPhiHostInducingRepresentation T k r ρ τ)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  compactInducedTransport (leftPhiHighRankEquiv k r F.Carrier)
    (leftInducing k r F.Carrier) (leftSubgroup (k + 1) (r + 1) F.Carrier)
    (leftPhiHighRank_mem_iff k r F.Carrier)
    (leftPhiHostInducingRepresentation T k r ρ τ)
    (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
      (leftInducingRepresentation ρ τ))
    (LinearEquiv.refl ℂ _) (fun _ _ => rfl)

@[simp]
theorem leftPhiHostCompactInducedEquiv_eval
    (z : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
      CompactFunctions (leftSubgroup (k + 1) (r + 1) F.Carrier)
        (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
          (leftInducingRepresentation ρ τ)))
    (x : mirabolic (k + r + 2) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
    eval (leftInducing k r F.Carrier) (leftPhiHostInducingRepresentation T k r ρ τ)
        (leftPhiHostCompactInducedEquiv T k r ρ τ z).1 x =
      eval (leftSubgroup (k + 1) (r + 1) F.Carrier)
        (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
          (leftInducingRepresentation ρ τ)) z.1 (leftPhiHighRankEquiv k r F.Carrier x) := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {τ' : Representation ℂ (mirabolic (r + 1) F.Carrier) W'}

/-- The actual tensor map between the higher inducing coefficients. -/
def leftPhiHostInducingMap (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') :
    letI := T.topology
    (leftPhiHostInducingRepresentation T k r ρ τ).IntertwiningMap
      (leftPhiHostInducingRepresentation T k r ρ' τ') :=
  letI := T.topology
  pullbackMap (leftInducingHom k r F.Carrier)
    (twistIntertwining (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
      (pullbackMap leftProjection (externalMap f g)))

/-- Naturality on every compactly induced function, for both input maps across
four independent coefficient universes. -/
theorem leftPhiHostCompactInducedEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (z : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
      CompactFunctions (leftSubgroup (k + 1) (r + 1) F.Carrier)
        (twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
          (leftInducingRepresentation ρ τ))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
    leftPhiHostCompactInducedEquiv T k r ρ' τ'
        (compactInducedMap (leftSubgroup (k + 1) (r + 1) F.Carrier)
          (twistIntertwining (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
            (pullbackMap leftProjection (externalMap f g))) z) =
      compactInducedMap (leftInducing k r F.Carrier)
        (leftPhiHostInducingMap T k r ρ τ f g)
        (leftPhiHostCompactInducedEquiv T k r ρ τ z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

/-- The smooth higher inducing coefficient, naturally in both representation
inputs, with no choice of coefficient vectors or finite-dimensional model. -/
def leftPhiHostInducingFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, uV} ℂ (leftInducing k r F.Carrier) :=
  letI := T.topology
  { obj := fun X => SmoothRep.of
      (leftPhiHostInducingRepresentation T k r X.1.representation X.2.representation)
      (leftPhiHostInducingRepresentation_smooth T k r _ _ X.1.isSmooth X.2.isSmooth)
    map := fun f => SmoothRep.ofHom
      (leftPhiHostInducingMap T k r _ _ (SmoothRep.hom f.1) (SmoothRep.hom f.2))
    map_id := fun X => by
      apply smoothRep_hom_ext
      intro x
      change TensorProduct.map LinearMap.id LinearMap.id x = x
      rw [TensorProduct.map_id]
      rfl
    map_comp := fun f g => by
      apply smoothRep_hom_ext
      intro x
      exact LinearMap.congr_fun
        (congrArg Representation.IntertwiningMap.toLinearMap
          (externalMap_comp (SmoothRep.hom f.1) (SmoothRep.hom g.1)
            (SmoothRep.hom f.2) (SmoothRep.hom g.2))) x }

/-- The actual higher mixed product, with its target's equality transport, is
compact induction of the full smooth coefficient in ambient orbit coordinates. -/
def leftPhiHostInductionIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    T.leftMixedProductFunctor.{uF, uV} (k + 1) (r + 1) ⋙
        mirabolicRankCast T (totalRank_eq k r) ≅
      leftPhiHostInducingFunctor T k r ⋙ SmoothRep.toRep ⋙
        compactInductionFunctor (leftInducing k r F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  refine (Functor.isoWhiskerLeft (T.leftMixedProductFunctor (k + 1) (r + 1))
    (mirabolicRankCastMixedOrbitIso T (totalRank_eq k r))) ≪≫ ?_
  refine NatIso.ofComponents
    (fun X => SmoothRep.mkIso (leftPhiHostCompactInducedEquiv T k r
      X.1.representation X.2.representation)) ?_
  intro X Y f
  apply smoothRep_hom_ext
  intro z
  exact leftPhiHostCompactInducedEquiv_natural T k r _ _
    (SmoothRep.hom f.1) (SmoothRep.hom f.2) z

/-- The lower expected host functor in explicit inverse-rank-pullback
coordinates. Its coefficient is the actual normalized source Phi quotient. -/
def leftPhiExpectedPullback
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
      (Mirabolic.phiMinus T ψ r) ⋙
    T.leftMixedProductFunctor (k + 1) r ⋙
      Mirabolic.continuousPullbackFunctor
        (rankCast (R := F.Carrier) (Nat.succ_add k r)).symm.toMonoidHom
        (continuous_rankCast_symm _)

/-- The exact published lower host functor agrees naturally with explicit
pullback of compact induction of the actual source-Phi coefficient. -/
def leftPhiExpectedHostIso
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    leftPhiExpected.{uF, uV} T ψ k r ≅ leftPhiExpectedPullback T k r ψ :=
  letI := T.topology
  Functor.isoWhiskerLeft
    ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
      (Mirabolic.phiMinus T ψ r) ⋙ T.leftMixedProductFunctor (k + 1) r)
    (mirabolicRankCastMixedOrbitIso T (Nat.succ_add k r))

theorem leftPhiExpectedPullback_representation
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    ((leftPhiExpectedPullback T k r ψ).obj X).representation =
      (compactInduced (leftSubgroup (k + 1) r F.Carrier)
        (leftPhiSourceCoefficient T k r ψ X.1.representation X.2)).comp
          (rankCast (R := F.Carrier) (Nat.succ_add k r)).symm.toMonoidHom := rfl

theorem leftPhiExpectedPullback_map
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    SmoothRep.hom ((leftPhiExpectedPullback T k r ψ).map f) =
      pullbackMap (rankCast (R := F.Carrier) (Nat.succ_add k r)).symm.toMonoidHom
        (compactInducedMap (leftSubgroup (k + 1) r F.Carrier)
          (leftPhiSourceCoefficientMap T k r ψ X.1.representation X.2
            (SmoothRep.hom f.1) (SmoothRep.hom f.2))) := rfl

end Langlands.Derivative.MirabolicProductMinus
