import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization

/-! Actual covariance and ambient normalization on the left stages coefficient. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction
  Induction.SplitKernelLocalization Jacquet.Localization MixedProductTensor

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem leftPhi_radical_determinantNorm {n : ℕ} (u : radical n F.Carrier) :
    T.determinantNorm (n + 1) u.val.val = 1 := by
  have hu : u.val.val ∈ GeneralLinear.upperUnipotent (n + 1) F.Carrier :=
    radical_le_upperUnipotent u.property
  have hd : GeneralLinear.determinant u.val.val = 1 := by
    apply Units.ext
    change Matrix.det u.val.val.val = 1
    rw [Matrix.det_of_isUpperTriangular hu.1]
    exact Finset.prod_eq_one fun i _ => hu.2 i
  change T.normalizedAbsUnits _ = 1
  rw [hd, map_one]

variable (k r : ℕ)

/-- The actual higher covariance character restricted to either orbit stabilizer. -/
def leftPhiStabilizerCharacter (i : Fin 2) : leftStabilizer k r F.Carrier i →* ℂˣ :=
  (T.leftLeviCharacter (k + 1) (r + 1)).comp (leftCoefficient k r F.Carrier i)

/-- The higher covariance is trivial on the entire actual radical intersection. -/
theorem leftPhiStabilizerCharacter_radical (i : Fin 2)
    (u : leftRadicalIntersection k r F.Carrier i) :
    leftPhiStabilizerCharacter T k r i (leftRadicalInclusion k r F.Carrier i u) = 1 := by
  change T.leftLeviCharacter (k + 1) (r + 1) (leftRadicalCoefficient k r F.Carrier i u) = 1
  rw [leftRadicalCoefficient_eq]
  apply Units.ext
  rw [T.leftLeviCharacter_apply, map_one,
    leftPhi_radical_determinantNorm T (leftRadicalSource k r i u)]
  simp

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)

/-- The full higher normalized inducing coefficient on the actual orbit stabilizer. -/
def leftPhiNormalizedStabilizer (i : Fin 2) :
    Representation ℂ (leftStabilizer k r F.Carrier i) (V ⊗[ℂ] W) :=
  twist (leftPhiStabilizerCharacter T k r i)
    ((external ρ τ).comp (leftCoefficient k r F.Carrier i))

/-- On the whole actual radical intersection the covariance contributes no scalar. -/
theorem leftPhiNormalizedStabilizer_radical (i : Fin 2)
    (u : leftRadicalIntersection k r F.Carrier i) (x : V ⊗[ℂ] W) :
    leftPhiNormalizedStabilizer T k r ρ τ i
        (leftRadicalInclusion k r F.Carrier i u) x =
      ((external ρ τ).comp (leftRadicalCoefficient k r F.Carrier i)) u x := by
  change (leftPhiStabilizerCharacter T k r i
    (leftRadicalInclusion k r F.Carrier i u) : ℂ) •
      ((external ρ τ).comp (leftRadicalCoefficient k r F.Carrier i)) u x = _
  rw [leftPhiStabilizerCharacter_radical T k r i u, Units.val_one, one_smul]

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The actual quotient carrier before identifying its radical coefficients. -/
abbrev leftPhiNormalizedStagesQuotient (i : Fin 2) :=
  letI := T.topology
  Coinvariants
    (leftPhiStagesRepresentation k r i (leftPhiNormalizedStabilizer T k r ρ τ i))
    (leftPhiStagesIntersection k r i)
    (intersectionCharacter (leftPhiStagesRetraction k r i)
      (leftPhiStagesTheta k r ψ i) (leftPhiStagesStabilizer k r i))

/-- Removing covariance on the radical preserves every coefficient class. -/
def leftPhiNormalizedRadicalEquiv (i : Fin 2) :
    letI := T.topology
    Coinvariants ((leftPhiNormalizedStabilizer T k r ρ τ i).comp
      (leftRadicalInclusion k r F.Carrier i)) ⊤ (leftPhiOrbitCharacter k r ψ i) ≃ₗ[ℂ]
      leftPhiCoefficientQuotient k r ψ ρ τ i :=
  letI := T.topology
  transportEquiv
    ((leftPhiNormalizedStabilizer T k r ρ τ i).comp
      (leftRadicalInclusion k r F.Carrier i))
    (leftPhiOrbitRepresentation k r ρ τ i) ⊤ ⊤ _
    (leftPhiOrbitCharacter k r ψ i) (MulEquiv.refl _) (LinearEquiv.refl ℂ _)
    (fun u x => leftPhiNormalizedStabilizer_radical T k r ρ τ i u.val x)
    (fun _ => rfl)

@[simp] theorem leftPhiNormalizedRadicalEquiv_mk (i : Fin 2) (x : V ⊗[ℂ] W) :
    letI := T.topology
    leftPhiNormalizedRadicalEquiv T k r ρ τ ψ i (mk _ _ _ x) =
      leftPhiCoefficientMk k r ψ ρ τ i x := rfl

/-- The nested quotient of the full covariance-normalized coefficient,
identified with the unnormalized orbit quotient by the identity on classes. -/
def leftPhiNormalizedStagesCoefficientEquiv (i : Fin 2) :
    letI := T.topology
    leftPhiNormalizedStagesQuotient T k r ρ τ ψ i ≃ₗ[ℂ]
      leftPhiCoefficientQuotient k r ψ ρ τ i :=
  letI := T.topology
  (leftPhiStagesCoefficientEquiv k r ψ i
      (leftPhiNormalizedStabilizer T k r ρ τ i)).trans
    (leftPhiNormalizedRadicalEquiv T k r ρ τ ψ i)

@[simp] theorem leftPhiNormalizedStagesCoefficientEquiv_mk (i : Fin 2) (x : V ⊗[ℂ] W) :
    letI := T.topology
    leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ i (mk _ _ _ x) =
      leftPhiCoefficientMk k r ψ ρ τ i x := rfl

/-- The inverse-half determinant character respects the actual mirabolic rank cast. -/
theorem leftPhiCharacter_rankCast_symm {m n : ℕ} (h : m = n)
    (g : mirabolic n F.Carrier) :
    Mirabolic.phiMinusCharacter T m ((rankCast h).symm g) =
      Mirabolic.phiMinusCharacter T n g := by
  subst n
  have he : (rankCast (R := F.Carrier) (rfl : m = m)).symm g = g := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    rfl
  rw [he]

/-- The ambient Phi inverse-half character on the actual smaller stages section. -/
def leftPhiAmbientSectionCharacter (i : Fin 2) :
    (leftStages k r F.Carrier i).comap plusSuccessor →* ℂˣ :=
  (Mirabolic.phiMinusCharacter T (k + r + 1)).comp
    ((leftStages k r F.Carrier i).comap plusSuccessor).subtype

/-- The actual stages coefficient action, including ambient minus normalization. -/
def leftPhiNormalizedStagesAction (i : Fin 2) :
    letI := T.topology
    Representation ℂ ((leftStages k r F.Carrier i).comap plusSuccessor)
      (leftPhiNormalizedStagesQuotient T k r ρ τ ψ i) :=
  letI := T.topology
  twist (leftPhiAmbientSectionCharacter T k r i)
    (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i))

/-- The actual normalized section action on every coefficient representative,
before evaluating the complete scalar at the identity orbit. -/
theorem leftPhiNormalizedStagesCoefficientEquiv_action_mk (i : Fin 2)
    (l : (leftStages k r F.Carrier i).comap plusSuccessor) (x : V ⊗[ℂ] W) :
    letI := T.topology
    leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ i
        (leftPhiNormalizedStagesAction T k r ρ τ ψ i l (mk _ _ _ x)) =
      ((leftPhiAmbientSectionCharacter T k r i l *
        leftPhiStabilizerCharacter T k r i
          (sectionInclusion (leftInducing k r F.Carrier)
            (leftRepresentative k r F.Carrier i)
            (leftPhiStagesSectionEquiv k r i l)) : ℂˣ) : ℂ) •
        leftPhiCoefficientMk k r ψ ρ τ i
          (((external ρ τ).comp (leftCoefficient k r F.Carrier i))
            (sectionInclusion (leftInducing k r F.Carrier)
              (leftRepresentative k r F.Carrier i)
              (leftPhiStagesSectionEquiv k r i l)) x) := by
  let := T.topology
  change leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ i
    ((leftPhiAmbientSectionCharacter T k r i l : ℂ) •
      leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i)
        l (mk _ _ _ x)) = _
  rw [map_smul]
  change (leftPhiAmbientSectionCharacter T k r i l : ℂ) •
    leftPhiNormalizedRadicalEquiv T k r ρ τ ψ i
      (leftPhiStagesCoefficientEquiv k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i)
        (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i)
          l (mk _ _ _ x))) = _
  rw [leftPhiStagesCoefficientEquiv_section_mk, leftPhiNormalizedRadicalEquiv_mk]
  change (leftPhiAmbientSectionCharacter T k r i l : ℂ) •
    leftPhiCoefficientMk k r ψ ρ τ i
      ((leftPhiStabilizerCharacter T k r i
        (sectionInclusion (leftInducing k r F.Carrier)
          (leftRepresentative k r F.Carrier i)
          (leftPhiStagesSectionEquiv k r i l)) : ℂ) • _) = _
  simp only [map_smul, smul_smul, Units.val_mul]

/-- Covariance times ambient inverse-half normalization is exactly the previously
computed full lower section character, through the actual rank transport. -/
theorem leftPhiNormalizedSection_scalar
    (l : (leftStages k r F.Carrier 1).comap plusSuccessor) :
    leftPhiAmbientSectionCharacter T k r 1 l *
        leftPhiStabilizerCharacter T k r 1
          (sectionInclusion (leftInducing k r F.Carrier)
            (leftRepresentative k r F.Carrier 1)
            (leftPhiStagesSectionEquiv k r 1 l)) =
      leftPhiSectionCharacter T (k + 1) r
        (leftIdentitySectionEquiv k r F.Carrier (leftPhiStagesSectionEquiv k r 1 l)) := by
  have hα : leftPhiAmbientSectionCharacter T k r 1 l =
      Mirabolic.phiMinusCharacter T (k + 1 + r)
        (leftIdentitySectionEquiv k r F.Carrier
          (leftPhiStagesSectionEquiv k r 1 l)).val := by
    change Mirabolic.phiMinusCharacter T (k + r + 1) l.val = _
    rw [leftIdentitySectionEquiv_val,
      leftPhiCharacter_rankCast_symm, leftPhiStagesSectionEquiv_val]
  rw [hα, leftPhiSectionCharacter_apply]
  congr 1
  change T.leftLeviCharacter (k + 1) (r + 1)
    (leftSectionCoefficient k r F.Carrier 1 (leftPhiStagesSectionEquiv k r 1 l)) = _
  rw [leftSectionCoefficient_one]

/-- At the identity orbit, the actual normalized action has the full computed
section scalar and the actual successor action on the second tensor factor. -/
theorem leftPhiNormalizedStagesCoefficientEquiv_one_tmul
    (l : (leftStages k r F.Carrier 1).comap plusSuccessor) (v : V) (w : W) :
    letI := T.topology
    leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ 1
        (leftPhiNormalizedStagesAction T k r ρ τ ψ 1 l (mk _ _ _ (v ⊗ₜ w))) =
      (leftPhiSectionCharacter T (k + 1) r
        (leftIdentitySectionEquiv k r F.Carrier (leftPhiStagesSectionEquiv k r 1 l)) : ℂ) •
        leftPhiCoefficientMk k r ψ ρ τ 1
          (ρ (leftProjection (leftIdentitySectionEquiv k r F.Carrier
              (leftPhiStagesSectionEquiv k r 1 l))).1 v ⊗ₜ
            τ (successor (leftProjection (leftIdentitySectionEquiv k r F.Carrier
              (leftPhiStagesSectionEquiv k r 1 l))).2) w) := by
  let := T.topology
  rw [leftPhiNormalizedStagesCoefficientEquiv_action_mk,
    leftPhiNormalizedSection_scalar, leftPhiInducingSection_tmul]

/-- The complete actual normalized cycle coefficient is zero. -/
theorem leftPhiNormalizedStagesQuotient_zero_subsingleton :
    Subsingleton (leftPhiNormalizedStagesQuotient T k r ρ τ ψ 0) := by
  let := T.topology
  let := leftPhiCoefficientQuotient_zero_subsingleton k r ψ ρ τ
  exact (leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ 0).injective.subsingleton

/-- The entire actual normalized identity-orbit quotient is the tensor with
the actual source character quotient. -/
def leftPhiNormalizedStagesTensorEquiv :
    letI := T.topology
    leftPhiNormalizedStagesQuotient T k r ρ τ ψ 1 ≃ₗ[ℂ]
      V ⊗[ℂ] Coinvariants τ (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) :=
  letI := T.topology
  (leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ 1).trans
    (leftPhiTensorEquiv k r ψ ρ τ)

@[simp] theorem leftPhiNormalizedStagesTensorEquiv_mk_tmul (v : V) (w : W) :
    letI := T.topology
    leftPhiNormalizedStagesTensorEquiv T k r ρ τ ψ (mk _ _ _ (v ⊗ₜ w)) =
      v ⊗ₜ mk τ (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) w := rfl

/-- The full normalized identity section action, after identifying the complete
quotient with the tensor of the source quotient. -/
theorem leftPhiNormalizedStagesTensorEquiv_action_tmul
    (l : (leftStages k r F.Carrier 1).comap plusSuccessor) (v : V) (w : W) :
    letI := T.topology
    leftPhiNormalizedStagesTensorEquiv T k r ρ τ ψ
        (leftPhiNormalizedStagesAction T k r ρ τ ψ 1 l (mk _ _ _ (v ⊗ₜ w))) =
      (leftPhiSectionCharacter T (k + 1) r
        (leftIdentitySectionEquiv k r F.Carrier (leftPhiStagesSectionEquiv k r 1 l)) : ℂ) •
        (ρ (leftProjection (leftIdentitySectionEquiv k r F.Carrier
            (leftPhiStagesSectionEquiv k r 1 l))).1 v ⊗ₜ
          mk τ (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r)
            (τ (successor (leftProjection (leftIdentitySectionEquiv k r F.Carrier
              (leftPhiStagesSectionEquiv k r 1 l))).2) w)) := by
  let := T.topology
  unfold leftPhiNormalizedStagesTensorEquiv
  rw [LinearEquiv.trans_apply]
  rw [leftPhiNormalizedStagesCoefficientEquiv_one_tmul, map_smul,
    leftPhiTensorEquiv_mk_tmul]

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {τ' : Representation ℂ (mirabolic (r + 1) F.Carrier) W'}

/-- Arbitrary maps in both factors intertwine the full higher covariance coefficients. -/
def leftPhiNormalizedStabilizerMap
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') (i : Fin 2) :
    (leftPhiNormalizedStabilizer T k r ρ τ i).IntertwiningMap
      (leftPhiNormalizedStabilizer T k r ρ' τ' i) :=
  twistIntertwining (leftPhiStabilizerCharacter T k r i)
    (pullbackMap (leftCoefficient k r F.Carrier i) (externalMap f g))

/-- Actual normalized stages maps, with independent universes for both new carriers. -/
def leftPhiNormalizedStagesMap
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') (i : Fin 2) :
    letI := T.topology
    (leftPhiNormalizedStagesAction T k r ρ τ ψ i).IntertwiningMap
      (leftPhiNormalizedStagesAction T k r ρ' τ' ψ i) :=
  letI := T.topology
  twistIntertwining (leftPhiAmbientSectionCharacter T k r i)
    (leftPhiStagesMap k r ψ i (leftPhiNormalizedStabilizerMap T k r ρ τ f g i))

@[simp] theorem leftPhiNormalizedStagesMap_mk
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') (i : Fin 2) (x : V ⊗[ℂ] W) :
    letI := T.topology
    leftPhiNormalizedStagesMap T k r ρ τ ψ f g i (mk _ _ _ x) =
      mk _ _ _ (TensorProduct.map f.toLinearMap g.toLinearMap x) := rfl

/-- The normalized coefficient identification commutes with every actual input map. -/
theorem leftPhiNormalizedStagesCoefficientEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') (i : Fin 2)
    (z : leftPhiNormalizedStagesQuotient T k r ρ τ ψ i) :
    letI := T.topology
    leftPhiNormalizedStagesCoefficientEquiv T k r ρ' τ' ψ i
        (leftPhiNormalizedStagesMap T k r ρ τ ψ f g i z) =
      leftPhiCoefficientMap k r ψ ρ τ f g i
        (leftPhiNormalizedStagesCoefficientEquiv T k r ρ τ ψ i z) := by
  let := T.topology
  refine Submodule.Quotient.induction_on _ z (fun x => ?_)
  rfl

/-- The identity-orbit tensor identification is natural on the complete quotient
for arbitrary input intertwiners and independent carrier universes. -/
theorem leftPhiNormalizedStagesTensorEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (z : leftPhiNormalizedStagesQuotient T k r ρ τ ψ 1) :
    letI := T.topology
    leftPhiNormalizedStagesTensorEquiv T k r ρ' τ' ψ
        (leftPhiNormalizedStagesMap T k r ρ τ ψ f g 1 z) =
      TensorProduct.map f.toLinearMap
        (mapLinear (radical (r + 1) F.Carrier) (Mirabolic.theta ψ r) g)
        (leftPhiNormalizedStagesTensorEquiv T k r ρ τ ψ z) := by
  let := T.topology
  change leftPhiTensorEquiv k r ψ ρ' τ'
    (leftPhiNormalizedStagesCoefficientEquiv T k r ρ' τ' ψ 1 _) = _
  rw [leftPhiNormalizedStagesCoefficientEquiv_natural, leftPhiTensorEquiv_naturality]
  rfl

end Langlands.Derivative.MirabolicProductMinus
