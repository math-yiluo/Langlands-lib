import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Parabolic.SecondAdjointnessStatement
import Langlands.Representation.Parabolic.NaturalInductionDualityStatement
import Langlands.Representation.Parabolic.NaturalJacquetDualityStatement
import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Smooth.Contragredient.HomDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters

/-!
# Second adjointness from natural induction and Jacquet duality

Given natural same-parabolic induction duality and natural upper/opposite
Jacquet duality, the composite

`Hom(i_P σ, π) ≃ Hom(Dπ, D(i_P σ)) ≃ Hom(Dπ, i_P(Dσ)) ≃ Hom(r_P(Dπ), Dσ)
  ≃ Hom(D(r̄_P π), Dσ) ≃ Hom(σ, r̄_P π)`

of admissible Hom duality, induction duality, first adjointness, Jacquet duality
and inverse admissible Hom duality is natural in both variables.
-/

noncomputable section

namespace Langlands.Parabolic.SecondAdjointness

open GeneralLinear Geometric

universe uF uV uW uG uA uB uC

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uA} {W : Type uB} {U : Type uC}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

/-- Admissible Hom duality, as the linear equivalence given by `contragredientMap`. -/
def homDuality
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSmooth ρ) (hσ : IsAdmissible σ) :
    ρ.IntertwiningMap σ ≃ₗ[ℂ]
      (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ) :=
  let t : ρ.IntertwiningMap σ →ₗ[ℂ]
      (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ) :=
    { toFun := contragredientMap
      map_add' := contragredientMap_add
      map_smul' := contragredientMap_smul }
  LinearEquiv.ofBijective t
    (contragredientMap_bijective_of_bidual hρ hσ.1
      ⟨smoothBidual_injective_of_compact_cofinal hcof σ hσ.1,
        smoothBidual_surjective_of_compact_cofinal hcof σ hσ⟩)

@[simp]
theorem homDuality_apply
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSmooth ρ) (hσ : IsAdmissible σ) (f : ρ.IntertwiningMap σ) :
    homDuality hcof hρ hσ f = contragredientMap f := rfl

/-- Postcomposition with an equivalence of representations. -/
def postcomp (E : σ.Equiv τ) : ρ.IntertwiningMap σ ≃ₗ[ℂ] ρ.IntertwiningMap τ where
  toFun f := E.toIntertwiningMap.comp f
  invFun g := E.symm.toIntertwiningMap.comp g
  left_inv f := Representation.IntertwiningMap.ext (LinearMap.ext fun v => E.symm_apply_apply (f v))
  right_inv g := Representation.IntertwiningMap.ext (LinearMap.ext fun v => E.apply_symm_apply (g v))
  map_add' f g := Representation.IntertwiningMap.ext (LinearMap.ext fun v => map_add E (f v) (g v))
  map_smul' c f := Representation.IntertwiningMap.ext (LinearMap.ext fun v => map_smul E c (f v))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem postcomp_apply (E : σ.Equiv τ) (f : ρ.IntertwiningMap σ) :
    postcomp E f = E.toIntertwiningMap.comp f := rfl

/-- Precomposition with the inverse of an equivalence of representations. -/
def precomp (E : ρ.Equiv τ) : ρ.IntertwiningMap σ ≃ₗ[ℂ] τ.IntertwiningMap σ where
  toFun f := f.comp E.symm.toIntertwiningMap
  invFun g := g.comp E.toIntertwiningMap
  left_inv f := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    congrArg f (E.symm_apply_apply v))
  right_inv g := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    congrArg g (E.apply_symm_apply v))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem precomp_apply (E : ρ.Equiv τ) (f : ρ.IntertwiningMap σ) :
    precomp E f = f.comp E.symm.toIntertwiningMap := rfl

end Generic

section Cofinal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Compact open subgroups are cofinal among open subgroups of a refined Levi,
transported from the flattened block Levi. -/
theorem refinedLevi_compactOpen_cofinal' {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    ∀ H : OpenSubgroup (refinedLevi F.Carrier B S),
      ∃ K : OpenSubgroup (refinedLevi F.Carrier B S),
        IsCompact (K : Set (refinedLevi F.Carrier B S)) ∧ K ≤ H := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let e := flattenedLeviEquivContinuous F.Carrier B S
  intro H
  let H' : OpenSubgroup ((B.flatten S).Levi F.Carrier) :=
    H.comap e.toMulEquiv.toMonoidHom e.continuous
  obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen (B.flatten S) H' (H'.isOpen.mem_nhds H'.one_mem)
  refine ⟨K.comap e.symm.toMulEquiv.toMonoidHom e.symm.continuous, ?_, ?_⟩
  · exact e.symm.toHomeomorph.isCompact_preimage.mpr hK
  · intro x hx
    have h := hKH hx
    change e (e.symm x) ∈ H at h
    simpa using h

end Cofinal

section Standard

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n)

/-- The opposite Jacquet functor on intertwiners, with underlying linear map the
pointwise `Jacquet.map`. -/
def oppositeJacquetMap {π π' : Rep.{uW} ℂ (GeneralLinear n F.Carrier)}
    (b : π.ρ.IntertwiningMap π'.ρ) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ.IntertwiningMap
      (CuspidalJacquetMultiplicity.oppositeJacquet T B π').ρ where
  toLinearMap := (Jacquet.map (B.oppositeUnipotentSubgroup F.Carrier)
    (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) b).toLinearMap
  isIntertwining' m := (Jacquet.normalizedMapOfModulus (B.oppositeUnipotentSubgroup F.Carrier)
    (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹ b).isIntertwining'
      (B.leviEquiv F.Carrier m)

theorem oppositeJacquetMap_apply {π π' : Rep.{uW} ℂ (GeneralLinear n F.Carrier)}
    (b : π.ρ.IntertwiningMap π'.ρ) (y : CuspidalJacquetMultiplicity.oppositeJacquet T B π) :
    oppositeJacquetMap T B b y =
      Jacquet.map (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) b y := rfl

variable
  (EI : letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    ∀ (σ : Rep.{uV} ℂ (B.Levi F.Carrier)), IsAdmissible σ.ρ →
      Representation.Equiv
        (smoothContragredient (T.normalizedParabolicInduced B σ.ρ))
        (T.normalizedParabolicInduced B (smoothContragredient σ.ρ)))
  (EJ : letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    ∀ (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier)), IsAdmissible π.ρ →
      Representation.Equiv
        (T.normalizedJacquet B (smoothContragredient π.ρ))
        (smoothContragredient (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ))

/-- The composite second-adjointness equivalence for a standard parabolic. -/
def family (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    IsAdmissible σ.ρ → IsAdmissible π.ρ →
      ((T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) ≃ₗ[ℂ]
        (σ.ρ.IntertwiningMap (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  fun hσ hπ =>
    (homDuality (GeneralLinear.compactOpen_cofinal F T n)
        (T.isSmooth_normalizedParabolicInduced B σ.ρ) hπ).trans <|
      (postcomp (EI σ hσ)).trans <|
        (FirstAdjointness.equiv T B (isSmooth_smoothContragredient π.ρ)).trans <|
          (precomp (EJ π hπ)).trans <|
            (homDuality (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) hσ.1
              (Parabolic.isAdmissible_standardOppositeJacquet F T B π π.ρ hπ)).symm

/-- The contragredient of the composite is the first-adjointness image composed
with inverse Jacquet duality. -/
theorem contragredientMap_family (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (f : letI := T.topology
      (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    contragredientMap (family T B EI EJ σ π hσ hπ f) =
      (FirstAdjointness.equiv T B (isSmooth_smoothContragredient π.ρ)
        ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f))).comp
          (EJ π hπ).symm.toIntertwiningMap := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  exact LinearEquiv.apply_symm_apply (homDuality (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) hσ.1
    (Parabolic.isAdmissible_standardOppositeJacquet F T B π π.ρ hπ)) _

/-- Naturality of the composite in the inducing representation. -/
theorem family_inducedMap
    (hEI : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      ∀ (σ τ : Rep.{uV} ℂ (B.Levi F.Carrier))
        (hσ : IsAdmissible σ.ρ) (hτ : IsAdmissible τ.ρ)
        (a : σ.ρ.IntertwiningMap τ.ρ)
        (ℓ : SmoothDual (T.normalizedParabolicInduced B τ.ρ)),
        EI σ hσ (contragredientMap (T.normalizedParabolicInducedMap B a) ℓ) =
          T.normalizedParabolicInducedMap B (contragredientMap a) (EI τ hτ ℓ))
    (σ σ' : Rep.{uV} ℂ (B.Levi F.Carrier)) (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hσ' : letI := T.topology
      IsAdmissible σ'.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (a : σ'.ρ.IntertwiningMap σ.ρ)
    (f : letI := T.topology
      (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    family T B EI EJ σ' π hσ' hπ (f.comp (T.normalizedParabolicInducedMap B a)) =
      (family T B EI EJ σ π hσ hπ f).comp a := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  refine (homDuality (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) hσ'.1
    (Parabolic.isAdmissible_standardOppositeJacquet F T B π π.ρ hπ)).injective ?_
  refine (homDuality_apply _ _ _ _).trans (Eq.trans ?_ (homDuality_apply _ _ _ _).symm)
  refine (contragredientMap_family T B EI EJ σ' π hσ' hπ _).trans ?_
  refine Eq.trans ?_ (contragredientMap_comp a (family T B EI EJ σ π hσ hπ f)).symm
  refine Eq.trans ?_ (congrArg (fun g => (contragredientMap a).comp g)
    (contragredientMap_family T B EI EJ σ π hσ hπ f)).symm
  have h1 : (EI σ' hσ').toIntertwiningMap.comp
        (contragredientMap (f.comp (T.normalizedParabolicInducedMap B a))) =
      (T.normalizedParabolicInducedMap B (contragredientMap a)).comp
        ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ℓ
    exact hEI σ' σ hσ' hσ a (contragredientMap f ℓ)
  refine (congrArg (fun g => (FirstAdjointness.equiv T B (isSmooth_smoothContragredient π.ρ)
    g).comp (EJ π hπ).symm.toIntertwiningMap) h1).trans ?_
  refine (congrArg (fun g => g.comp (EJ π hπ).symm.toIntertwiningMap)
    (FirstAdjointness.equiv_inducedMap T B (isSmooth_smoothContragredient π.ρ)
      (contragredientMap a) ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)))).trans ?_
  rfl

/-- Naturality of the composite in the ambient representation. -/
theorem family_comp
    (hEJ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      ∀ (π τ : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
        (hπ : IsAdmissible π.ρ) (hτ : IsAdmissible τ.ρ)
        (a : π.ρ.IntertwiningMap τ.ρ)
        (x : B.JacquetModule (smoothContragredient τ.ρ))
        (y : Jacquet.Coinvariants π.ρ (B.oppositeUnipotentSubgroup F.Carrier)),
        (EJ π hπ (T.normalizedJacquetMap B (contragredientMap a) x)).1 y =
          (EJ τ hτ x).1
            (Jacquet.map (B.oppositeUnipotentSubgroup F.Carrier)
              (B.leviSubgroup F.Carrier)
              (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) a y))
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (π π' : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (hπ' : letI := T.topology
      IsAdmissible π'.ρ)
    (b : π.ρ.IntertwiningMap π'.ρ)
    (f : letI := T.topology
      (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    family T B EI EJ σ π' hσ hπ' (b.comp f) =
      (oppositeJacquetMap T B b).comp (family T B EI EJ σ π hσ hπ f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  refine (homDuality (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) hσ.1
    (Parabolic.isAdmissible_standardOppositeJacquet F T B π' π'.ρ hπ')).injective ?_
  refine (homDuality_apply _ _ _ _).trans (Eq.trans ?_ (homDuality_apply _ _ _ _).symm)
  refine (contragredientMap_family T B EI EJ σ π' hσ hπ' (b.comp f)).trans ?_
  refine Eq.trans ?_ (contragredientMap_comp (family T B EI EJ σ π hσ hπ f)
    (oppositeJacquetMap T B b)).symm
  refine Eq.trans ?_ (congrArg (fun g => g.comp (contragredientMap (oppositeJacquetMap T B b)))
    (contragredientMap_family T B EI EJ σ π hσ hπ f)).symm
  refine (congrArg (fun g => (FirstAdjointness.equiv T B (isSmooth_smoothContragredient π'.ρ)
    ((EI σ hσ).toIntertwiningMap.comp g)).comp (EJ π' hπ').symm.toIntertwiningMap)
    (contragredientMap_comp f b)).trans ?_
  refine (congrArg (fun g => g.comp (EJ π' hπ').symm.toIntertwiningMap)
    (FirstAdjointness.equiv_comp T B (isSmooth_smoothContragredient π.ρ)
      (isSmooth_smoothContragredient π'.ρ) (contragredientMap b)
      ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)))).trans ?_
  have h2 : (T.normalizedJacquetMap B (contragredientMap b)).comp
        (EJ π' hπ').symm.toIntertwiningMap =
      (EJ π hπ).symm.toIntertwiningMap.comp (contragredientMap (oppositeJacquetMap T B b)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ℓ
    change T.normalizedJacquetMap B (contragredientMap b) ((EJ π' hπ').symm ℓ) =
      (EJ π hπ).symm (contragredientMap (oppositeJacquetMap T B b) ℓ)
    apply EquivLike.injective (EJ π hπ)
    rw [Representation.Equiv.apply_symm_apply]
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    have h := hEJ π π' hπ hπ' b ((EJ π' hπ').symm ℓ) y
    rw [Representation.Equiv.apply_symm_apply] at h
    exact h
  exact congrArg (fun g => (FirstAdjointness.equiv T B (isSmooth_smoothContragredient π.ρ)
    ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f))).comp g) h2

/-- Standard second adjointness from natural induction and Jacquet duality. -/
theorem standardSecondAdjointness_of_dualities
    (hI : StandardNaturalInductionDualityClause.{uF, uV})
    (hJ : StandardNaturalJacquetDualityClause.{uF, uW}) :
    StandardSecondAdjointnessClause.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n _ B
  obtain ⟨EI, hEI⟩ := hI p F T n B
  obtain ⟨EJ, hEJ⟩ := hJ p F T n B
  refine ⟨fun σ π hσ hπ => family T B EI EJ σ π hσ hπ, ?_, ?_⟩
  · intro σ σ' π hσ hσ' hπ a f v
    exact congrArg (fun g => g v) (family_inducedMap T B EI EJ hEI σ σ' π hσ hσ' hπ a f)
  · intro σ π π' hσ hπ hπ' b f v
    exact congrArg (fun g => g v) (family_comp T B EI EJ hEJ σ π π' hσ hπ hπ' b f)

end Standard

section Refined

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)

variable
  (EI : letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)), IsAdmissible σ.ρ →
      Representation.Equiv
        (smoothContragredient (T.normalizedRefinedInduced B S σ.ρ))
        (T.normalizedRefinedInduced B S (smoothContragredient σ.ρ)))
  (EJ : letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (π : Rep.{uW} ℂ (B.Levi F.Carrier)), IsAdmissible π.ρ →
      Representation.Equiv
        (T.normalizedRefinedJacquet B S (smoothContragredient π.ρ))
        (smoothContragredient (T.normalizedRefinedOppositeJacquet B S π.ρ)))

/-- The composite second-adjointness equivalence for a parabolic of a block Levi. -/
def refinedFamily (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    IsAdmissible σ.ρ → IsAdmissible π.ρ →
      ((T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) ≃ₗ[ℂ]
        (σ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  fun hσ hπ =>
    (homDuality (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
        (T.isSmooth_normalizedRefinedInduced B S σ.ρ) hπ).trans <|
      (postcomp (EI σ hσ)).trans <|
        (FirstAdjointness.refinedEquiv T B S (isSmooth_smoothContragredient π.ρ)).trans <|
          (precomp (EJ π hπ)).trans <|
            (homDuality (refinedLevi_compactOpen_cofinal' T B S) hσ.1
              (isAdmissible_normalizedRefinedOppositeJacquet F T B S _ π.ρ hπ)).symm

/-- The contragredient of the refined composite is the refined first-adjointness
image composed with inverse refined Jacquet duality. -/
theorem contragredientMap_refinedFamily (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (f : letI := T.topology
      (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    contragredientMap (refinedFamily T B S EI EJ σ π hσ hπ f) =
      (FirstAdjointness.refinedEquiv T B S (isSmooth_smoothContragredient π.ρ)
        ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f))).comp
          (EJ π hπ).symm.toIntertwiningMap := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact LinearEquiv.apply_symm_apply (homDuality (refinedLevi_compactOpen_cofinal' T B S) hσ.1
    (isAdmissible_normalizedRefinedOppositeJacquet F T B S _ π.ρ hπ)) _

/-- Naturality of the refined composite in the inducing representation. -/
theorem refinedFamily_inducedMap
    (hEI : letI := T.topology
      letI := T.leviTopologicalGroup B
      ∀ (σ τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
        (hσ : IsAdmissible σ.ρ) (hτ : IsAdmissible τ.ρ)
        (a : σ.ρ.IntertwiningMap τ.ρ)
        (ℓ : SmoothDual (T.normalizedRefinedInduced B S τ.ρ)),
        EI σ hσ (contragredientMap (T.normalizedRefinedInducedMap B S a) ℓ) =
          T.normalizedRefinedInducedMap B S (contragredientMap a) (EI τ hτ ℓ))
    (σ σ' : Rep.{uV} ℂ (refinedLevi F.Carrier B S)) (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hσ' : letI := T.topology
      IsAdmissible σ'.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (a : σ'.ρ.IntertwiningMap σ.ρ)
    (f : letI := T.topology
      (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    refinedFamily T B S EI EJ σ' π hσ' hπ (f.comp (T.normalizedRefinedInducedMap B S a)) =
      (refinedFamily T B S EI EJ σ π hσ hπ f).comp a := by
  let := T.topology
  let := T.leviTopologicalGroup B
  refine (homDuality (refinedLevi_compactOpen_cofinal' T B S) hσ'.1
    (isAdmissible_normalizedRefinedOppositeJacquet F T B S _ π.ρ hπ)).injective ?_
  refine (homDuality_apply _ _ _ _).trans (Eq.trans ?_ (homDuality_apply _ _ _ _).symm)
  refine (contragredientMap_refinedFamily T B S EI EJ σ' π hσ' hπ _).trans ?_
  refine Eq.trans ?_ (contragredientMap_comp a (refinedFamily T B S EI EJ σ π hσ hπ f)).symm
  refine Eq.trans ?_ (congrArg (fun g => (contragredientMap a).comp g)
    (contragredientMap_refinedFamily T B S EI EJ σ π hσ hπ f)).symm
  have h1 : (EI σ' hσ').toIntertwiningMap.comp
        (contragredientMap (f.comp (T.normalizedRefinedInducedMap B S a))) =
      (T.normalizedRefinedInducedMap B S (contragredientMap a)).comp
        ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ℓ
    exact hEI σ' σ hσ' hσ a (contragredientMap f ℓ)
  refine (congrArg (fun g => (FirstAdjointness.refinedEquiv T B S
    (isSmooth_smoothContragredient π.ρ) g).comp (EJ π hπ).symm.toIntertwiningMap) h1).trans ?_
  refine (congrArg (fun g => g.comp (EJ π hπ).symm.toIntertwiningMap)
    (FirstAdjointness.refinedEquiv_inducedMap T B S (isSmooth_smoothContragredient π.ρ)
      (contragredientMap a) ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)))).trans ?_
  rfl

/-- Naturality of the refined composite in the ambient representation. -/
theorem refinedFamily_comp
    (hEJ : letI := T.topology
      letI := T.leviTopologicalGroup B
      ∀ (π τ : Rep.{uW} ℂ (B.Levi F.Carrier))
        (hπ : IsAdmissible π.ρ) (hτ : IsAdmissible τ.ρ)
        (a : π.ρ.IntertwiningMap τ.ρ)
        (x : RefinedJacquetModule B S (smoothContragredient τ.ρ))
        (y : RefinedOppositeJacquetModule B S π.ρ),
        (EJ π hπ (T.normalizedRefinedJacquetMap B S (contragredientMap a) x)).1 y =
          (EJ τ hτ x).1 (T.normalizedRefinedOppositeJacquetMap B S a y))
    (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)) (π π' : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hσ : letI := T.topology
      IsAdmissible σ.ρ)
    (hπ : letI := T.topology
      IsAdmissible π.ρ)
    (hπ' : letI := T.topology
      IsAdmissible π'.ρ)
    (b : π.ρ.IntertwiningMap π'.ρ)
    (f : letI := T.topology
      (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) :
    letI := T.topology
    refinedFamily T B S EI EJ σ π' hσ hπ' (b.comp f) =
      (T.normalizedRefinedOppositeJacquetMap B S b).comp
        (refinedFamily T B S EI EJ σ π hσ hπ f) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  refine (homDuality (refinedLevi_compactOpen_cofinal' T B S) hσ.1
    (isAdmissible_normalizedRefinedOppositeJacquet F T B S _ π'.ρ hπ')).injective ?_
  refine (homDuality_apply _ _ _ _).trans (Eq.trans ?_ (homDuality_apply _ _ _ _).symm)
  refine (contragredientMap_refinedFamily T B S EI EJ σ π' hσ hπ' (b.comp f)).trans ?_
  refine Eq.trans ?_ (contragredientMap_comp (refinedFamily T B S EI EJ σ π hσ hπ f)
    (T.normalizedRefinedOppositeJacquetMap B S b)).symm
  refine Eq.trans ?_ (congrArg
    (fun g => g.comp (contragredientMap (T.normalizedRefinedOppositeJacquetMap B S b)))
    (contragredientMap_refinedFamily T B S EI EJ σ π hσ hπ f)).symm
  refine (congrArg (fun g => (FirstAdjointness.refinedEquiv T B S
    (isSmooth_smoothContragredient π'.ρ)
    ((EI σ hσ).toIntertwiningMap.comp g)).comp (EJ π' hπ').symm.toIntertwiningMap)
    (contragredientMap_comp f b)).trans ?_
  refine (congrArg (fun g => g.comp (EJ π' hπ').symm.toIntertwiningMap)
    (FirstAdjointness.refinedEquiv_comp T B S (isSmooth_smoothContragredient π.ρ)
      (isSmooth_smoothContragredient π'.ρ) (contragredientMap b)
      ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f)))).trans ?_
  have h2 : (T.normalizedRefinedJacquetMap B S (contragredientMap b)).comp
        (EJ π' hπ').symm.toIntertwiningMap =
      (EJ π hπ).symm.toIntertwiningMap.comp
        (contragredientMap (T.normalizedRefinedOppositeJacquetMap B S b)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ℓ
    change T.normalizedRefinedJacquetMap B S (contragredientMap b) ((EJ π' hπ').symm ℓ) =
      (EJ π hπ).symm (contragredientMap (T.normalizedRefinedOppositeJacquetMap B S b) ℓ)
    apply EquivLike.injective (EJ π hπ)
    rw [Representation.Equiv.apply_symm_apply]
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    have h := hEJ π π' hπ hπ' b ((EJ π' hπ').symm ℓ) y
    rw [Representation.Equiv.apply_symm_apply] at h
    exact h
  exact congrArg (fun g => (FirstAdjointness.refinedEquiv T B S
    (isSmooth_smoothContragredient π.ρ)
    ((EI σ hσ).toIntertwiningMap.comp (contragredientMap f))).comp g) h2

/-- Refined second adjointness for one block shape and refinement, from given
natural refined induction and Jacquet dualities. -/
theorem refinedSecondAdjointness_at
    (hEI : letI := T.topology
      letI := T.leviTopologicalGroup B
      ∀ (σ τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
        (hσ : IsAdmissible σ.ρ) (hτ : IsAdmissible τ.ρ)
        (a : σ.ρ.IntertwiningMap τ.ρ)
        (ℓ : SmoothDual (T.normalizedRefinedInduced B S τ.ρ)),
        EI σ hσ (contragredientMap (T.normalizedRefinedInducedMap B S a) ℓ) =
          T.normalizedRefinedInducedMap B S (contragredientMap a) (EI τ hτ ℓ))
    (hEJ : letI := T.topology
      letI := T.leviTopologicalGroup B
      ∀ (π τ : Rep.{uW} ℂ (B.Levi F.Carrier))
        (hπ : IsAdmissible π.ρ) (hτ : IsAdmissible τ.ρ)
        (a : π.ρ.IntertwiningMap τ.ρ)
        (x : RefinedJacquetModule B S (smoothContragredient τ.ρ))
        (y : RefinedOppositeJacquetModule B S π.ρ),
        (EJ π hπ (T.normalizedRefinedJacquetMap B S (contragredientMap a) x)).1 y =
          (EJ τ hτ x).1 (T.normalizedRefinedOppositeJacquetMap B S a y)) :
    letI := T.topology
    ∃ E : ∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
        (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
        IsAdmissible σ.ρ → IsAdmissible π.ρ →
        ((T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ) ≃ₗ[ℂ]
          (σ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)),
      (∀ (σ σ' : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
        (π : Rep.{uW} ℂ (B.Levi F.Carrier))
        (hσ : IsAdmissible σ.ρ) (hσ' : IsAdmissible σ'.ρ)
        (hπ : IsAdmissible π.ρ) (a : σ'.ρ.IntertwiningMap σ.ρ)
        (f : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ)
        (v : σ'),
        E σ' π hσ' hπ (f.comp (T.normalizedRefinedInducedMap B S a)) v =
          E σ π hσ hπ f (a v)) ∧
      (∀ (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
        (π π' : Rep.{uW} ℂ (B.Levi F.Carrier))
        (hσ : IsAdmissible σ.ρ) (hπ : IsAdmissible π.ρ)
        (hπ' : IsAdmissible π'.ρ) (b : π.ρ.IntertwiningMap π'.ρ)
        (f : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ)
        (v : σ),
        E σ π' hσ hπ' (b.comp f) v =
          T.normalizedRefinedOppositeJacquetMap B S b (E σ π hσ hπ f v)) :=
  ⟨fun σ π hσ hπ => refinedFamily T B S EI EJ σ π hσ hπ,
    fun σ σ' π hσ hσ' hπ a f v =>
      (congrArg (fun g => g v)
        (refinedFamily_inducedMap T B S EI EJ hEI σ σ' π hσ hσ' hπ a f)).trans
          (Representation.IntertwiningMap.comp_apply _ _ _ _ a v),
    fun σ π π' hσ hπ hπ' b f v =>
      (congrArg (fun g => g v)
        (refinedFamily_comp T B S EI EJ hEJ σ π π' hσ hπ hπ' b f)).trans
          (Representation.IntertwiningMap.comp_apply _ _ _ _ _ v)⟩

/-- Refined second adjointness from natural refined induction and Jacquet duality. -/
theorem refinedSecondAdjointness_of_dualities
    (hI : RefinedNaturalInductionDualityClause.{uF, uV})
    (hJ : RefinedNaturalJacquetDualityClause.{uF, uW}) :
    RefinedSecondAdjointnessClause.{uF, uV, uW} :=
  -- Term-mode `Exists.elim`: tactic `cases`/`obtain` on these clauses is very slow.
  fun p _ F T n _ B S => (hI p F T n B S).elim fun EI hEI =>
    (hJ p F T n B S).elim fun EJ hEJ => refinedSecondAdjointness_at T B S EI EJ hEI hEJ

end Refined

/-- Normalized second adjointness, standard and refined, from natural induction
duality and natural upper/opposite Jacquet duality. -/
theorem secondAdjointness_of_dualities
    (hI : NaturalNormalizedInductionDualityStatement.{uF, uV})
    (hJ : NaturalNormalizedJacquetDualityStatement.{uF, uW}) :
    NormalizedSecondAdjointnessStatement.{uF, uV, uW} :=
  ⟨standardSecondAdjointness_of_dualities hI.1 hJ.1,
    refinedSecondAdjointness_of_dualities hI.2 hJ.2⟩

end Langlands.Parabolic.SecondAdjointness
