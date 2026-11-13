import Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStructure
import Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientForward
import Langlands.Representation.Exponents.LeviJacquetContragredientDynamic
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.Category.FrobeniusChainLimits
import Langlands.Representation.Category.SmoothCoproducts
import Langlands.Representation.Category.ConcreteSmoothLimits
import Langlands.Representation.Jacquet.ProductCompressionStationarity

/-! # Second adjointness is equivalent to the Jacquet–contragredient formula

Renard 2026, VI.9.6 (printed pp.201–202 / PDF pp.207–208). The forward implication is
`nonempty_leviContragredientIso_of_secondAdjunction`. For the reverse implication, a natural
isomorphism `Ψ : r_{P̄}(π~) ≅ (r_P π)~` makes `π ↦ r_{P̄}(π~)` preserve the countable power
`(⊕ π)~ = ∏ π~` (the Frobenius chain of `FrobeniusChainLimits`). From this preserved product
the compression by an `M`-central contracting element has stationary powers on fixed
smooth functionals (`ProductCompressionStationarity`), which gives both Fitting splittings
needed for the stable-lift duality and then second adjointness, exactly as in
`nonempty_leviSecondAdjunction_of_dynamic`.
-/

noncomputable section

universe u v uG uM uV

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {M' : Type uM} [Group M'] [TopologicalSpace M'] [IsTopologicalGroup M']

/-- If the transported normalized Jacquet functor `R = r_U ⋙ e^*` takes the dual of the
countable direct sum `⊕_ℕ A` to a limit cone, then compression by a `Mb`-central element
with an Iwahori contraction for `(U, Mb, O)` has stationary power ranges and kernels on the
`K`-fixed smooth functionals of `A`. -/
theorem contragredient_compression_stationary_of_isLimit
    (U Mb O : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : Mb ≤ Subgroup.normalizer (U : Set G)) (e : M' ≃ₜ* Mb)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hlim : IsLimit (Functor.mapCone (normalizedJacquetFunctor.{uG, uV} U Mb hU hMU ⋙
        SmoothRep.pullbackFunctor e)
      (Functor.mapCone SmoothRep.contragredientFunctor.{0, uG, uV}
        (Cocone.op (SmoothRep.directSumCofan.{uG, 0, uV} (fun _ : ℕ => A))))))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (h : Jacquet.IsIwahoriContraction K U Mb O g) (hcen : ∀ m ∈ Mb, m * g = g * m) :
    ∃ b, ∀ s, b ≤ s →
      LinearMap.range (Jacquet.compressedAction (smoothContragredient A.representation)
          (isSmooth_smoothContragredient A.representation) K hK g ^ s) =
        LinearMap.range (Jacquet.compressedAction (smoothContragredient A.representation)
          (isSmooth_smoothContragredient A.representation) K hK g ^ b) ∧
      LinearMap.ker (Jacquet.compressedAction (smoothContragredient A.representation)
          (isSmooth_smoothContragredient A.representation) K hK g ^ s) =
        LinearMap.ker (Jacquet.compressedAction (smoothContragredient A.representation)
          (isSmooth_smoothContragredient A.representation) K hK g ^ b) := by
  let A' : ℕ → SmoothRep.{0, uG, uV} ℂ G := fun _ => A
  let ρ := smoothContragredient A.representation
  let σ := smoothContragredient (SmoothRep.directSum.{uG, 0, uV} A').representation
  let q : ℕ → σ.IntertwiningMap ρ := fun n =>
    contragredientMap (SmoothRep.hom (SmoothRep.directSumι.{uG, 0, uV} A' n))
  let χ := HaarModulus.closedInverseHalfCharacter U hU Mb hMU
  let _ := (SmoothRep.contragredientAdjunction.{0, uG, uV} (R := ℂ) (G := G)).isRightAdjoint
  have hGlim := isLimitOfPreserves SmoothRep.contragredientFunctor.{0, uG, uV}
    (SmoothRep.directSumIsColimit.{uG, 0, uV} A').op
  refine Jacquet.stationary_of_powerFamily ρ σ (isSmooth_smoothContragredient _)
    (isSmooth_smoothContragredient _) hK h hMU hcen q ?_ ?_ ?_
  · -- every family of `K`-fixed functionals is one `K`-fixed functional on the direct sum
    intro x
    obtain ⟨w, hwfix, hw⟩ := SmoothRep.exists_fixed_eq_of_isLimit hGlim
      (fun j => (x j.unop.as : SmoothDual A.representation))
      (SmoothRep.discreteOp_map_apply _ _) K (fun k hk j => (x j.unop.as).property ⟨k, hk⟩)
    exact ⟨⟨w, fun k => hwfix k k.property⟩, fun n => hw (Opposite.op ⟨n⟩)⟩
  · -- the projections of the preserved product are jointly injective
    intro w hw
    have h0 : (Jacquet.Localization.mk σ U 1 w : Jacquet.Localization.Coinvariants σ U 1) = 0 :=
      SmoothRep.eq_zero_of_isLimit hlim _ fun j => by
        apply (Jacquet.Localization.trivialEquiv ρ U Mb hMU).toLinearEquiv.injective
        exact (hw j.unop.as).trans (map_zero _).symm
    have h1 := congrArg (Jacquet.Localization.trivialEquiv σ U Mb hMU).toLinearEquiv h0
    rw [map_zero] at h1
    exact h1
  · -- every family of Levi-fixed Jacquet classes lifts to the preserved product
    intro y
    choose v hv using fun n => Jacquet.mk_surjective ρ U (y n : Jacquet.Coinvariants ρ U)
    let L : OpenSubgroup M' :=
      ((K.comap Mb.subtype continuous_subtype_val) ⊓
        ⟨χ.ker, HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU Mb hMU⟩).comap
        e.toMonoidHom e.continuous
    refine (SmoothRep.exists_eq_of_isLimit hlim
      (fun j => (Jacquet.Localization.mk ρ U 1 (v j.unop.as) :
        Jacquet.Localization.Coinvariants ρ U 1))
      (SmoothRep.discreteOp_map_apply _ _) L (fun k hk j => ?_)).elim ?_
    rotate_left
    · rintro x hx
      obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective σ U 1 x
      refine ⟨w, fun n => ?_⟩
      have hxn := congrArg (Jacquet.Localization.trivialEquiv ρ U Mb hMU).toLinearEquiv
        (hx (Opposite.op ⟨n⟩))
      rw [← hv n]
      exact hxn
    · have hk1 : ((e k : Mb) : G) ∈ K := hk.1
      have hk2 : χ (e k) = 1 := hk.2
      have hfix : Jacquet.Localization.mk ρ U 1 (ρ (e k) (v j.unop.as)) =
          Jacquet.Localization.mk ρ U 1 (v j.unop.as) := by
        apply (Jacquet.Localization.trivialEquiv ρ U Mb hMU).toLinearEquiv.injective
        change Jacquet.mk ρ U (ρ (e k) (v j.unop.as)) = Jacquet.mk ρ U (v j.unop.as)
        rw [← Jacquet.action_mk ρ U Mb hMU (e k), hv]
        exact (y j.unop.as).property ⟨e k, hk1⟩
      have hχ1 : HaarModulus.closedInverseHalfCharacter U hU Mb hMU (e k) = 1 := hk2
      show (((HaarModulus.closedInverseHalfCharacter U hU Mb hMU (e k) : ℂˣ) : ℂ) •
          Jacquet.Localization.mk ρ U 1 (ρ (e k) (v j.unop.as)) :
            Jacquet.Localization.Coinvariants ρ U 1) =
        Jacquet.Localization.mk ρ U 1 (v j.unop.as)
      rw [hχ1, Units.val_one, one_smul]
      exact hfix

end Generic

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance contragredientEquivalencePointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Subgroups equal to `N(χ⁻¹)`, `M(χ)` and `N(χ)` have an `M(χ)`-central element with an
opposite Iwahori contraction basis: the contraction point of `χ⁻¹` of
`dynamic_exists_central_hasOppositeIwahoriContractionBasis`. -/
theorem exists_central_hasOppositeIwahoriContractionBasis_of_dynamic
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (Ub L O : Subgroup (rationalPoints G))
    (hUχ : Ub = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hLχ : L = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hOχ : O = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) :
    ∃ g : rationalPoints G, (∀ x ∈ L, x * g = g * x) ∧
      Jacquet.HasOppositeIwahoriContractionBasis Ub L O g := by
  subst hUχ hLχ hOχ
  obtain ⟨g, hc, hB⟩ :=
    RationalPointFamily.dynamic_exists_central_hasOppositeIwahoriContractionBasis hG
      (Dynamic.inverseCocharacter χ)
  rw [Dynamic.centralizer_inverseCocharacter, Dynamic.inverseCocharacter_inverseCocharacter]
    at hB
  rw [Dynamic.centralizer_inverseCocharacter] at hc
  exact ⟨g, hc, hB⟩

/-- Renard VI.9.6, (VI.9.6.2) ⇒ (VI.9.6.1), for represented parabolics realized by a
cocharacter as in `nonempty_leviSecondAdjunction_of_dynamic`, with the VI.9.1 uniform
stabilization hypothesis replaced by a natural isomorphism `r_{P̄}(π~) ≅ (r_P π)~`. -/
theorem nonempty_leviSecondAdjunction_of_contragredientIso_of_dynamic
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hN : pointImage (n ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hrec : ∀ (hU : IsClosed (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hO : IsClosed (pointImage (n ≫ p) : Set (rationalPoints G)))
      (hMU : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hMO : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (n ≫ p) : Set (rationalPoints G)))
      (x : pointImage (m ≫ p)),
      HaarModulus.closedRestrictCharacter _ hU _ hMU x *
        HaarModulus.closedRestrictCharacter _ hO _ hMO x = 1)
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hmod : ∀ g : rationalPoints G, Measure.modularCharacter g = 1)
    (hδ :
      letI : LocallyCompactSpace (pointImage p) :=
        (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
      ∀ q : pointImage p, Measure.modularCharacter q =
        (HaarModulus.closedRestrictCharacter (pointImage (n ≫ p))
          (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
          (pointImage p)
          (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul).le_normalizer
          q : ℝ≥0)) :
    letI := leviPointTopology m hm
    haveI : LocallyCompactSpace (rationalPoints M) :=
      leviPoints_locallyCompactSpace p m hp hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
          leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, max u v}) →
      Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
        leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) := by
  let := leviPointTopology m hm
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p m hp hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  rintro ⟨Ψ⟩
  let F := leviFirstAdjointnessAdjunction.{u, v} p m n hp hm hn hmul
  let C := Classical.choice
    (nonempty_leviInductionContragredientIso.{u, v} hG p m n hp hm hn hmul)
  apply nonempty_leviSecondAdjunction_of_pointImage p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP
  intro hUbar hMUbar
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let : MeasurableSpace (rationalPoints G) := borel _
  have : BorelSpace (rationalPoints G) := ⟨rfl⟩
  let : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  have h := isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul
  have hU := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hproj := continuous_projection_pointImage p m n hp hm hn hmul
  have hdec : IsSemidirectDecomposition (pointImage pbar) (pointImage (m ≫ p))
      (pointImage (nbar ≫ pbar)) := by
    rw [← hP]
    exact isSemidirectDecomposition_pointImage pbar mbar nbar hpbar.isClosedSubgroup hnbar
      hmulbar
  obtain ⟨g, hc, hB⟩ :=
    exists_central_hasOppositeIwahoriContractionBasis_of_dynamic hG χ _ _ _ hNbar hM hN
  have hχ := fun x => closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter
    _ _ _ hUbar hU hMUbar h.levi_le_normalizer x (hrec hUbar hU hMUbar h.levi_le_normalizer x)
  -- Stationary compression on fixed smooth functionals, from the preserved countable power.
  have hstat : ∀ (A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G))
      (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))),
      Jacquet.IsIwahoriContraction K (pointImage (nbar ≫ pbar)) (pointImage (m ≫ p))
        (pointImage (n ≫ p)) g →
      ∃ b, ∀ s, b ≤ s →
        LinearMap.range (Jacquet.compressedAction (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) K hK g ^ s) =
          LinearMap.range (Jacquet.compressedAction (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) K hK g ^ b) ∧
        LinearMap.ker (Jacquet.compressedAction (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) K hK g ^ s) =
          LinearMap.ker (Jacquet.compressedAction (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) K hK g ^ b) := by
    intro A K hK hI
    have hI' : Jacquet.IsIwahoriContraction K (pointImage (nbar ≫ pbar))
        (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) g := by
      rw [hP]
      exact hI
    have hc' : ∀ x ∈ pointImage (mbar ≫ pbar), x * g = g * x := by
      rw [hP]
      exact hc
    exact contragredient_compression_stationary_of_isLimit
      (pointImage (nbar ≫ pbar)) (pointImage (mbar ≫ pbar)) (pointImage (n ≫ p)) hUbar
      (pointImage_le_normalizer pbar mbar nbar hnbar) (leviPointsEquiv pbar mbar hpbar hmbar) A
      (SmoothRep.frobeniusChainDualLimit F C Ψ
        (SmoothRep.directSumIsColimit.{u, 0, max u v} (fun _ : ℕ => A)))
      K hK g hI' hc'
  obtain ⟨Ψ0, hΨ0⟩ := exists_isStableLiftDuality_of_admits _ _ _ hUbar hU hMUbar
    h.levi_le_normalizer g hc hB hχ (fun A =>
      (Jacquet.stablePairingDataOfIwahoriContractions _ _ _ hMUbar h.levi_le_normalizer g hc
        hB).admits_of_iwahoriContractions_of_splits A.representation
        (fun _ hK => hK.2.1) (fun _ hK => hK.2.2) A.isSmooth
        (fun K hK => by
          obtain ⟨b, hb⟩ := hstat A K hK.1 hK.2.1
          exact Jacquet.compactCompressionSplits_of_stationary
            (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) K hK.1 g b hb)
        (fun K hK => by
          obtain ⟨b, hb⟩ := hstat A K hK.1 hK.2.1
          exact Jacquet.compactCompressionSplits_inv_of_contragredient_stationary
            A.representation A.isSmooth K hK.1 g b hb))
  obtain ⟨meas, C', hC'⟩ := exists_isNaturalIntegralDuality_of_compactSpace.{u, max u v} h hU
    (isClosed_pointImage p hp.isClosedSubgroup) hproj hmod hδ
  exact nonempty_secondAdjunction_of_stableLift.{u, v} (h := h) (hU := hU)
    (isUnimodularModulus_pointImage_radical p n hp.isClosedSubgroup hn.1) hproj
    (fun x hxP hxO => hdec.eq_one_of_inf_eq hPP hxP hxO) hUbar hMUbar
    (fun f g hfg => jacquetFunctor_map_isShortExact hdec hUbar
      (isLimitOfCompactSubgroups_pointImage_radical pbar nbar hpbar.isClosedSubgroup hnbar.1)
      f g hfg)
    ⊤ meas C' hC' g hB Ψ0 hΨ0

/-- Renard VI.9.6, (VI.9.6.2) ⇒ (VI.9.6.1), for one pair of represented parabolics
`P = MN` and `P̄ = M N̄` with `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`: a natural
isomorphism `r_{P̄}(π~) ≅ (r_P π)~` gives `i_P ⊣ r_{P̄}`. -/
theorem nonempty_leviSecondAdjunction_of_contragredientIso
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)) :
    letI := leviPointTopology m hm
    haveI : LocallyCompactSpace (rationalPoints M) :=
      leviPoints_locallyCompactSpace p m hp hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
          leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, max u v}) →
      Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
        leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) := by
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp hm
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hPχ hn
  have hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hMχ]
  have hNbar := pointImage_opposite_radical_eq_dynamic parabolicDynamic
    oppositeDynamicParabolicUniqueness hG χ m hPχ hMχ hpbar hmbar hnbar hP hPP
  exact nonempty_leviSecondAdjunction_of_contragredientIso_of_dynamic.{u, v} hG p m n hp hm hn
    hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP χ hN hM hNbar
    (fun hU hO hMU hMO x =>
      RationalPointFamily.dynamicOppositeHaarReciprocity_of_leviAdjoint
        Dynamic.leviAdjointDeterminantReciprocity hG χ _ _ _ hNbar hM hN hU hO hMU hMO x)
    (rationalPoints_modularCharacter_eq_one RationalPointFamily.rationalReductiveUnimodularity
      standardCocharacter hG)
    (modularCharacter_pointImage_of_unimodularity
      RationalPointFamily.rationalReductiveUnimodularity standardCocharacter hG
      p m n hp hm hn hmul)

omit [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Renard VI.9.6: for every pair of represented parabolics `P = MN` and `P̄ = M N̄` with
`mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, second adjointness `i_P ⊣ r_{P̄}` holds if
and only if `r_{P̄}(π~) ≅ (r_P π)~` naturally in `π`. -/
theorem leviSecondAdjointnessContragredientEquivalence :
    LeviSecondAdjointnessContragredientEquivalenceStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
  exact ⟨nonempty_leviContragredientIso_of_secondAdjunction.{u, v} hG p m n hp hm hn hmul
      pbar mbar nbar hpbar hmbar hnbar hmulbar,
    nonempty_leviSecondAdjunction_of_contragredientIso.{u, v} hG p m n hp hm hn hmul
      pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP⟩

end Langlands.Aubert.General.RepresentedParabolic
