import Langlands.Representation.Category.Twist
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies

/-!
# Conditional finite-length standard intertwining target

The target uses the actual parabolic point subgroups, the full rational norm
family, and the isomorphism-class orbit of an arbitrary admissible finite-length
smooth representation. Analytic convergence and rationality are conclusions.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uL uI uV uW

section Orbit

variable {L : Type uL} [Group L] [TopologicalSpace L] [NonarchimedeanGroup L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  (π : SmoothRep.{0, uL, uV} ℂ L)

/-- The actual isomorphism class of the unramified twist. -/
def unramifiedTwistClass (χ : unramifiedCharacters ν) :
    SmoothRep.IsoClass.{0, uL, uV} ℂ L :=
  SmoothRep.isoClass (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))

/-- The actual range of the twist-class map; no representative is selected. -/
def UnramifiedTwistOrbit :=
  {c : SmoothRep.IsoClass.{0, uL, uV} ℂ L // c ∈ Set.range (unramifiedTwistClass ν π)}

/-- The surjective parameter map into the actual twist orbit. -/
def unramifiedTwistOrbitMap (χ : unramifiedCharacters ν) : UnramifiedTwistOrbit ν π :=
  ⟨unramifiedTwistClass ν π χ, ⟨χ, rfl⟩⟩

/-- The orbit carries the quotient topology of the existing character space. -/
instance : TopologicalSpace (UnramifiedTwistOrbit ν π) :=
  TopologicalSpace.coinduced (unramifiedTwistOrbitMap ν π) inferInstance

/-- The actual orbit image of a character region. -/
def unramifiedTwistOrbitRegion (Ω : Set (unramifiedCharacters ν)) :
    Set (UnramifiedTwistOrbit ν π) :=
  unramifiedTwistOrbitMap ν π '' Ω

/-- All characters whose twists lie in the same orbit region. -/
def unramifiedTwistOrbitSaturation (Ω : Set (unramifiedCharacters ν)) :
    Set (unramifiedCharacters ν) :=
  unramifiedTwistOrbitMap ν π ⁻¹' unramifiedTwistOrbitRegion ν π Ω

theorem subset_unramifiedTwistOrbitSaturation (Ω : Set (unramifiedCharacters ν)) :
    Ω ⊆ unramifiedTwistOrbitSaturation ν π Ω := by
  intro χ hχ
  exact ⟨χ, hχ, rfl⟩

theorem mem_unramifiedTwistOrbitSaturation_iff
    (Ω : Set (unramifiedCharacters ν)) (χ : unramifiedCharacters ν) :
    χ ∈ unramifiedTwistOrbitSaturation ν π Ω ↔
      ∃ ψ ∈ Ω, Nonempty
        (π.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν ψ) ≅
          π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) := by
  change (∃ ψ ∈ Ω, unramifiedTwistOrbitMap ν π ψ = unramifiedTwistOrbitMap ν π χ) ↔ _
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    exact ⟨ψ, hψ, (SmoothRep.isoClass_eq_iff _ _).mp (congrArg Subtype.val heq)⟩
  · rintro ⟨ψ, hψ, hiso⟩
    exact ⟨ψ, hψ, Subtype.ext ((SmoothRep.isoClass_eq_iff _ _).mpr hiso)⟩

end Orbit

open Aubert.General Induction StandardIntertwining

/-- Waldspurger IV.1.1 on actual point groups, conditional on the displayed
structural data. The unimodular and squared-modulus identities, the open
orbit cone, full convergence, one-denominator rationality and representative
naturality are conclusions, not structural assumptions. -/
def ConditionalParabolicIntertwiningStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
      (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
      (a : A.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P') (q : Q ⟶ G) (v : V ⟶ Q)
      (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
      (_hLevi : l ≫ p = l' ≫ p')
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
      (_hQ : (Dynamic.parabolic
        (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
      (_hv : LeviSubgroup.IsGeometricUnipotentRadical v),
      letI : Mono r.data.i.hom.hom.left :=
        r.isCompatible.maximalSplit.isSplitSubtorus.mono
      letI : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
        let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
        let := r.isCompatible.levi.isClosedSubgroup.mono
        let := r.isCompatible.parabolic.isClosedSubgroup.mono
        have : Mono (a ≫ l ≫ p).hom.hom.left := by
          change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
          infer_instance
        exact mono_of_mono_fac
          (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
      ∀ [Fintype (relativeWeylGroup r.data.i)],
        let B := weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i
        let C := parabolicPointUnramifiedIntertwiningRegion r B n q v
        let Ppt := (SubgroupFunctor.range p).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let P'pt := (SubgroupFunctor.range p').carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let Mpt := parabolicLeviPointSubgroup p l
        let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt) (hU : IsClosed (Upt : Set (rationalPoints G)))
          (h' : IsSemidirectDecomposition P'pt Mpt U'pt)
          (hU' : IsClosed (U'pt : Set (rationalPoints G)))
          (hP : IsClosed (Ppt : Set (rationalPoints G)))
          (hP' : IsClosed (P'pt : Set (rationalPoints G)))
          (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
          (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (hr : Continuous h.projection) (hr' : Continuous h'.projection),
          let ν := parabolicLeviRationalNormCharacters r
          let hν := continuous_parabolicLeviRationalNormCharacters r
          let hM := isClosed_parabolicLeviPointSubgroup r
          ∀ [MeasurableSpace U'pt] [BorelSpace U'pt]
            [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
            [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
            [BorelSpace (QuotientSpace (U := Upt) U'pt)]
            (qν : Measure (QuotientSpace (U := Upt) U'pt))
            (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
            [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
            [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
            (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
            (π : SmoothRep.{0, u, uV} ℂ Mpt),
            π.IsAdmissible → π.HasFiniteLength →
            ∃ (hδ : IsUnimodularModulus Upt hU) (hδ' : IsUnimodularModulus U'pt hU')
              (hsq : SquaredModulusCompatibility h hU h' hU') (R : ℝ),
              (C R).Nonempty ∧ IsOpen (C R) ∧
              IsOpen (unramifiedTwistOrbitRegion ν π (C R)) ∧
              let Ω := unramifiedTwistOrbitSaturation ν π (C R)
              ∃ (hfull : ∀ χ : Ω, domain h hU U'pt
                (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤),
                StandardCompactRationalOn h hU hδ K hP hK hPK ν hν hr
                  h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq Ω π hfull ∧
                ∀ (χ : Ω) (W : SmoothRep.{0, u, uW} ℂ Mpt)
                  (e : (π.twist χ.val.val.toMonoidHom
                    (unramifiedCharacter_isOpen_ker ν χ.val)).representation.Equiv W.representation),
                  ∃ (hfullW : domain h hU U'pt W qν = ⊤),
                    (fullSourceIntertwiner h hU h' hU' W qν μU' μI hqν hM hsq hfullW).comp
                        (inducedMap h hU e.toIntertwiningMap) =
                      (inducedMap h' hU' e.toIntertwiningMap).comp
                        (fullSourceIntertwiner h hU h' hU'
                          (π.twist χ.val.val.toMonoidHom
                            (unramifiedCharacter_isOpen_ker ν χ.val))
                          qν μU' μI hqν hM hsq (hfull χ))

end Langlands.Plancherel
