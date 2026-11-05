import Langlands.Representation.Plancherel.ParabolicPointUniformNumerator
import Langlands.Representation.Plancherel.ParabolicIntertwiningTopology
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Assembly of the host conclusion from convergence and domination -/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

section Assembly

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {p' : P' ⟶ G} {l' : M ⟶ P'} (r' : ParabolicRootPresentation p' l' a)
  (hLevi : l ≫ p = l' ≫ p')
  {n : U ⟶ P} {n' : U' ⟶ P'} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')

local instance assemblyAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance assemblyTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance assemblyLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

variable [Smooth G.X.hom] [IsSeparated G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt P'pt U'pt : Subgroup (rationalPoints G)}
  (hPpt : Ppt = (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
  (hU'pt : U'pt = (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
  (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
  (hU : IsClosed (Upt : Set (rationalPoints G))) (hδ : IsUnimodularModulus Upt hU)
  (K : OpenSubgroup (rationalPoints G)) (hP : IsClosed (Ppt : Set (rationalPoints G)))
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr : Continuous h.projection)
  (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
  (hU' : IsClosed (U'pt : Set (rationalPoints G))) (hδ' : IsUnimodularModulus U'pt hU')
  (hP' : IsClosed (P'pt : Set (rationalPoints G)))
  (hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'pt] [BorelSpace U'pt]
  [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
  [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
  [BorelSpace (QuotientSpace (U := Upt) U'pt)]
  (qν : Measure (QuotientSpace (U := Upt) U'pt))
  (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The analytic inputs on a region `C` of unramified parameters: `C` is
nonempty and open, the actual standard integral converges on the whole source
at every parameter of `C`, and the compact integrands are locally dominated on
the actual twist-orbit saturation of `C`. -/
def ParabolicLeviAnalyticInputs
    (π : Langlands.SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (C : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))) : Prop :=
  C.Nonempty ∧ IsOpen C ∧
    (∀ χ : C, domain h hU U'pt
      (π.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤) ∧
    CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK
      (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
      hr π U'pt qν (unramifiedTwistOrbitSaturation (parabolicLeviRationalNormCharacters r) π C)

include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- **Assembly of the host conclusion.** For a region `C` that is nonempty and
open, full convergence on `C` and local integrable domination on its actual
twist-orbit saturation `Ω` give every remaining conjunct of the host
conclusion: openness of the orbit region, full convergence on `Ω`,
compact rationality on `Ω`, and representative naturality. -/
theorem parabolicLevi_intertwiningConclusion_of_dominated
    (π : Langlands.SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hadm : π.IsAdmissible) (hfin : π.HasFiniteLength)
    (C : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))
    (hC : ParabolicLeviAnalyticInputs r h hU hδ K hP hK hPK hr qν π C) :
    C.Nonempty ∧ IsOpen C ∧
      IsOpen (unramifiedTwistOrbitRegion (parabolicLeviRationalNormCharacters r) π C) ∧
      ∃ (hfull : ∀ χ : unramifiedTwistOrbitSaturation (parabolicLeviRationalNormCharacters r) π C,
          domain h hU U'pt (π.twist χ.val.val.toMonoidHom
            (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤),
        StandardCompactRationalOn h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
          (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
          qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq
          (unramifiedTwistOrbitSaturation (parabolicLeviRationalNormCharacters r) π C) π hfull ∧
        ∀ (χ : unramifiedTwistOrbitSaturation (parabolicLeviRationalNormCharacters r) π C)
          (W : Langlands.SmoothRep.{0, u, uW} ℂ (parabolicLeviPointSubgroup p l))
          (e : (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker
            (parabolicLeviRationalNormCharacters r) χ.val)).representation.Equiv
              W.representation),
          ∃ (hfullW : domain h hU U'pt W qν = ⊤),
            (fullSourceIntertwiner h hU h' hU' W qν μU' μI hqν
                (isClosed_parabolicLeviPointSubgroup r) hsq hfullW).comp
                (inducedMap h hU e.toIntertwiningMap) =
              (inducedMap h' hU' e.toIntertwiningMap).comp
                (fullSourceIntertwiner h hU h' hU'
                  (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker
                    (parabolicLeviRationalNormCharacters r) χ.val))
                  qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq (hfull χ)) := by
  obtain ⟨hCne, hCopen, hfullC, hdom⟩ := hC
  have hfull := domain_eq_top_on_unramifiedTwistOrbitSaturation h hU U'pt qν
    (parabolicLeviRationalNormCharacters r) π C hfullC
  refine ⟨hCne, hCopen, isOpen_unramifiedTwistOrbitRegion _ π hCopen, hfull, ?_, ?_⟩
  · exact parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength r r' hLevi hn hn'
      hPpt hUpt hU'pt h hU hδ K hP hK hPK hr h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hsq π hadm
      hfin (isOpen_unramifiedTwistOrbitSaturation _ π hCopen) hfull hdom
  · intro χ W e
    exact fullSourceIntertwiner_equivalent_representative h hU U'pt qν h' hU' μU' μI hqν
      (isClosed_parabolicLeviPointSubgroup r) hsq (hfull χ) e

end Assembly

end Langlands.Plancherel
